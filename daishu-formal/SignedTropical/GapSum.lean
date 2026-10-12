import SignedTropical.Sorting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The threshold integral as a gap sum

`signed_assignment.tex`, Definition `def:filtration`, equations `eq:sorted` and
`eq:gap-sum`, Lemma `lem:bit`.

For `D : Fin m → ℝ` sort the entries and prepend a zero:
`s₀ = 0, s₁ ≤ ⋯ ≤ s_m` (`sortedVal`), and put `G_k = {e : D_e ≤ s_k}` (`threshSet`).  The
threshold integral of a set function `F` is defined here as the gap sum
`C_F(D) = ∑_{k<m} (s_{k+1} - s_k) F(G_k)` (`gapSum`).  The paper defines it as
`∫₀^∞ F(G_t(D)) dt` for `F(E) = 0` and proves the two equal (Proposition
`prop:two-readings`); no size statement uses the integral, so no measure theory enters
(`BLUEPRINT.md`, D4).  The gap sum makes sense for every `F`, without `F(E) = 0`.

On `D ≥ 0` the prepended zero keeps `s` monotone (`sortedVal_mono`), every entry of `D`
is one of the `s_j` (`exists_sortedVal_eq`), which gives Lemma `lem:bit`
(`bit_identity`), and the layer-cake identity `∑_k (s_{k+1} - s_k) [s_k < s_j] = s_j`
(`sum_gap_lt`) gives the reading of a modular function as a gap sum
(`sum_eq_gapSum_card`) used by the greedy identity.
-/

open Finset

namespace SignedTropical

variable {m : ℕ}

/-- The entries of `D` in increasing order. -/
noncomputable def sortedVals (D : Fin m → ℝ) : List ℝ := (List.ofFn D).insertionSort (· ≤ ·)

/-- `sortedVal D k = s_k`: `s₀ = 0` and `s_{k+1}` is the `(k+1)`-st smallest entry of `D`
(`eq:sorted`). -/
noncomputable def sortedVal (D : Fin m → ℝ) (k : ℕ) : ℝ := (0 :: sortedVals D).getD k 0

/-- The threshold set `G_k = {e : D_e ≤ s_k}` (`eq:sorted`). -/
noncomputable def threshSet (D : Fin m → ℝ) (k : ℕ) : Finset (Fin m) :=
  univ.filter fun e => D e ≤ sortedVal D k

/-- **The threshold integral, as a gap sum** (`eq:gap-sum`):
`C_F(D) = ∑_{k<m} (s_{k+1} - s_k) F(G_k)`. -/
noncomputable def gapSum (F : Finset (Fin m) → ℝ) (D : Fin m → ℝ) : ℝ :=
  ∑ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k) * F (threshSet D k)

variable {D : Fin m → ℝ}

@[simp] theorem length_sortedVals (D : Fin m → ℝ) : (sortedVals D).length = m := by
  simp [sortedVals]

theorem pairwise_sortedVals (D : Fin m → ℝ) : (sortedVals D).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ _

theorem mem_sortedVals {v : ℝ} : v ∈ sortedVals D ↔ ∃ e, D e = v := by
  simp [sortedVals, List.mem_ofFn]

@[simp] theorem sortedVal_zero (D : Fin m → ℝ) : sortedVal D 0 = 0 := rfl

theorem sortedVal_succ (D : Fin m → ℝ) {k : ℕ} (hk : k < m) :
    sortedVal D (k + 1) = (sortedVals D)[k]'(by simpa using hk) := by
  rw [sortedVal, List.getD_cons_succ, List.getD_eq_getElem]

/-- The sorted values with zero prepended form a sorted list when `D ≥ 0`. -/
theorem pairwise_zero_sortedVals (hD : ∀ e, 0 ≤ D e) :
    (0 :: sortedVals D).Pairwise (· ≤ ·) := by
  refine List.pairwise_cons.2 ⟨fun v hv => ?_, pairwise_sortedVals D⟩
  obtain ⟨e, rfl⟩ := mem_sortedVals.1 hv
  exact hD e

theorem sortedVal_mono (hD : ∀ e, 0 ≤ D e) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    sortedVal D i ≤ sortedVal D j := by
  have hl : (0 :: sortedVals D).length = m + 1 := by simp
  have hs := (pairwise_zero_sortedVals hD).sortedLE
  simp only [sortedVal]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact hs.getElem_le_getElem_of_le hij

/-- Every entry of `D` is one of `s₁, …, s_m`. -/
theorem exists_sortedVal_eq (D : Fin m → ℝ) (e : Fin m) :
    ∃ j, 1 ≤ j ∧ j ≤ m ∧ sortedVal D j = D e := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 (mem_sortedVals.2 ⟨e, rfl⟩)
  have hk' : k < m := by simpa using hk
  exact ⟨k + 1, by omega, by omega, by rw [sortedVal_succ D hk', hke]⟩

/-- Each of `s₁, …, s_m` is an entry of `D`. -/
theorem exists_eq_sortedVal (D : Fin m → ℝ) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    ∃ e, sortedVal D j = D e := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨e, he⟩ := mem_sortedVals.1 (List.getElem_mem (l := sortedVals D)
    (n := k) (by simp; omega))
  exact ⟨e, by rw [sortedVal_succ D (by omega), he]⟩

/-- No entry of `D` lies strictly between two consecutive sorted values. -/
theorem le_or_succ_le (hD : ∀ e, 0 ≤ D e) (e : Fin m) {k : ℕ} (hk : k < m) :
    D e ≤ sortedVal D k ∨ sortedVal D (k + 1) ≤ D e := by
  obtain ⟨j, hj1, hjm, hje⟩ := exists_sortedVal_eq D e
  rcases le_or_gt j k with hjk | hjk
  · exact Or.inl (hje ▸ sortedVal_mono hD hjk hk.le)
  · exact Or.inr (hje ▸ sortedVal_mono hD hjk hjm)

/-- `Δ - min(t, Δ) = max(Δ - t, 0)`: the form of `lem:bit` the circuit computes. -/
theorem sub_min_eq_max (t Δ : ℝ) : Δ - min t Δ = max (Δ - t) 0 := by
  rcases le_total t Δ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

/-- **Lemma `lem:bit` (exact membership at amplitude).**  For every `e` and every `k < m`,
`Δ_k - min(max(D_e - s_k, 0), Δ_k) = Δ_k · 1[e ∈ G_k]`. -/
theorem bit_identity (hD : ∀ e, 0 ≤ D e) (e : Fin m) {k : ℕ} (hk : k < m) :
    (sortedVal D (k + 1) - sortedVal D k)
        - min (max (D e - sortedVal D k) 0) (sortedVal D (k + 1) - sortedVal D k)
      = (sortedVal D (k + 1) - sortedVal D k) * if e ∈ threshSet D k then 1 else 0 := by
  have hmono := sortedVal_mono hD (Nat.le_succ k) hk
  simp only [threshSet, mem_filter, mem_univ, true_and]
  rcases le_or_succ_le hD e hk with h | h
  · rw [max_eq_right (by linarith), if_pos h, min_eq_left (by linarith)]; ring
  · by_cases h' : D e ≤ sortedVal D k
    · have : sortedVal D (k + 1) = sortedVal D k := le_antisymm (h.trans h') hmono
      rw [this, if_pos h']; simp
    · rw [if_neg h', max_eq_left (by linarith), min_eq_right (by linarith)]; ring

/-- **Layer cake.**  For `j ≤ m`, `∑_{k<m} (s_{k+1} - s_k) [s_k < s_j] = s_j`. -/
theorem sum_gap_lt (hD : ∀ e, 0 ≤ D e) {j : ℕ} (hj : j ≤ m) :
    ∑ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k)
        * (if sortedVal D k < sortedVal D j then 1 else 0) = sortedVal D j := by
  have hterm : ∀ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k)
      * (if sortedVal D k < sortedVal D j then 1 else 0)
      = if k < j then sortedVal D (k + 1) - sortedVal D k else 0 := by
    intro k hk
    rw [mem_range] at hk
    by_cases hkj : k < j
    · rw [if_pos hkj]
      by_cases hlt : sortedVal D k < sortedVal D j
      · rw [if_pos hlt, mul_one]
      · have h1 : sortedVal D k ≤ sortedVal D (k + 1) := sortedVal_mono hD (Nat.le_succ k) hk
        have h2 : sortedVal D (k + 1) ≤ sortedVal D j := sortedVal_mono hD hkj hj
        rw [if_neg hlt, mul_zero]; linarith
    · rw [if_neg hkj, if_neg (not_lt.2 (sortedVal_mono hD (not_lt.1 hkj) hk.le)), mul_zero]
  rw [sum_congr rfl hterm, ← sum_filter, show (range m).filter (· < j) = range j by
    ext k; simp only [mem_filter, mem_range]; omega, sum_range_sub, sortedVal_zero, sub_zero]

/-- Every entry is the gap sum of its own upper indicator. -/
theorem eq_sum_gap (hD : ∀ e, 0 ≤ D e) (e : Fin m) :
    D e = ∑ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k)
        * (if sortedVal D k < D e then 1 else 0) := by
  obtain ⟨j, -, hjm, hje⟩ := exists_sortedVal_eq D e
  rw [← hje, sum_gap_lt hD hjm]

/-- **A modular function as a gap sum.**  For `D ≥ 0` and every set `I`,
`∑_{e ∈ I} D_e = ∑_k (s_{k+1} - s_k) |I \ G_k|`. -/
theorem sum_eq_gapSum_card (hD : ∀ e, 0 ≤ D e) (I : Finset (Fin m)) :
    ∑ e ∈ I, D e = gapSum (fun S => ((I \ S).card : ℝ)) D := by
  simp only [gapSum]
  rw [sum_congr rfl fun e _ => eq_sum_gap hD e, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_sum, sum_boole, show I.filter (fun e => sortedVal D k < D e) = I \ threshSet D k by
    ext e; simp [threshSet, not_le]]

theorem gapSum_add (F G : Finset (Fin m) → ℝ) (D : Fin m → ℝ) :
    gapSum (fun S => F S + G S) D = gapSum F D + gapSum G D := by
  simp only [gapSum, mul_add, sum_add_distrib]

theorem gapSum_smul (c : ℝ) (F : Finset (Fin m) → ℝ) (D : Fin m → ℝ) :
    gapSum (fun S => c * F S) D = c * gapSum F D := by
  simp only [gapSum, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem gapSum_finsetSum {ι : Type} (s : Finset ι) (F : ι → Finset (Fin m) → ℝ)
    (D : Fin m → ℝ) : gapSum (fun S => ∑ i ∈ s, F i S) D = ∑ i ∈ s, gapSum (F i) D := by
  simp only [gapSum, mul_sum]
  exact sum_comm

/-- On `D ≥ 0` the gaps are nonnegative, so the gap sum is monotone in `F`. -/
theorem gapSum_mono (hD : ∀ e, 0 ≤ D e) {F G : Finset (Fin m) → ℝ} (h : ∀ S, F S ≤ G S) :
    gapSum F D ≤ gapSum G D :=
  sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (h _)
    (sub_nonneg.2 (sortedVal_mono hD (Nat.le_succ k) (mem_range.1 hk)))

/-- The complement of `G_k` is the strict upper level set `{e : s_k < D_e}`. -/
theorem compl_threshSet (D : Fin m → ℝ) (k : ℕ) :
    univ \ threshSet D k = univ.filter fun e => sortedVal D k < D e := by
  ext e
  simp [threshSet]

end SignedTropical
