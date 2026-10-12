import SignedTropical.Rainbow.RankOne
import SignedTropical.Rainbow.Lagrangian

/-!
# The schedule of Theorem C

`greedy_intersection.tex`, proof of Theorem `thm:C`, Steps 1, 2 and 4, and the duality of
Step 3: start at `p = 0` and, for `r = 1, …, k − 1`, apply the stage-`r` PO-SL update `L r` times
(`schedule L`), for stage lengths `L` that are **valid**: at every weight, stage `r` ends within
`L r` updates (`ValidLength`).
* `validLength_stageLength`: `stageLength k m r = min(r(⌊m²/4⌋ + 1), 1 + (r - 1) k m)`, the smaller
  of the stage bounds of Theorems `thm:potential` and `thm:stagelength`, is valid
  (`stage_bound`).
* `validLength_rankOne`: `L r = r` is valid when every component of `M` has rank at most one
  (Corollary `cor:rankone`, `RankOne.lt_of_nu_iterate_eq`).

At `p = 0` already `ν₀ ≥ 1` (`one_le_nu`); stage `r` starts with `ν₀ ≥ r` and ends with
`ν₀ ≥ r + 1`, so after stage `k − 1`, `ν₀ = k`, and `Ψ(p) = Opt(w)` by Lemma `lem:duality`
(`psi_schedule`).  The number of updates of `stageLength`, `rounds k m`, is at most
`(⌊m²/4⌋ + 1) k(k-1)/2` (`rounds_le_potential`) and at most `k³ m` (`rounds_le`).
-/

open Finset

namespace SignedTropical.Rainbow.Schedule

open SignedTropical.Rainbow SignedTropical.Rainbow.Potential

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k}

/-- Stage lengths `L` are **valid** for `M` and `blk` if, at every weight `w`, every stage
`r < k` ends within `L r` updates: from every `p` with `ν₀(p) ≥ r`, `L r` iterations of the
stage-`r` map reach `ν₀ ≥ r + 1`. -/
def ValidLength (M : Matroid (Fin m)) (blk : Fin m → Fin k) (L : ℕ → ℕ) : Prop :=
  ∀ (w : Fin m → ℝ) (r : ℕ), r < k → ∀ p : Fin k → ℝ, r ≤ nu (minBases M (shift blk w p)) blk →
    r + 1 ≤ nu (minBases M (shift blk w ((stageMap M blk w r)^[L r] p))) blk

/-- Stage lengths are valid as soon as every iterate with `ν₀ = r` has index below `L r`. -/
theorem validLength_of_lt (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B)
    {L : ℕ → ℕ} (h : ∀ (w : Fin m → ℝ) (r : ℕ), r < k → ∀ p : Fin k → ℝ,
      r ≤ nu (minBases M (shift blk w p)) blk → ∀ n,
        nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r → n < L r) :
    ValidLength M blk L := fun w r hrk p hp =>
  Nat.succ_le_of_lt <| lt_of_le_of_ne (le_nu_iterate hE hM hp _) fun h' =>
    lt_irrefl (L r) (h w r hrk p hp (L r) h'.symm)

/-- The number of updates in stage `r`: the smaller of the bounds `r(⌊m²/4⌋ + 1)` of Theorem
`thm:potential` and `1 + (r - 1) k m` of Theorem `thm:stagelength`. -/
def stageLength (k m r : ℕ) : ℕ := min (r * (m ^ 2 / 4 + 1)) (1 + (r - 1) * (k * m))

/-- **The stage bound**: `stageLength k m` is valid.  An iterate with `ν₀ = r` has index below
both bounds (`Potential.lt_of_nu_iterate_eq`, `StageLength.lt_of_nu_iterate_eq`). -/
theorem validLength_stageLength (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) : ValidLength M blk (stageLength k m) :=
  validLength_of_lt hE hM fun _ _ hrk _ hp _ hn =>
    lt_min (Potential.lt_of_nu_iterate_eq hE hk hM hrk hp hn)
      (StageLength.lt_of_nu_iterate_eq hE hk hM hrk hp hn)

/-- **Corollary `cor:rankone`**: when every circuit of `M` has at most two elements, that is
every component has rank at most one, stage `r` ends within `r` updates. -/
theorem validLength_rankOne (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hpar : ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2) : ValidLength M blk (fun r => r) :=
  validLength_of_lt hE hM fun _ _ hrk _ hp _ hn => RankOne.lt_of_nu_iterate_eq hE hk hM hpar hrk hp hn

/-- Stages `1, …, j` with stage lengths `L`: `schedule L M blk w j p` applies the stage-`r` update
`L r` times, for `r = 1, …, j` in this order. -/
noncomputable def schedule (L : ℕ → ℕ) (M : Matroid (Fin m)) (blk : Fin m → Fin k)
    (w : Fin m → ℝ) : ℕ → (Fin k → ℝ) → (Fin k → ℝ)
  | 0, p => p
  | j + 1, p => (stageMap M blk w (j + 1))^[L (j + 1)] (schedule L M blk w j p)

/-- `ν₀ ≥ 1` at every state when `M` has rank `k ≥ 1`: one element of a minimum base is a rainbow
independent set of `M^u`. -/
theorem one_le_nu (hE : M.E = Set.univ) (hk : rank M = k) (hk1 : 1 ≤ k) (u : Fin m → ℝ) :
    1 ≤ nu (minBases M u) blk := by
  obtain ⟨B, hB⟩ := exists_isMinBase M u
  obtain ⟨e, he⟩ : B.Nonempty := card_pos.1 (by rw [card_base M hB.1, hk]; omega)
  have hI : IsRainbowIndep (minBases M u) blk {e} :=
    ⟨(hB.isBase_minBases hE).indep.subset (by simpa using he), by simp [IsRainbow]⟩
  simpa using hI.card_le_nu

/-- After stages `1, …, j` with `j < k` and valid stage lengths, `ν₀ ≥ j + 1`. -/
theorem le_nu_schedule {L : ℕ → ℕ} (hL : ValidLength M blk L) (w : Fin m → ℝ) (p : Fin k → ℝ)
    (hp : 1 ≤ nu (minBases M (shift blk w p)) blk) :
    ∀ j, j < k → j + 1 ≤ nu (minBases M (shift blk w (schedule L M blk w j p))) blk
  | 0, _ => hp
  | j + 1, hj => hL w (j + 1) hj _ (le_nu_schedule hL w p hp j (by omega))

/-- **Theorem `thm:C`, Steps 1 to 3, the mathematical part.**  After the schedule from `p = 0`
with valid stage lengths, `ν₀ = k` and the Lagrangian is the optimum: `Ψ(p) = Opt(w)`. -/
theorem psi_schedule (hE : M.E = Set.univ) (hk : rank M = k) {L : ℕ → ℕ}
    (hL : ValidLength M blk L) (w : Fin m → ℝ) :
    Psi M blk w (schedule L M blk w (k - 1) 0) = Opt M blk w := by
  refine Pos.psi_eq_opt hE hk (le_antisymm (nu_le _ _) ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact Nat.zero_le _
  have := le_nu_schedule hL w 0 (one_le_nu hE hk hk1 _) (k - 1) (by omega)
  rwa [Nat.sub_add_cancel hk1] at this

/-- The total number of updates of `stageLength`, `Σ_{r<k} stageLength k m r`. -/
def rounds (k m : ℕ) : ℕ := ∑ r ∈ range k, stageLength k m r

/-- The number of updates is at most `(⌊m²/4⌋ + 1) k(k-1)/2`, the count of Theorem
`thm:potential`. -/
theorem rounds_le_potential (k m : ℕ) : rounds k m ≤ (m ^ 2 / 4 + 1) * (k * (k - 1) / 2) := by
  calc rounds k m ≤ ∑ r ∈ range k, r * (m ^ 2 / 4 + 1) :=
        sum_le_sum fun r _ => min_le_left _ _
    _ = (m ^ 2 / 4 + 1) * (k * (k - 1) / 2) := by rw [← sum_mul, sum_range_id, mul_comm]

/-- **The number of updates is at most `k³ m`** for `k ≤ m`, by Theorem `thm:stagelength`: each of
the `k` stages takes at most `1 + (k - 1) k m` updates, and `k (1 + (k - 1) k m) ≤ k³ m`. -/
theorem rounds_le {k m : ℕ} (hkm : k ≤ m) : rounds k m ≤ k ^ 3 * m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [rounds]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : 0 < m := hk.trans_le hkm
  have h1 : ∀ r ∈ range (j + 1), stageLength (j + 1) m r ≤ 1 + j * ((j + 1) * m) := fun r hr =>
    (min_le_right _ _).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (by rw [mem_range] at hr; omega)) 1)
  have h2 : j + 1 ≤ (j + 1) ^ 2 * m :=
    (Nat.le_self_pow two_ne_zero _).trans (Nat.le_mul_of_pos_right _ hm)
  calc rounds (j + 1) m ≤ (j + 1) * (1 + j * ((j + 1) * m)) := by
        simpa [rounds] using sum_le_card_nsmul _ _ _ h1
    _ = (j + 1) + j * ((j + 1) ^ 2 * m) := by ring
    _ ≤ (j + 1) ^ 2 * m + j * ((j + 1) ^ 2 * m) := Nat.add_le_add_right h2 _
    _ = (j + 1) ^ 3 * m := by ring

/-- With `L r = r`, the number of updates is `Σ_{r<k} r = k(k-1)/2 ≤ k²`. -/
theorem sum_range_id_le (k : ℕ) : ∑ r ∈ range k, r ≤ k ^ 2 := by
  rw [sum_range_id, sq]
  exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))

end SignedTropical.Rainbow.Schedule
