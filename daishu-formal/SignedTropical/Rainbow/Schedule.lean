import SignedTropical.Rainbow.RankOne
import SignedTropical.Rainbow.Lagrangian

/-!
# The schedule of Theorem C

`greedy_intersection.tex`, proof of Theorem `thm:C`, Steps 1, 2 and 4, and the duality of
Step 3: start at `p = 0` and, for `r = 1, …, k − 1`, apply the stage-`r` PO-SL update `L r` times
(`schedule L`), for stage lengths `L` that are **valid**: at every weight, stage `r` ends within
`L r` updates (`ValidLength`).
* `validLength_stageLength`: `stageLength k m r = min(r(⌊m²/4⌋ + 1), 1 + (r - 1) k m,
  1 + k (2m - k - 1))`, the smallest of the stage bounds of Theorems `thm:potential` and
  `thm:stagelength`, is valid.
* `validLength_rankOne`: `L r = r` is valid when every component of `M` has rank at most one
  (Corollary `cor:rankone`, `RankOne.lt_of_nu_iterate_eq`).

At `p = 0` already `ν₀ ≥ 1` (`one_le_nu`); stage `r` starts with `ν₀ ≥ r` and ends with
`ν₀ ≥ r + 1`, so after stage `k − 1`, `ν₀ = k`, and `Ψ(p) = Opt(w)` by Lemma `lem:duality`
(`psi_schedule`).  The number of updates of `stageLength`, `rounds k m`, is at most
`(⌊m²/4⌋ + 1) k(k-1)/2` (`rounds_le_potential`) and at most `2 k² m` (`rounds_le`).  The observer
of stage `r` has `r + 1` rounds of augmentation, so the size of Theorem C weighs stage `r` by
`r + 2`: `40 Σ_r stageLength k m r (r + 2) ≤ 49 k³ m` (`sum_stageLength_mul_le`), and with
`L r = r`, `2 Σ_r r (r + 2) ≤ k³` (`sum_range_mul_le`).
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

/-- The number of updates in stage `r`: the smallest of the bounds `r(⌊m²/4⌋ + 1)` of Theorem
`thm:potential` and `1 + (r - 1) k m`, `1 + k (2m - k - 1)` of Theorem `thm:stagelength`. -/
def stageLength (k m r : ℕ) : ℕ :=
  min (min (r * (m ^ 2 / 4 + 1)) (1 + (r - 1) * (k * m))) (1 + k * (2 * m - k - 1))

/-- **The stage bound**: `stageLength k m` is valid.  An iterate with `ν₀ = r` has index below
the three bounds (`Potential.lt_of_nu_iterate_eq`, `StageLength.lt_of_nu_iterate_eq`,
`StageLength.lt_of_nu_iterate_eq_fixed`). -/
theorem validLength_stageLength (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) : ValidLength M blk (stageLength k m) :=
  validLength_of_lt hE hM fun _ _ hrk _ hp _ hn =>
    lt_min (lt_min (Potential.lt_of_nu_iterate_eq hE hk hM hrk hp hn)
      (StageLength.lt_of_nu_iterate_eq hE hk hM hrk hp hn))
      (StageLength.lt_of_nu_iterate_eq_fixed hE hk hM hrk hp hn)

/-- **Corollary `cor:rankone`**: when every component of `M` has rank at most one, stage `r` ends
within `r` updates. -/
theorem validLength_rankOne (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1) : ValidLength M blk (fun r => r) :=
  validLength_of_lt hE hM fun _ _ hrk _ hp _ hn => RankOne.lt_of_nu_iterate_eq hE hk hM hcomp hrk hp hn

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
        sum_le_sum fun r _ => (min_le_left _ _).trans (min_le_left _ _)
    _ = (m ^ 2 / 4 + 1) * (k * (k - 1) / 2) := by rw [← sum_mul, sum_range_id, mul_comm]

/-- **The number of updates is at most `2 k² m`** for `k ≤ m`, by Theorem `thm:stagelength`: stage
`0` is empty, and each of the stages `1, …, k - 1` takes at most `1 + k (2m - k - 1) ≤ 1 + 2km`
updates, and `(k - 1)(1 + 2km) ≤ 2 k² m`. -/
theorem rounds_le {k m : ℕ} (hkm : k ≤ m) : rounds k m ≤ 2 * k ^ 2 * m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [rounds]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h0 : stageLength (j + 1) m 0 = 0 := by simp [stageLength]
  have h1 : ∀ r ∈ range j, stageLength (j + 1) m (r + 1) ≤ 1 + 2 * (j + 1) * m := fun r _ =>
    (min_le_right _ _).trans (Nat.add_le_add_left
      ((Nat.mul_le_mul_left (j + 1) (Nat.sub_le_sub_right (Nat.sub_le (2 * m) (j + 1)) 1)).trans
        (by rw [Nat.mul_comm 2 (j + 1), Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
      1)
  have h2 : j + 1 ≤ (j + 1) * m := Nat.le_mul_of_pos_right _ hm
  calc rounds (j + 1) m
      = ∑ r ∈ range j, stageLength (j + 1) m (r + 1) + stageLength (j + 1) m 0 := by
        rw [rounds, sum_range_succ']
    _ ≤ j * (1 + 2 * (j + 1) * m) := by
        rw [h0, add_zero]
        simpa using sum_le_card_nsmul _ _ _ h1
    _ ≤ 2 * (j + 1) ^ 2 * m := by nlinarith

/-- With `L r = r`, the number of updates is `Σ_{r<k} r = k(k-1)/2 ≤ k²`. -/
theorem sum_range_id_le (k : ℕ) : ∑ r ∈ range k, r ≤ k ^ 2 := by
  rw [sum_range_id, sq]
  exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))

/-- **The weighted number of updates**: `40 Σ_r stageLength k m r (r + 2) ≤ 49 k³ m` for
`k ≤ m`.  Stage `0` is empty, stage `1` takes at most one update (`1 + (r - 1) k m` at `r = 1`),
and each of the stages `2, …, k - 1` at most `A = 1 + k (2m - k - 1)`.  With `k = j + 2` and
`2m = a + j + 3`, `A = 1 + (j + 2) a`, `2 Σ_{r=2}^{k-1} (r + 2) = j² + 7j`, and
`49 (j+2)³ (a + j + 3) - 40 A (j² + 7j) - 240 = (j+2) a (3j - 14)² + 49j⁴ + 441j³ + 1430j² +
1876j + 936`. -/
theorem sum_stageLength_mul_le {k m : ℕ} (hkm : k ≤ m) :
    40 * ∑ r ∈ range k, stageLength k m r * (r + 2) ≤ 49 * k ^ 3 * m := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [stageLength]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, 2 * m = a + j + 3 := ⟨2 * m - j - 3, by omega⟩
  have h0 : stageLength (j + 2) m 0 = 0 := by simp [stageLength]
  have h1 : stageLength (j + 2) m 1 ≤ 1 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by simp))
  have h2 : ∀ r ∈ range j, stageLength (j + 2) m (r + 2) * (r + 4) ≤
      (1 + (j + 2) * a) * (r + 4) := fun r _ => by
    refine Nat.mul_le_mul_right _ ((min_le_right _ _).trans_eq ?_)
    rw [show 2 * m - (j + 2) - 1 = a by omega]
  have hsplit : ∑ r ∈ range (j + 2), stageLength (j + 2) m r * (r + 2) =
      ∑ r ∈ range j, stageLength (j + 2) m (r + 2) * (r + 4) + stageLength (j + 2) m 1 * 3 := by
    rw [sum_range_succ', sum_range_succ', h0]
    simp only [zero_mul, add_zero, zero_add]
  have hS : (∑ r ∈ range j, (r + 4)) * 2 = j * j + 7 * j := by
    rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, add_mul, sum_range_id_mul_two]
    rcases j with _ | j
    · simp
    · simp only [Nat.add_sub_cancel]
      ring
  have hT : ∑ r ∈ range j, stageLength (j + 2) m (r + 2) * (r + 4) ≤
      (1 + (j + 2) * a) * ∑ r ∈ range j, (r + 4) := by
    rw [mul_sum]
    exact sum_le_sum h2
  have key : 40 * ((1 + (j + 2) * a) * (j * j + 7 * j)) + 240 ≤
      49 * (j + 2) ^ 3 * (a + j + 3) := by
    have e : ((49 * (j + 2) ^ 3 * (a + j + 3) : ℕ) : ℤ) -
        ((40 * ((1 + (j + 2) * a) * (j * j + 7 * j)) + 240 : ℕ) : ℤ) =
        ((j : ℤ) + 2) * a * (3 * j - 14) ^ 2 +
          (49 * (j : ℤ) ^ 4 + 441 * j ^ 3 + 1430 * j ^ 2 + 1876 * j + 936) := by
      push_cast
      ring
    have hpos : (0 : ℤ) ≤ ((j : ℤ) + 2) * a * (3 * j - 14) ^ 2 +
        (49 * (j : ℤ) ^ 4 + 441 * j ^ 3 + 1430 * j ^ 2 + 1876 * j + 936) := by positivity
    have := e.symm ▸ hpos
    omega
  have h2m : 2 * (49 * (j + 2) ^ 3 * m) = 49 * (j + 2) ^ 3 * (a + j + 3) := by
    rw [← ha]
    ring
  have hAU : (1 + (j + 2) * a) * ((∑ r ∈ range j, (r + 4)) * 2) =
      (1 + (j + 2) * a) * (j * j + 7 * j) := by
    rw [hS]
  rw [hsplit]
  nlinarith [hT, h1, key, h2m, hAU]

/-- **The weighted number of updates for components of rank one**, `L r = r`:
`2 Σ_r r (r + 2) ≤ k³`. -/
theorem sum_range_mul_le (k : ℕ) : 2 * ∑ r ∈ range k, r * (r + 2) ≤ k ^ 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    nlinarith [Nat.le_mul_self k]

end SignedTropical.Rainbow.Schedule
