import SignedTropical.Rainbow.Potential
import SignedTropical.Rainbow.Events
import SignedTropical.Integral

/-!
# The update as a gap sum over the event levels

`greedy_intersection.tex`, Lemma `lem:oneupdate`, Step 3.  Let `Λ = lev M v` be the `2m` levels
and `Q = Qv M v` the query values of `Rainbow/Events.lean`.  Every `Q_j` is a level or `0`
(`Events.Qv_inLev`), so at `t ≥ 0` the bits `[Q_j ≤ t]` depend only on the sublevel set
`{i : Λ_i ≤ t}` (`bits_sublevel`).  If a Boolean function `F_b` of these bits equals
`[ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]` at every `t ≥ 0` (the observer of Lemma `lem:observer`), then
the PO-SL update is the gap sum over the levels,
`a_b = Σ_{i < 2m} (s_{i+1} - s_i) F_b([Q ≤ s_i])`, `s` the sorted levels with `s_0 = 0`
(`update_eq_levSum`).  The proof reads `a_b` as an integral (`eq:update-integral`,
`Validity.update_eq_integral`) and the gap sum as an integral (`Integral.gapSum_eq_integral_Ioi`);
the integrand vanishes beyond the largest level and the largest difference `v_f - v_e`, where
`N(t) = M` (`POSL.N_eq_self`) has a rainbow base, so `ν = k > r`.
-/

open Finset MeasureTheory

namespace SignedTropical.Rainbow.GapUpdate

open SignedTropical.Rainbow SignedTropical.Rainbow.Events

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}

open Classical in
/-- At `t ≥ 0` the bits `[Q_j ≤ t]` are read from the sublevel set of the levels: `Q_j = 0`, or
`Q_j = Λ_i` for some `i` with `Λ_i ≤ t`. -/
theorem bits_sublevel (v : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (fun j => decide (Qv M v j = 0 ∨ ∃ i ∈ Integral.sublevel (lev M v) t, lev M v i = Qv M v j))
      = fun j => decide (Qv M v j ≤ t) := by
  funext j
  refine decide_eq_decide.2 ⟨?_, fun h => ?_⟩
  · rintro (h0 | ⟨i, hi, hiq⟩)
    · rw [h0]; exact ht
    · rw [← hiq]; exact Integral.mem_sublevel.1 hi
  · rcases Qv_inLev (M := M) (v := v) j with h0 | ⟨i, hi⟩
    · exact Or.inl h0
    · exact Or.inr ⟨i, Integral.mem_sublevel.2 (hi ▸ h), hi⟩

open Classical in
/-- **Lemma `lem:oneupdate`, Step 3.**  At a state with `r ≤ ν₀ = ν(M^v)` and `r < k`, if the
Boolean function `F_b` of the event bits equals `[ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]` at the event bits
of every `t ≥ 0`, the PO-SL update is `a_b = Σ_{i < 2m} (s_{i+1} - s_i) F_b([Q ≤ s_i])`. -/
theorem update_eq_levSum (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) {v : Fin m → ℝ} (hr : r ≤ nu (minBases M v) blk)
    (hrk : r < k) {F : Fin k → (Fin (qn m) → Bool) → Bool}
    (hF : ∀ t, 0 ≤ t → ∀ b, F b (fun j => decide (Qv M v j ≤ t)) =
      decide (nu (POSL.N M v t) blk ≤ r ∧ b ∈ Av (POSL.N M v t) blk)) (b : Fin k) :
    Validity.update (POSL.N M v) blk r b = ∑ i ∈ range (m + m),
      (sortedVal (lev M v) (i + 1) - sortedVal (lev M v) i) *
        if F b (fun j => decide (Qv M v j ≤ sortedVal (lev M v) i)) then 1 else 0 := by
  have hΛ : ∀ i, 0 ≤ lev M v i := lev_nonneg
  set Φ : Finset (Fin (m + m)) → ℝ := fun S =>
    if F b (fun j => decide (Qv M v j = 0 ∨ ∃ i ∈ S, lev M v i = Qv M v j)) then 1 else 0
    with hΦdef
  have hΦ : ∀ t, 0 ≤ t → Φ (Integral.sublevel (lev M v) t) =
      (if nu (POSL.N M v t) blk ≤ r then (1 : ℝ) else 0) *
        (if b ∈ Av (POSL.N M v t) blk then 1 else 0) := by
    intro t ht
    simp only [hΦdef, bits_sublevel v ht, hF t ht b, ite_zero_mul_ite_zero, mul_one,
      decide_eq_true_eq]
  -- beyond every level and every difference `v_f - v_e`, `N(t) = M`, so `Φ(E) = 0`
  set T : ℝ := ∑ i, lev M v i + ∑ e, ∑ f, |v f - v e| with hT
  have hT0 : 0 ≤ T := add_nonneg (sum_nonneg fun i _ => hΛ i)
    (sum_nonneg fun e _ => sum_nonneg fun f _ => abs_nonneg _)
  have hΛT : ∀ i, lev M v i ≤ T := fun i =>
    (single_le_sum (fun j _ => hΛ j) (mem_univ i)).trans (le_add_of_nonneg_right
      (sum_nonneg fun e _ => sum_nonneg fun f _ => abs_nonneg _))
  have hvT : ∀ e f, v f - v e ≤ T := fun e f =>
    (le_abs_self _).trans <| (single_le_sum (f := fun f => |v f - v e|)
      (fun _ _ => abs_nonneg _) (mem_univ f)).trans <|
      (single_le_sum (f := fun e => ∑ f, |v f - v e|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ e)).trans
      (le_add_of_nonneg_left (sum_nonneg fun i _ => hΛ i))
  have hΦu : Φ univ = 0 := by
    have hu : Integral.sublevel (lev M v) T = univ :=
      eq_univ_of_forall fun i => Integral.mem_sublevel.2 (hΛT i)
    rw [← hu, hΦ T hT0, POSL.N_eq_self hE hvT, (nu_eq_iff hk).2 hM, if_neg (by omega), zero_mul]
  have hN := POSL.isAdmissible hE hM v
  rw [(Validity.update_eq_integral hE hk hr hrk hN (b := b)).2,
    ← setIntegral_congr_fun measurableSet_Ioi (fun t ht => hΦ t (le_of_lt ht)),
    ← (Integral.gapSum_eq_integral_Ioi hΛ hΦu).2, gapSum]
  refine sum_congr rfl fun i hi => ?_
  have hs : 0 ≤ sortedVal (lev M v) i := (sortedVal_zero (lev M v)).symm.le.trans
    (sortedVal_mono hΛ (Nat.zero_le i) (mem_range.1 hi).le)
  rw [Integral.threshSet_eq_sublevel]
  simp only [hΦdef, bits_sublevel v hs]
