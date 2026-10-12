import SignedTropical.Rainbow.Potential
import SignedTropical.Integral

/-!
# The update as a threshold integral over pairs

`greedy_intersection.tex`, Lemma `lem:oneupdate`, Step 2.  Index the ordered pairs `(e, f)` by
`Fin (m * m)` and put `D⁺_{ef} = max(v_f - v_e, 0)` (`Dplus`).  Its sublevel set at `t ≥ 0` is
`G_t` (`relOf_sublevel`).  With the observable `F_b(G) = [ν(N_G) ≤ r] ∧ [b ∈ Av(N_G)]` of Lemma
`lem:observer` (`obs`), which vanishes at `E × E` (`obs_univ`), the PO-SL update is the gap sum
`a_b = C_{F_b}(D⁺)` (`update_eq_gapSum`), by `eq:update-integral` (`Validity.update_eq_integral`),
Proposition `prop:posl` (`POSL.N_eq_NG`) and the integral reading of the gap sum
(`Integral.gapSum_eq_integral_Ioi`).
-/

open Finset MeasureTheory

namespace SignedTropical.Rainbow.GapUpdate

open SignedTropical.Rainbow

variable {m k : ℕ}

/-- The pair `(e, f)` with index `i`. -/
def pairOf (i : Fin (m * m)) : Fin m × Fin m := finProdFinEquiv.symm i

/-- `D⁺_{ef} = max(v_f - v_e, 0)`, indexed by the pairs. -/
noncomputable def Dplus (v : Fin m → ℝ) (i : Fin (m * m)) : ℝ :=
  max (v (pairOf i).2 - v (pairOf i).1) 0

/-- The relation read from a set of pair indices. -/
def relOf (S : Finset (Fin (m * m))) : Finset (Fin m × Fin m) := S.image pairOf

/-- The observable `F_b(G) = [ν(N_G) ≤ r] ∧ [b ∈ Av(N_G)]` of Lemma `lem:observer`, read on a
set of pair indices, as a real number `0` or `1`. -/
noncomputable def obs (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (b : Fin k)
    (S : Finset (Fin (m * m))) : ℝ :=
  if nu (POSL.NG M (relOf S)) blk ≤ r ∧ b ∈ Av (POSL.NG M (relOf S)) blk then 1 else 0

theorem Dplus_nonneg (v : Fin m → ℝ) (i : Fin (m * m)) : 0 ≤ Dplus v i :=
  le_max_right _ _

/-- The gap sum reads `F` only at the sublevel sets `G_t(D)` with `t ≥ 0`: two observables that
agree there have the same gap sum.  (So a Boolean observer that is correct on the sets `G_t`
suffices for the compiler.) -/
theorem gapSum_congr_sublevel {n : ℕ} {D : Fin n → ℝ} (hD : ∀ e, 0 ≤ D e)
    {F F' : Finset (Fin n) → ℝ} (h : ∀ t, 0 ≤ t → F (Integral.sublevel D t) = F' (Integral.sublevel D t)) :
    gapSum F D = gapSum F' D := by
  refine sum_congr rfl fun k hk => ?_
  rw [Integral.threshSet_eq_sublevel, h _ ((sortedVal_mono hD (Nat.zero_le k)
    (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (mem_range.1 hk)))).trans' (by simp [sortedVal]))]

/-- The sublevel set of `D⁺` at `t ≥ 0` is `G_t`. -/
theorem relOf_sublevel (v : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    relOf (Integral.sublevel (Dplus v) t) = POSL.Gt v t := by
  ext ⟨e, f⟩
  simp only [relOf, mem_image, Integral.mem_sublevel, POSL.Gt, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hpair⟩
    rw [Dplus, hpair, max_le_iff] at hi
    exact hi.1
  · intro h
    refine ⟨finProdFinEquiv (e, f), ?_, by simp [pairOf]⟩
    rw [Dplus, show pairOf (finProdFinEquiv (e, f)) = (e, f) by simp [pairOf]]
    exact max_le h ht

theorem relOf_univ : relOf (univ : Finset (Fin (m * m))) = univ := by
  refine eq_univ_of_forall fun p => mem_image.2 ⟨finProdFinEquiv p, mem_univ _, by simp [pairOf]⟩

variable {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}

/-- `F_b(E × E) = 0`: at `E × E` the matroid is `M`, which has a rainbow base, so `ν = k > r`. -/
theorem obs_univ (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hrk : r < k) (b : Fin k) : obs M blk r b univ = 0 := by
  rw [obs, relOf_univ, POSL.NG_univ hE, (nu_eq_iff hk).2 hM, if_neg fun h => by omega]

/-- **Lemma `lem:oneupdate`, Step 2.**  At a state with `r ≤ ν₀ = ν(M^v)` and `r < k`, the
PO-SL update is the gap sum `a_b = C_{F_b}(D⁺)`. -/
theorem update_eq_gapSum (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) {v : Fin m → ℝ} (hr : r ≤ nu (minBases M v) blk)
    (hrk : r < k) (b : Fin k) :
    Validity.update (POSL.N M v) blk r b = gapSum (obs M blk r b) (Dplus v) := by
  have hN := POSL.isAdmissible hE hM v
  rw [(Validity.update_eq_integral hE hk hr hrk hN (b := b)).2,
    (Integral.gapSum_eq_integral_Ioi (Dplus_nonneg v) (obs_univ hE hk hM hrk b)).2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  simp only [obs, relOf_sublevel v ht0, ← POSL.N_eq_NG ht0, ite_zero_mul_ite_zero, mul_one]

end SignedTropical.Rainbow.GapUpdate
