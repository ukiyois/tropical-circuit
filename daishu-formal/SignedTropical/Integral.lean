import SignedTropical.GapSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The threshold integral as an integral; the Lipschitz bound

`greedy_intersection.tex`, Definition `def:ti`; `signed_assignment.tex`, Proposition
`prop:two-readings`, Lemma `lem:lipschitz`, and the Lipschitz bound of Corollary
`cor:integer-observable`.

Phase 1 defines the threshold integral as the gap sum `C_F(D) = ∑_{k<m} Δ_k F(G_k)`
(`gapSum`).  For `D ≥ 0` the sublevel set `G_t(D) = {e : D_e ≤ t}` (`sublevel D t`) equals `G_k`
for `s_k ≤ t < s_{k+1}` (`sublevel_eq_threshSet`) and `E` for `t ≥ s_m` (`sublevel_eq_univ`), so
`t ↦ F(G_t(D))` is a step function whose Lebesgue integral is the gap sum:

* `gapSum_eq_intervalIntegral`: `C_F(D) = ∫_0^{s_m} F(G_t(D)) dt` for every `F`, where
  `s_m = max_e D_e` (`sortedVal_last_eq_iSup`) (Definition `def:ti`);
* `gapSum_eq_integral_Ioi`: `C_F(D) = ∫_0^∞ F(G_t(D)) dt` when `F(E) = 0` (`eq:gap-sum`);
* `gapSum_eq_integral_lovasz`: `C_F(D) = ∫_0^∞ g({e : D_e ≥ t}) dt` with `g(S) = F(E \ S)`,
  when `F(E) = 0` (`eq:lovasz`); `gapSum_compl_eq_integral` is the same identity started from
  `g` with `g(∅) = 0`;

each together with the integrability of the integrand.

If `0 ≤ F ≤ c` then `|C_F(D) - C_F(D')| ≤ c ‖D - D'‖₁` (`abs_gapSum_sub_le`), which gives
Lemma `lem:lipschitz` (`lipschitz`, Boolean `F`, `c = 1`) and the Lipschitz bound of Corollary
`cor:integer-observable` (`integer_observable_lipschitz`, `c = max_S f(S)`).  Neither needs
`F(E) = 0`: the value `F(E)` does not enter the gap sum (`gapSum_ite_univ`), since a gap with
`G_k = E` has width `0`.
-/

open Finset MeasureTheory

namespace SignedTropical.Integral

variable {m : ℕ} {D D' : Fin m → ℝ}

/-- The sublevel set `G_t(D) = {e : D_e ≤ t}`. -/
noncomputable def sublevel (D : Fin m → ℝ) (t : ℝ) : Finset (Fin m) := {e | D e ≤ t}

@[simp] theorem mem_sublevel {t : ℝ} {e : Fin m} : e ∈ sublevel D t ↔ D e ≤ t := by
  simp [sublevel]

/-- `G_k = G_{s_k}(D)`. -/
theorem threshSet_eq_sublevel (D : Fin m → ℝ) (k : ℕ) :
    threshSet D k = sublevel D (sortedVal D k) := rfl

/-- `G_t(D) = G_k` for `s_k ≤ t < s_{k+1}`: no entry of `D` lies strictly between two
consecutive sorted values. -/
theorem sublevel_eq_threshSet (hD : ∀ e, 0 ≤ D e) {k : ℕ} (hk : k < m) {t : ℝ}
    (ht : t ∈ Set.Ico (sortedVal D k) (sortedVal D (k + 1))) : sublevel D t = threshSet D k := by
  ext e
  rw [threshSet_eq_sublevel, mem_sublevel, mem_sublevel]
  rcases le_or_succ_le hD e hk with h | h
  · exact iff_of_true (h.trans ht.1) h
  · exact iff_of_false (fun _ => by linarith [ht.2]) (fun _ => by linarith [ht.1, ht.2])

/-- `D_e ≤ s_m` for every `e`. -/
theorem le_sortedVal_last (hD : ∀ e, 0 ≤ D e) (e : Fin m) : D e ≤ sortedVal D m := by
  obtain ⟨j, -, hjm, hje⟩ := exists_sortedVal_eq D e
  exact hje ▸ sortedVal_mono hD hjm le_rfl

/-- `G_t(D) = E` for `t ≥ s_m`. -/
theorem sublevel_eq_univ (hD : ∀ e, 0 ≤ D e) {t : ℝ} (ht : sortedVal D m ≤ t) :
    sublevel D t = univ :=
  filter_true_of_mem fun e _ => (le_sortedVal_last hD e).trans ht

/-- `s_m = max_e D_e`, which is `0` when `m = 0`. -/
theorem sortedVal_last_eq_iSup (hD : ∀ e, 0 ≤ D e) : sortedVal D m = ⨆ e, D e := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Real.iSup_of_isEmpty, sortedVal_zero]
  · obtain ⟨e, he⟩ := exists_eq_sortedVal D hm le_rfl
    haveI : Nonempty (Fin m) := ⟨e⟩
    rw [he]
    exact le_antisymm (le_ciSup (Set.finite_range D).bddAbove e)
      (ciSup_le fun e' => he ▸ le_sortedVal_last hD e')

/-- A function equal to `c` on `(a, b)` is integrable on `[a, b]` with integral `(b - a) c`. -/
theorem intervalIntegral_of_eqOn_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (h : Set.EqOn (fun _ => c) f (Set.Ioo a b)) :
    IntervalIntegrable f volume a b ∧ ∫ t in a..b, f t = (b - a) * c :=
  ⟨intervalIntegrable_const.congr_uIoo (by rwa [Set.uIoo_of_le hab]), by
    rw [← intervalIntegral.integral_congr_Ioo_of_le hab h, intervalIntegral.integral_const,
      smul_eq_mul]⟩

/-- On the `k`-th gap the integrand is the constant `F(G_k)`. -/
theorem intervalIntegral_gap (hD : ∀ e, 0 ≤ D e) (F : Finset (Fin m) → ℝ) {k : ℕ}
    (hk : k < m) :
    IntervalIntegrable (fun t => F (sublevel D t)) volume (sortedVal D k) (sortedVal D (k + 1)) ∧
      ∫ t in sortedVal D k..sortedVal D (k + 1), F (sublevel D t)
        = (sortedVal D (k + 1) - sortedVal D k) * F (threshSet D k) :=
  intervalIntegral_of_eqOn_Ioo (sortedVal_mono hD k.le_succ hk) fun _ ht =>
    congrArg F (sublevel_eq_threshSet hD hk ⟨ht.1.le, ht.2⟩).symm

/-- **Definition `def:ti`.**  For `D ≥ 0` and every `F : 2^E → ℝ`, the function
`t ↦ F(G_t(D))` is integrable on `[0, s_m]` and `C_F(D) = ∫_0^{s_m} F(G_t(D)) dt`. -/
theorem gapSum_eq_intervalIntegral (hD : ∀ e, 0 ≤ D e) (F : Finset (Fin m) → ℝ) :
    IntervalIntegrable (fun t => F (sublevel D t)) volume 0 (sortedVal D m) ∧
      gapSum F D = ∫ t in (0)..sortedVal D m, F (sublevel D t) := by
  have h k (hk : k < m) := intervalIntegral_gap hD F hk
  refine ⟨IntervalIntegrable.trans_iterate fun k hk => (h k hk).1, ?_⟩
  rw [← sortedVal_zero D, ← intervalIntegral.sum_integral_adjacent_intervals fun k hk => (h k hk).1,
    gapSum]
  exact sum_congr rfl fun k hk => (h k (mem_range.1 hk)).2.symm

/-- **Proposition `prop:two-readings`, `eq:gap-sum`**, and the remark after Definition `def:ti`.
For `D ≥ 0` and `F : 2^E → ℝ` with `F(E) = 0`, the function `t ↦ F(G_t(D))` is integrable on
`(0, ∞)` and `C_F(D) = ∫_0^∞ F(G_t(D)) dt`. -/
theorem gapSum_eq_integral_Ioi (hD : ∀ e, 0 ≤ D e) {F : Finset (Fin m) → ℝ} (hF : F univ = 0) :
    IntegrableOn (fun t => F (sublevel D t)) (Set.Ioi 0) ∧
      gapSum F D = ∫ t in Set.Ioi 0, F (sublevel D t) := by
  obtain ⟨hi, he⟩ := gapSum_eq_intervalIntegral hD F
  have h0 : 0 ≤ sortedVal D m := sortedVal_mono hD (Nat.zero_le m) le_rfl
  have hz : ∀ t ∈ Set.Ioi 0 \ Set.Ioc 0 (sortedVal D m), F (sublevel D t) = 0 := fun t ht => by
    rw [sublevel_eq_univ hD (not_le.1 fun h => ht.2 ⟨ht.1, h⟩).le, hF]
  refine ⟨hi.1.of_forall_sdiff_eq_zero measurableSet_Ioi hz, ?_⟩
  rw [he, intervalIntegral.integral_of_le h0,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self hz]

/-- **Proposition `prop:two-readings`, `eq:lovasz`.**  Let `D ≥ 0`, let `F : 2^E → ℝ` satisfy
`F(E) = 0`, and write `g(S) = F(E \ S)`.  Then `t ↦ g({e : D_e ≥ t})` is integrable on `(0, ∞)`
and `C_F(D) = ∫_0^∞ g({e : D_e ≥ t}) dt`. -/
theorem gapSum_eq_integral_lovasz (hD : ∀ e, 0 ≤ D e) {F g : Finset (Fin m) → ℝ}
    (hF : F univ = 0) (hg : ∀ S, g S = F (univ \ S)) :
    IntegrableOn (fun t => g {e | t ≤ D e}) (Set.Ioi 0) ∧
      gapSum F D = ∫ t in Set.Ioi 0, g {e | t ≤ D e} := by
  obtain ⟨hi, he⟩ := gapSum_eq_integral_Ioi hD hF
  have hae : ∀ᵐ t, t ∈ Set.Ioi (0 : ℝ) → F (sublevel D t) = g {e | t ≤ D e} :=
    ((Set.finite_range D).countable.ae_notMem volume).mono fun t ht _ => by
      rw [hg]
      congr 1
      ext e
      simp only [mem_sublevel, mem_sdiff, mem_filter, mem_univ, true_and, not_le]
      exact ⟨fun h => h.lt_of_ne fun h' => ht ⟨e, h'⟩, le_of_lt⟩
  exact ⟨hi.congr_fun_ae ((ae_restrict_iff' measurableSet_Ioi).2 hae),
    he.trans (setIntegral_congr_ae measurableSet_Ioi hae)⟩

/-- `eq:lovasz` from the side of `g`: if `g(∅) = 0` and `D ≥ 0`, then `t ↦ g({e : D_e ≥ t})` is
integrable on `(0, ∞)` and its integral, the Lovász extension of `g` at `D`, is `C_F(D)` for
`F(S) = g(E \ S)`. -/
theorem gapSum_compl_eq_integral (hD : ∀ e, 0 ≤ D e) {g : Finset (Fin m) → ℝ} (hg : g ∅ = 0) :
    IntegrableOn (fun t => g {e | t ≤ D e}) (Set.Ioi 0) ∧
      gapSum (fun S => g (univ \ S)) D = ∫ t in Set.Ioi 0, g {e | t ≤ D e} :=
  gapSum_eq_integral_lovasz hD (by simpa using hg) fun S => by simp

/-- The value `F(E)` does not enter the gap sum: a gap with `G_k = E` has width `0`. -/
theorem gapSum_ite_univ (hD : ∀ e, 0 ≤ D e) (F : Finset (Fin m) → ℝ) :
    gapSum (fun S => if S = univ then 0 else F S) D = gapSum F D := by
  refine sum_congr rfl fun k hk => ?_
  have hk := mem_range.1 hk
  by_cases h : threshSet D k = univ
  · obtain ⟨e, he⟩ := exists_eq_sortedVal D k.succ_pos hk
    have h1 : D e ≤ sortedVal D k := (filter_eq_self.1 h) e (mem_univ e)
    have h2 := sortedVal_mono hD k.le_succ hk
    rw [show sortedVal D (k + 1) - sortedVal D k = 0 by linarith, zero_mul, zero_mul]
  · simp only [h, if_false]

/-- The Lipschitz bound when `F(E) = 0`, read through the integral: the integrands at `D` and
`D'` differ by at most `c`, and only at `t` with `min(D_e, D'_e) ≤ t < max(D_e, D'_e)` for some
`e`. -/
theorem abs_gapSum_sub_le_of_univ (hD : ∀ e, 0 ≤ D e) (hD' : ∀ e, 0 ≤ D' e)
    {F : Finset (Fin m) → ℝ} {c : ℝ} (hF : ∀ S, 0 ≤ F S ∧ F S ≤ c) (hF0 : F univ = 0) :
    |gapSum F D - gapSum F D'| ≤ c * ∑ e, |D e - D' e| := by
  have hc : 0 ≤ c := (hF ∅).1.trans (hF ∅).2
  obtain ⟨hi, he⟩ := gapSum_eq_integral_Ioi hD hF0
  obtain ⟨hi', he'⟩ := gapSum_eq_integral_Ioi hD' hF0
  rw [he, he', ← integral_sub hi hi']
  let I : Fin m → Set ℝ := fun e => Set.Ico (min (D e) (D' e)) (max (D e) (D' e))
  have hI : ∀ e ∈ univ, Integrable ((I e).indicator fun _ => c) := fun e _ =>
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have hpos : ∀ t, 0 ≤ ∑ e, (I e).indicator (fun _ => c) t := fun t =>
    sum_nonneg fun e _ => Set.indicator_nonneg (fun _ _ => hc) t
  have hpt : ∀ t, |F (sublevel D t) - F (sublevel D' t)|
      ≤ ∑ e, (I e).indicator (fun _ => c) t := by
    intro t
    by_cases h : sublevel D t = sublevel D' t
    · rw [h, sub_self, abs_zero]
      exact hpos t
    obtain ⟨e, he⟩ : ∃ e, ¬(D e ≤ t ↔ D' e ≤ t) := by
      by_contra! H
      exact h (Finset.ext fun e => by simp [H e])
    have hte : t ∈ I e := by
      simp only [I, Set.mem_Ico, min_le_iff, ← not_le, max_le_iff]
      tauto
    have h1 := hF (sublevel D t)
    have h2 := hF (sublevel D' t)
    calc |F (sublevel D t) - F (sublevel D' t)| ≤ c := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
      _ = (I e).indicator (fun _ => c) t := (Set.indicator_of_mem hte fun _ => c).symm
      _ ≤ ∑ e, (I e).indicator (fun _ => c) t :=
        single_le_sum (fun e _ => Set.indicator_nonneg (fun _ _ => hc) t) (mem_univ e)
  calc |∫ t in Set.Ioi 0, F (sublevel D t) - F (sublevel D' t)|
      ≤ ∫ t in Set.Ioi 0, |F (sublevel D t) - F (sublevel D' t)| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioi 0, ∑ e, (I e).indicator (fun _ => c) t :=
      setIntegral_mono (hi.sub hi').abs (integrable_finsetSum _ hI).integrableOn hpt
    _ ≤ ∫ t, ∑ e, (I e).indicator (fun _ => c) t :=
      setIntegral_le_integral (integrable_finsetSum _ hI) (Filter.Eventually.of_forall hpos)
    _ = c * ∑ e, |D e - D' e| := by
      rw [integral_finsetSum _ hI, mul_sum]
      refine sum_congr rfl fun e _ => ?_
      rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le min_le_max,
        max_sub_min_eq_abs', smul_eq_mul, mul_comm]

/-- **The Lipschitz bound.**  If `0 ≤ F(S) ≤ c` for every `S`, then for all `D, D' ≥ 0`,
`|C_F(D) - C_F(D')| ≤ c ‖D - D'‖₁`. -/
theorem abs_gapSum_sub_le (hD : ∀ e, 0 ≤ D e) (hD' : ∀ e, 0 ≤ D' e) {F : Finset (Fin m) → ℝ}
    {c : ℝ} (hF : ∀ S, 0 ≤ F S ∧ F S ≤ c) :
    |gapSum F D - gapSum F D'| ≤ c * ∑ e, |D e - D' e| := by
  rw [← gapSum_ite_univ hD, ← gapSum_ite_univ hD']
  refine abs_gapSum_sub_le_of_univ hD hD' (fun S => ?_) (if_pos rfl)
  split_ifs
  · exact ⟨le_rfl, (hF ∅).1.trans (hF ∅).2⟩
  · exact hF S

/-- **Lemma `lem:lipschitz`.**  For a Boolean observable `F : 2^E → {0, 1}` and all
`D, D' ≥ 0`, `|C_F(D) - C_F(D')| ≤ ‖D - D'‖₁`.  The paper's hypothesis `F(E) = 0` is not
needed. -/
theorem lipschitz (F : Finset (Fin m) → Bool) (hD : ∀ e, 0 ≤ D e) (hD' : ∀ e, 0 ≤ D' e) :
    |gapSum (fun S => if F S then 1 else 0) D - gapSum (fun S => if F S then 1 else 0) D'|
      ≤ ∑ e, |D e - D' e| :=
  (abs_gapSum_sub_le hD hD' fun S => by split_ifs <;> norm_num).trans_eq (one_mul _)

/-- **Corollary `cor:integer-observable`, the Lipschitz bound.**  For `f : 2^E → ℕ` and all
`D, D' ≥ 0`, `|C_f(D) - C_f(D')| ≤ (max_S f(S)) ‖D - D'‖₁`.  The paper's hypothesis
`f(E) = 0` is not needed. -/
theorem integer_observable_lipschitz (f : Finset (Fin m) → ℕ) (hD : ∀ e, 0 ≤ D e)
    (hD' : ∀ e, 0 ≤ D' e) :
    |gapSum (fun S => (f S : ℝ)) D - gapSum (fun S => (f S : ℝ)) D'|
      ≤ (univ.sup f : ℕ) * ∑ e, |D e - D' e| :=
  abs_gapSum_sub_le hD hD' fun S => ⟨Nat.cast_nonneg _, Nat.cast_le.2 (le_sup (mem_univ S))⟩

end SignedTropical.Integral
