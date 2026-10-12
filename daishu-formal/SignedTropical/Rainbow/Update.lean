import SignedTropical.Rainbow.MinBases
import SignedTropical.Integral

/-!
# The update

`greedy_intersection.tex`, Section 4.4: Definition `def:update`, the paragraph after it, and
equation `eq:update-integral`.  `M : Matroid (Fin m)` has ground set `univ` and rank `k`, the
blocks are the fibres of `blk : Fin m → Fin k`, and `N : ℝ → Matroid (Fin m)` is an admissible
family for the weight `v` (`IsAdmissible M blk v N`, Definition `def:admissible`).  The stage
`r` enters as a parameter; the paper's standing hypothesis is `ν₀ = ν(M^v) = r < k`.

Definitions (none of them assumes admissibility):

* `BaseMisses N blk r b`: some base of `N` meeting exactly `r` blocks misses the block `b`;
* `tau N blk r = τ = min {t ≥ 0 : ν(N(t)) ≥ r + 1}`, a real infimum;
* `lam N blk r b = λ_b = min {t ≥ 0 : BaseMisses (N t) blk r b}`, an infimum in `[0, ∞]`,
  equal to `∞` when no such `t` exists;
* `update N blk r b = a_b = (τ - λ_b)₊`, computed in `[0, ∞]` (where `τ - ∞ = 0`).

Results:

* `isLeast_sInf`: by (F5), a nonempty set `{t ≥ 0 : P(N(t))}` has a least element.  Hence
  `isLeast_tau` (by (F1), (F2), (F4), (F5)) and `exists_isLeast_lam` (by (F5)): the minima of
  the definition exist; `lam_eq_top_iff`: `λ_b = ∞` exactly when there is none.
* The paragraph after the definition: `nu_eq_of_lt_tau` (`ν(N(t)) = r` for `t < τ`),
  `succ_le_nu_of_tau_le`; `exists_isRainbowIndep_subset`, `exists_isBase_of_isRainbowIndep` and
  `mem_Av_iff_baseMisses` (a base meeting `r` blocks contains a rainbow independent set of size
  `r` and conversely); `lam_le_iff` and `mem_Av_iff_lam_le` (the set of `t ∈ [0, τ)` at which
  `b` is avoidable is `[λ_b, τ)`).
* `update_eq_zero`: `a = 0` if `ν₀ > r`, as the definition sets.  `update_eq_tau`,
  `update_le_of_forall_notMem`, `update_eq_max`: the values used later.
* Equation `eq:update-integral`: `volume_eq` (`a_b` is the Lebesgue measure of
  `{t ≥ 0 : ν(N(t)) ≤ r, b ∈ Av(N(t))}`), `update_eq_integral` (the integral over `(0, ∞)`)
  and `update_eq_intervalIntegral` (the integral over `[0, T]` for every `T ≥ τ`), for every
  `r ≤ ν₀`, so for both cases of the definition.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace SignedTropical.Rainbow.Validity

open SignedTropical.Rainbow

variable {m k : ℕ}

/-! ### Definition `def:update` -/

/-- Some base of `N` meeting exactly `r` blocks misses the block `b`. -/
def BaseMisses (N : Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (b : Fin k) : Prop :=
  ∃ B : Finset (Fin m), N.IsBase (B : Set (Fin m)) ∧ #(blocksMet blk B) = r ∧
    b ∉ blocksMet blk B

/-- `τ = min {t ≥ 0 : ν(N(t)) ≥ r + 1}`; the minimum exists for an admissible family
(`isLeast_tau`). -/
noncomputable def tau (N : ℝ → Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) : ℝ :=
  sInf {t | 0 ≤ t ∧ r + 1 ≤ nu (N t) blk}

/-- `λ_b = min {t ≥ 0 : some base of N(t) meeting exactly r blocks misses b}`, and `∞` if there
is none: the infimum in `[0, ∞]`, which is `∞` for the empty set (`lam_eq_top_iff`) and a
minimum otherwise (`exists_isLeast_lam`). -/
noncomputable def lam (N : ℝ → Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (b : Fin k) :
    ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ BaseMisses (N t) blk r b), ENNReal.ofReal t

/-- **Definition `def:update`.**  The update `a_b = (τ - λ_b)₊`, computed in `[0, ∞]`, where
`τ - ∞ = 0`; the update is `p ↦ p + a`.  If `ν₀ > r`, then `τ = 0` and `a = 0`
(`update_eq_zero`), as the definition sets. -/
noncomputable def update (N : ℝ → Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (b : Fin k) :
    ℝ :=
  (ENNReal.ofReal (tau N blk r) - lam N blk r b).toReal

/-! ### The minima exist -/

/-- By (F5), a nonempty set `{t ≥ 0 : P(N(t))}` has a least element, its infimum: `N` is
constant on `[l, t]` for `t` below the least level above the infimum `l`. -/
theorem isLeast_sInf {N : ℝ → Matroid (Fin m)}
    (hF5 : ∃ c : Finset ℝ, 0 ∈ c ∧ ∀ t t', 0 ≤ t → t ≤ t' →
      (∀ x ∈ c, ¬(t < x ∧ x ≤ t')) → N t = N t')
    {P : Matroid (Fin m) → Prop} (h : ∃ t, 0 ≤ t ∧ P (N t)) :
    IsLeast {t | 0 ≤ t ∧ P (N t)} (sInf {t | 0 ≤ t ∧ P (N t)}) := by
  obtain ⟨c, -, hc⟩ := hF5
  set S := {t | 0 ≤ t ∧ P (N t)}
  have hbdd : BddBelow S := ⟨0, fun _ ht => ht.1⟩
  have hl0 : 0 ≤ sInf S := Real.sInf_nonneg fun _ ht => ht.1
  -- some `t ∈ S` has no level in `(sInf S, t]`, so `N(sInf S) = N(t)`
  obtain ⟨t, htS, hlev⟩ : ∃ t ∈ S, ∀ x ∈ c, ¬(sInf S < x ∧ x ≤ t) := by
    by_cases hc' : (c.filter (sInf S < ·)).Nonempty
    · obtain ⟨t, htS, htx⟩ := exists_lt_of_csInf_lt h (mem_filter.1 (min'_mem _ hc')).2
      exact ⟨t, htS, fun x hx hlx =>
        (htx.trans_le (min'_le _ x (mem_filter.2 ⟨hx, hlx.1⟩))).not_ge hlx.2⟩
    · obtain ⟨t, htS⟩ := h
      exact ⟨t, htS, fun x hx hlx => hc' ⟨x, mem_filter.2 ⟨hx, hlx.1⟩⟩⟩
  refine ⟨⟨hl0, ?_⟩, fun _ ht => csInf_le hbdd ht⟩
  rw [hc _ t hl0 (csInf_le hbdd htS) hlev]
  exact htS.2

variable {M : Matroid (Fin m)} {blk : Fin m → Fin k} {v : Fin m → ℝ} {N : ℝ → Matroid (Fin m)}
  {r : ℕ} {b : Fin k}

/-- `ν(N(t))` grows with `t`, by (F2). -/
theorem nu_mono_of_le (hN : IsAdmissible M blk v N) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') :
    nu (N t) blk ≤ nu (N t') blk :=
  nu_mono (hN.F2 t t' ht htt')

/-- `ν₀ ≤ ν(N(t))` for `t ≥ 0`, by (F1) and (F2). -/
theorem nu_zero_le (hN : IsAdmissible M blk v N) {t : ℝ} (ht : 0 ≤ t) :
    nu (minBases M v) blk ≤ nu (N t) blk :=
  hN.F1 ▸ nu_mono_of_le hN le_rfl ht

/-- `N(t)` has rank `k` for `t ≥ 0`: by (F1) and (F2) a base of `M^v` is a base of `N(t)`. -/
theorem rank_eq_of_isAdmissible (hE : M.E = Set.univ) (hk : rank M = k)
    (hN : IsAdmissible M blk v N) {t : ℝ} (ht : 0 ≤ t) : rank (N t) = k := by
  obtain ⟨B, hB⟩ := (N 0).exists_isBase
  obtain ⟨B, rfl⟩ := exists_finset B
  rw [← card_base (N t) (hN.F2 0 t le_rfl ht B hB), card_base (N 0) hB, hN.F1,
    rank_minBases hE v, hk]

/-- By (F4), `ν(N(t)) ≥ r + 1` for some `t ≥ 0` when `r < k`. -/
theorem exists_succ_le_nu (hE : M.E = Set.univ) (hk : rank M = k) (hrk : r < k)
    (hN : IsAdmissible M blk v N) : ∃ t, 0 ≤ t ∧ r + 1 ≤ nu (N t) blk := by
  obtain ⟨T, hT, hTb⟩ := hN.F4
  refine ⟨T, hT, ?_⟩
  rw [nu_eq_rank_iff.2 (hTb T le_rfl), rank_eq_of_isAdmissible hE hk hN hT]
  exact hrk

/-- **Definition `def:update`, `τ` is a minimum** (by (F1), (F2), (F4) and (F5)). -/
theorem isLeast_tau (hE : M.E = Set.univ) (hk : rank M = k) (hrk : r < k)
    (hN : IsAdmissible M blk v N) :
    IsLeast {t | 0 ≤ t ∧ r + 1 ≤ nu (N t) blk} (tau N blk r) :=
  isLeast_sInf (P := fun N' => r + 1 ≤ nu N' blk) hN.F5 (exists_succ_le_nu hE hk hrk hN)

theorem tau_nonneg : 0 ≤ tau N blk r :=
  Real.sInf_nonneg fun _ ht => ht.1

/-- `λ_b = ∞` exactly when no base of any `N(t)` meeting exactly `r` blocks misses `b`. -/
theorem lam_eq_top_iff : lam N blk r b = ⊤ ↔ ∀ t, 0 ≤ t → ¬BaseMisses (N t) blk r b := by
  simp [lam, iInf_eq_top, ENNReal.ofReal_ne_top]

theorem lam_le_ofReal {t : ℝ} (ht : 0 ≤ t) (h : BaseMisses (N t) blk r b) :
    lam N blk r b ≤ ENNReal.ofReal t :=
  iInf₂_le t ⟨ht, h⟩

/-- **Definition `def:update`, `λ_b` is a minimum** (by (F5)): if some base of some `N(t)`
meeting exactly `r` blocks misses `b`, the least such `t` exists and is `λ_b`. -/
theorem exists_isLeast_lam (hN : IsAdmissible M blk v N)
    (h : ∃ t, 0 ≤ t ∧ BaseMisses (N t) blk r b) :
    ∃ l, IsLeast {t | 0 ≤ t ∧ BaseMisses (N t) blk r b} l ∧ lam N blk r b = ENNReal.ofReal l := by
  have hl := isLeast_sInf (P := fun N' => BaseMisses N' blk r b) hN.F5 h
  refine ⟨_, hl, le_antisymm (lam_le_ofReal hl.1.1 hl.1.2) (le_iInf₂ fun t ht => ?_)⟩
  exact ENNReal.ofReal_le_ofReal (hl.2 ht)

/-- By (F2), a base of `N(t)` meeting `r` blocks and missing `b` is one of `N(t')`, `t ≤ t'`. -/
theorem BaseMisses.mono (hN : IsAdmissible M blk v N) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t')
    (h : BaseMisses (N t) blk r b) : BaseMisses (N t') blk r b :=
  let ⟨B, hB, hc, hb⟩ := h
  ⟨B, hN.F2 t t' ht htt' B hB, hc, hb⟩

/-- The set of `t ≥ 0` at which some base of `N(t)` meeting exactly `r` blocks misses `b` is
`[λ_b, ∞)`, by (F2) and (F5). -/
theorem lam_le_iff (hN : IsAdmissible M blk v N) {t : ℝ} (ht : 0 ≤ t) :
    lam N blk r b ≤ ENNReal.ofReal t ↔ BaseMisses (N t) blk r b := by
  refine ⟨fun h => ?_, lam_le_ofReal ht⟩
  by_cases hex : ∃ t, 0 ≤ t ∧ BaseMisses (N t) blk r b
  · obtain ⟨l, hl, hlam⟩ := exists_isLeast_lam hN hex
    rw [hlam, ENNReal.ofReal_le_ofReal_iff ht] at h
    exact hl.1.2.mono hN hl.1.1 h
  · rw [(lam_eq_top_iff.2 fun t ht h => hex ⟨t, ht, h⟩), top_le_iff] at h
    exact absurd h ENNReal.ofReal_ne_top

/-! ### The paragraph after the definition -/

/-- For `0 ≤ t < τ`, `ν(N(t)) = r` (by (F1), (F2) and the choice of `τ`). -/
theorem nu_eq_of_lt_tau (hr : r ≤ nu (minBases M v) blk) (hN : IsAdmissible M blk v N) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < tau N blk r) : nu (N t) blk = r := by
  refine le_antisymm (not_lt.1 fun h => ht.not_ge ?_) (hr.trans (nu_zero_le hN ht0))
  exact csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht0, h⟩

/-- For `t ≥ τ`, `ν(N(t)) ≥ r + 1`. -/
theorem succ_le_nu_of_tau_le (hE : M.E = Set.univ) (hk : rank M = k) (hrk : r < k)
    (hN : IsAdmissible M blk v N) {t : ℝ} (ht : tau N blk r ≤ t) : r + 1 ≤ nu (N t) blk :=
  (isLeast_tau hE hk hrk hN).1.2.trans
    (nu_mono_of_le hN (isLeast_tau hE hk hrk hN).1.1 ht)

/-- A base contains a rainbow independent set meeting the same blocks. -/
theorem exists_isRainbowIndep_subset {N : Matroid (Fin m)} {B : Finset (Fin m)}
    (hB : N.IsBase (B : Set (Fin m))) :
    ∃ I ⊆ B, IsRainbowIndep N blk I ∧ blocksMet blk I = blocksMet blk B := by
  obtain ⟨I, hIB, hI, himg⟩ := exists_subset_injOn_image_eq_of_surjOn (f := blk) (B : Set (Fin m))
    (blocksMet blk B) (by rw [blocksMet, coe_image]; exact Set.surjOn_image blk _)
  exact ⟨I, coe_subset.1 hIB, ⟨hB.indep.subset hIB, hI⟩, himg⟩

/-- A rainbow independent set of size `ν(N)` lies in a base of `N` meeting the same blocks. -/
theorem exists_isBase_of_isRainbowIndep {N : Matroid (Fin m)} {I : Finset (Fin m)}
    (hI : IsRainbowIndep N blk I) (hcard : #I = nu N blk) :
    ∃ B : Finset (Fin m), N.IsBase (B : Set (Fin m)) ∧ I ⊆ B ∧
      blocksMet blk B = blocksMet blk I := by
  obtain ⟨B, hB, hIB⟩ := hI.1.exists_isBase_superset
  obtain ⟨B, rfl⟩ := exists_finset B
  refine ⟨B, hB, coe_subset.1 hIB, (eq_of_subset_of_card_le
    (image_subset_image (coe_subset.1 hIB)) ?_).symm⟩
  change #(blocksMet blk B) ≤ #(blocksMet blk I)
  rw [hI.2.card_blocksMet, hcard]
  exact card_blocksMet_le_nu hB.indep

/-- Some base of `N` meets exactly `ν(N)` blocks. -/
theorem exists_isBase_card_blocksMet (N : Matroid (Fin m)) (blk : Fin m → Fin k) :
    ∃ B : Finset (Fin m), N.IsBase (B : Set (Fin m)) ∧ #(blocksMet blk B) = nu N blk := by
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu N blk
  obtain ⟨B, hB, -, hBI⟩ := exists_isBase_of_isRainbowIndep hI hcard
  exact ⟨B, hB, by rw [hBI, hI.2.card_blocksMet, hcard]⟩

/-- If `ν(N) = r`, then `b ∈ Av(N)` iff some base of `N` meeting exactly `r` blocks misses `b`:
a base meeting `r` blocks contains a rainbow independent set of size `r` meeting the same
blocks, and conversely. -/
theorem mem_Av_iff_baseMisses {N : Matroid (Fin m)} (h : nu N blk = r) :
    b ∈ Av N blk ↔ BaseMisses N blk r b := by
  rw [mem_Av]
  constructor
  · rintro ⟨I, hI, hcard, hb⟩
    obtain ⟨B, hB, -, hBI⟩ := exists_isBase_of_isRainbowIndep hI hcard
    exact ⟨B, hB, by rw [hBI, hI.2.card_blocksMet, hcard, h], hBI ▸ hb⟩
  · rintro ⟨B, hB, hcard, hb⟩
    obtain ⟨I, -, hI, hIB⟩ := exists_isRainbowIndep_subset (blk := blk) hB
    exact ⟨I, hI, by rw [← hI.2.card_blocksMet, hIB, hcard, h], hIB ▸ hb⟩

/-- The set of `t ∈ [0, τ)` at which `b` is avoidable is `[λ_b, τ)`. -/
theorem mem_Av_iff_lam_le (hr : r ≤ nu (minBases M v) blk) (hN : IsAdmissible M blk v N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < tau N blk r) :
    b ∈ Av (N t) blk ↔ lam N blk r b ≤ ENNReal.ofReal t := by
  rw [lam_le_iff hN ht0, mem_Av_iff_baseMisses (nu_eq_of_lt_tau hr hN ht0 ht)]

/-- `λ_b = 0` exactly for the blocks avoidable in `M^v`. -/
theorem lam_eq_zero_iff (hr : nu (minBases M v) blk = r) (hN : IsAdmissible M blk v N) :
    lam N blk r b = 0 ↔ b ∈ Av (minBases M v) blk := by
  rw [← hN.F1, mem_Av_iff_baseMisses (by rw [hN.F1, hr]), ← lam_le_iff hN le_rfl,
    ENNReal.ofReal_zero, nonpos_iff_eq_zero]

/-! ### Values of the update -/

theorem update_nonneg : 0 ≤ update N blk r b :=
  ENNReal.toReal_nonneg

theorem update_le_tau : update N blk r b ≤ tau N blk r :=
  (ENNReal.toReal_mono ENNReal.ofReal_ne_top tsub_le_self).trans_eq
    (ENNReal.toReal_ofReal tau_nonneg)

theorem ofReal_update :
    ENNReal.ofReal (update N blk r b) = ENNReal.ofReal (tau N blk r) - lam N blk r b :=
  ENNReal.ofReal_toReal (ENNReal.sub_ne_top ENNReal.ofReal_ne_top)

/-- If `λ_b = l` is finite, `a_b = (τ - l)₊`. -/
theorem update_eq_max {l : ℝ} (hl : 0 ≤ l) (h : lam N blk r b = ENNReal.ofReal l) :
    update N blk r b = max (tau N blk r - l) 0 := by
  rw [update, h, ← ENNReal.ofReal_sub _ hl, ENNReal.toReal_ofReal']

/-- If `λ_b = ∞`, then `a_b = 0`. -/
theorem update_eq_zero_of_lam_eq_top (h : lam N blk r b = ⊤) : update N blk r b = 0 := by
  rw [update, h, ENNReal.sub_top, ENNReal.toReal_zero]

/-- If `ν₀ > r`, then `τ = 0`; only (F1) is used. -/
theorem tau_eq_zero (hN1 : N 0 = minBases M v) (h : r < nu (minBases M v) blk) :
    tau N blk r = 0 :=
  le_antisymm (csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨le_rfl, hN1 ▸ h⟩) tau_nonneg

/-- **Definition `def:update`, the case `ν₀ > r`.**  Then `a = 0`; only (F1) is used. -/
theorem update_eq_zero (hN1 : N 0 = minBases M v) (h : r < nu (minBases M v) blk) :
    update N blk r = 0 := by
  ext b
  rw [update, tau_eq_zero hN1 h, ENNReal.ofReal_zero, zero_tsub, ENNReal.toReal_zero,
    Pi.zero_apply]

/-- A block avoidable in `M^v` has `λ_b = 0` and receives `a_b = τ`. -/
theorem update_eq_tau (hr : nu (minBases M v) blk = r) (hN : IsAdmissible M blk v N)
    (hb : b ∈ Av (minBases M v) blk) : update N blk r b = tau N blk r := by
  rw [update, (lam_eq_zero_iff hr hN).2 hb, tsub_zero, ENNReal.toReal_ofReal tau_nonneg]

/-- If `δ ≤ τ` and `b` is avoidable at no `t ∈ [0, δ)`, then `a_b ≤ τ - δ`, as `λ_b ≥ δ`. -/
theorem update_le_of_forall_notMem (hr : r ≤ nu (minBases M v) blk)
    (hN : IsAdmissible M blk v N) {δ : ℝ} (hδ : δ ≤ tau N blk r)
    (h : ∀ t, 0 ≤ t → t < δ → b ∉ Av (N t) blk) : update N blk r b ≤ tau N blk r - δ := by
  by_cases htop : lam N blk r b = ⊤
  · rw [update_eq_zero_of_lam_eq_top htop]
    linarith
  obtain ⟨l, hl0, hl⟩ : ∃ l, 0 ≤ l ∧ lam N blk r b = ENNReal.ofReal l :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
  have hδl : δ ≤ l := not_lt.1 fun hlt =>
    h l hl0 hlt ((mem_Av_iff_lam_le hr hN hl0 (hlt.trans_le hδ)).2 hl.le)
  rw [update_eq_max hl0 hl]
  exact max_le (by linarith) (by linarith)

/-! ### Equation `eq:update-integral` -/

/-- The set `{t ≥ 0 : ν(N(t)) ≤ r, b ∈ Av(N(t))}` is `{t ∈ [0, τ) : λ_b ≤ t}`. -/
theorem setOf_nu_le_mem_Av_eq (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : r ≤ nu (minBases M v) blk) (hrk : r < k) (hN : IsAdmissible M blk v N) :
    {t | 0 ≤ t ∧ nu (N t) blk ≤ r ∧ b ∈ Av (N t) blk} =
      {t | 0 ≤ t ∧ t < tau N blk r ∧ lam N blk r b ≤ ENNReal.ofReal t} := by
  ext t
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun ht0 => ?_
  by_cases ht : t < tau N blk r
  · rw [mem_Av_iff_lam_le hr hN ht0 ht, nu_eq_of_lt_tau hr hN ht0 ht]
    simp [ht]
  · have := succ_le_nu_of_tau_le hE hk hrk hN (not_lt.1 ht)
    simp only [ht, false_and, iff_false, not_and]
    intro h
    omega

theorem measurableSet_setOf_nu_le_mem_Av (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : r ≤ nu (minBases M v) blk) (hrk : r < k) (hN : IsAdmissible M blk v N) :
    MeasurableSet {t | 0 ≤ t ∧ nu (N t) blk ≤ r ∧ b ∈ Av (N t) blk} := by
  rw [setOf_nu_le_mem_Av_eq hE hk hr hrk hN, Set.setOf_and, Set.setOf_and]
  exact (measurableSet_le measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const ENNReal.measurable_ofReal))

/-- **Equation `eq:update-integral`, measure form.**  For `r ≤ ν₀` (both cases of Definition
`def:update`), `a_b` is the Lebesgue measure of `{t ≥ 0 : ν(N(t)) ≤ r, b ∈ Av(N(t))}`. -/
theorem volume_eq (hE : M.E = Set.univ) (hk : rank M = k) (hr : r ≤ nu (minBases M v) blk)
    (hrk : r < k) (hN : IsAdmissible M blk v N) :
    volume {t | 0 ≤ t ∧ nu (N t) blk ≤ r ∧ b ∈ Av (N t) blk} =
      ENNReal.ofReal (update N blk r b) := by
  rw [setOf_nu_le_mem_Av_eq hE hk hr hrk hN, ofReal_update]
  by_cases htop : lam N blk r b = ⊤
  · simp [htop, ENNReal.ofReal_ne_top]
  obtain ⟨l, hl0, hl⟩ : ∃ l, 0 ≤ l ∧ lam N blk r b = ENNReal.ofReal l :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
  have hset : {t | 0 ≤ t ∧ t < tau N blk r ∧ ENNReal.ofReal l ≤ ENNReal.ofReal t} =
      Set.Ico l (tau N blk r) := by
    ext t
    exact ⟨fun ⟨ht0, htτ, hlt⟩ => ⟨(ENNReal.ofReal_le_ofReal_iff ht0).1 hlt, htτ⟩,
      fun ⟨hlt, htτ⟩ => ⟨hl0.trans hlt, htτ, ENNReal.ofReal_le_ofReal hlt⟩⟩
  rw [hl, hset, Real.volume_Ico, ENNReal.ofReal_sub _ hl0]

/-- **Equation `eq:update-integral`.**  For `r ≤ ν₀` (both cases of Definition `def:update`),
`a_b = ∫_0^∞ 1[ν(N(t)) ≤ r] 1[b ∈ Av(N(t))] dt`, the integrand being integrable on `(0, ∞)`. -/
theorem update_eq_integral (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : r ≤ nu (minBases M v) blk) (hrk : r < k) (hN : IsAdmissible M blk v N) :
    IntegrableOn (fun t => (if nu (N t) blk ≤ r then (1 : ℝ) else 0) *
        (if b ∈ Av (N t) blk then 1 else 0)) (Set.Ioi 0) ∧
      update N blk r b = ∫ t in Set.Ioi 0, (if nu (N t) blk ≤ r then (1 : ℝ) else 0) *
        (if b ∈ Av (N t) blk then 1 else 0) := by
  set A := {t | 0 ≤ t ∧ nu (N t) blk ≤ r ∧ b ∈ Av (N t) blk}
  have hA : MeasurableSet A := measurableSet_setOf_nu_le_mem_Av hE hk hr hrk hN
  have hvol : volume A = ENNReal.ofReal (update N blk r b) := volume_eq hE hk hr hrk hN
  have heq : Set.EqOn (A.indicator 1) (fun t => (if nu (N t) blk ≤ r then (1 : ℝ) else 0) *
      (if b ∈ Av (N t) blk then 1 else 0)) (Set.Ioi 0) := fun t ht => by
    simp only [A, Set.indicator, Set.mem_setOf_eq, Pi.one_apply, ite_zero_mul_ite_zero, mul_one,
      le_of_lt (Set.mem_Ioi.1 ht), true_and]
  refine ⟨IntegrableOn.congr_fun ?_ heq measurableSet_Ioi, ?_⟩
  · exact ((integrable_indicator_iff hA).2
      (integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top))).integrableOn
  · rw [← setIntegral_congr_fun measurableSet_Ioi heq, ← integral_Ici_eq_integral_Ioi,
      integral_indicator_one hA, measureReal_restrict_apply hA,
      Set.inter_eq_left.2 fun t ht => ht.1, measureReal_def, hvol,
      ENNReal.toReal_ofReal update_nonneg]

/-- **Equation `eq:update-integral` on a bounded interval.**  For `r ≤ ν₀` and every `T ≥ τ`,
`a_b = ∫_0^T 1[ν(N(t)) ≤ r] 1[b ∈ Av(N(t))] dt`, the integrand being integrable on `[0, T]`. -/
theorem update_eq_intervalIntegral (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : r ≤ nu (minBases M v) blk) (hrk : r < k) (hN : IsAdmissible M blk v N) {T : ℝ}
    (hT : tau N blk r ≤ T) :
    IntervalIntegrable (fun t => (if nu (N t) blk ≤ r then (1 : ℝ) else 0) *
        (if b ∈ Av (N t) blk then 1 else 0)) volume 0 T ∧
      update N blk r b = ∫ t in (0)..T, (if nu (N t) blk ≤ r then (1 : ℝ) else 0) *
        (if b ∈ Av (N t) blk then 1 else 0) := by
  obtain ⟨hi, he⟩ := update_eq_integral (b := b) hE hk hr hrk hN
  have hT0 : 0 ≤ T := tau_nonneg.trans hT
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).2
    (hi.mono_set Set.Ioc_subset_Ioi_self), ?_⟩
  rw [intervalIntegral.integral_of_le hT0, he]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self fun t ht => ?_
  have htT : T < t := not_le.1 fun h => ht.2 ⟨ht.1, h⟩
  have := succ_le_nu_of_tau_le hE hk hrk hN (hT.trans htT.le)
  rw [if_neg (by omega), zero_mul]

end SignedTropical.Rainbow.Validity
