import SignedTropical.Rainbow.Defs

/-!
# Connected components

`greedy_intersection.tex`, Lemma `lem:minbases`(4): the ground set splits into connected
components; two distinct elements lie on a common circuit exactly when they lie in one
component; closure, rank, the matroid itself and minimum bases decompose over components.

`connRel M e f` (`Rainbow/Defs.lean`) says that `e = f` or that `e` and `f` lie on a common
circuit of `M : Matroid (Fin m)`.  The results that mention the ground set assume
`M.E = Set.univ`.

* `connRel_equivalence`: `connRel M` is an equivalence relation.  Transitivity rests on
  `exists_isCircuit_of_inter_nonempty`: if a circuit through `x` meets a circuit through `z`,
  some circuit contains `x` and `z` (two strong circuit eliminations and an induction).
* `comp M e`, `components M`: the component of `e` and the set of components.  Every element
  lies in exactly one component (`existsUnique_mem_components`); a loop and a coloop are
  components by themselves (`comp_eq_singleton_of_isLoop`, `comp_eq_singleton_of_isColoop`).
* `exists_isCircuit_iff_comp_eq`: two distinct elements lie on a common circuit if and only if
  they lie in one component.
* `isCircuit_subset_comp`, `fundCircuit_subset_comp`: a circuit lies in one component.
* `mem_closure_iff_comp`, `closure_eq_biUnion_comp`, `rk_eq_sum_comp`, `eq_disjointSigma`,
  `isBase_iff_comp`: closure and rank decompose, `M` is the direct sum of its restrictions to
  the components, and a set is a base if and only if it meets every component `K` in a base of
  `M ↾ K`.
* `isMinBase_iff_comp`: `B` is a minimum base of `u` if and only if every `B ∩ K` is a minimum
  base of `u` in `M ↾ K`.
* `isMinBase_iff_fundCircuit` (Lemma `lem:minbases`(1), proved here for use below) and
  `isMinBase_congr`: the minimum bases of `u` depend only on the comparisons `u_e ≤ u_f` with
  `e`, `f` in one component; `isMinBase_iff_isBase`: for `u` constant on components every base
  is minimum.  The consequences for `M^u` are `minBases_congr` and `minBases_eq_self` of
  `Rainbow/MinBases.lean`.
-/

open Finset
open scoped Matroid

namespace SignedTropical.Rainbow.Conn

variable {m : ℕ} {M : Matroid (Fin m)}

/-! ### The equivalence relation -/

/-- If a circuit through `x` meets a circuit through `z`, some circuit contains `x` and `z`.
Induction on `|C₂ \ C₁|`, with two strong circuit eliminations. -/
theorem exists_isCircuit_of_inter_nonempty {C₁ C₂ : Set (Fin m)} {x z : Fin m}
    (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (hx : x ∈ C₁) (hz : z ∈ C₂)
    (hC : (C₁ ∩ C₂).Nonempty) : ∃ C, M.IsCircuit C ∧ x ∈ C ∧ z ∈ C := by
  induction hn : (C₂ \ C₁).ncard using Nat.strong_induction_on generalizing C₂ with
  | _ n ih =>
  by_cases hxC₂ : x ∈ C₂
  · exact ⟨C₂, hC₂, hxC₂, hz⟩
  by_cases hzC₁ : z ∈ C₁
  · exact ⟨C₁, hC₁, hx, hzC₁⟩
  obtain ⟨y, hy₁, hy₂⟩ := hC
  -- a circuit `C₃ ∋ x` inside `C₁ ∪ C₂` avoiding `y`
  obtain ⟨C₃, hC₃s, hC₃, hxC₃⟩ := hC₁.strong_elimination hC₂ hy₁ hy₂ hx hxC₂
  by_cases hzC₃ : z ∈ C₃
  · exact ⟨C₃, hC₃, hxC₃, hzC₃⟩
  -- `C₃` is not a proper subset of `C₁`, so it meets `C₂ \ C₁`
  obtain ⟨w, hwC₃, hwC₂, hwC₁⟩ : ∃ w ∈ C₃, w ∈ C₂ ∧ w ∉ C₁ := by
    by_contra! h
    refine hC₁.not_ssubset hC₃ ((Set.ssubset_iff_of_subset fun a ha => ?_).2
      ⟨y, hy₁, fun hy => (hC₃s hy).2 rfl⟩)
    obtain ⟨ha₁ | ha₂, -⟩ := hC₃s ha
    · exact ha₁
    · exact h a ha ha₂
  -- a circuit `C₄ ∋ z` inside `C₂ ∪ C₃` avoiding `w`, with fewer elements outside `C₁`
  obtain ⟨C₄, hC₄s, hC₄, hzC₄⟩ := hC₂.strong_elimination hC₃ hwC₂ hwC₃ hz hzC₃
  have hout : C₄ \ C₁ ⊆ (C₂ \ C₁) \ {w} := by
    rintro a ⟨ha, ha₁⟩
    obtain ⟨ha₂ | ha₃, haw⟩ := hC₄s ha
    · exact ⟨⟨ha₂, ha₁⟩, haw⟩
    · exact ⟨⟨(hC₃s ha₃).1.resolve_left ha₁, ha₁⟩, haw⟩
  have hlt : (C₂ \ C₁) \ {w} ⊂ C₂ \ C₁ := Set.sdiff_singleton_ssubset.2 ⟨hwC₂, hwC₁⟩
  refine ih _ (hn ▸ Set.ncard_lt_ncard (hout.trans_ssubset hlt)) hC₄ hzC₄ ?_ rfl
  -- `C₄` meets `C₁`, since it is not a proper subset of `C₂`
  by_contra hdisj
  refine hC₂.not_ssubset hC₄ (lt_of_le_of_lt (fun a ha => ?_) (hlt.trans_le Set.sdiff_subset))
  exact hout ⟨ha, fun ha₁ => hdisj ⟨a, ha₁, ha⟩⟩

theorem connRel_refl (M : Matroid (Fin m)) (e : Fin m) : connRel M e e := .inl rfl

theorem connRel_symm {e f : Fin m} (h : connRel M e f) : connRel M f e :=
  h.imp Eq.symm fun ⟨C, hC, he, hf⟩ => ⟨C, hC, hf, he⟩

theorem connRel_trans {e f g : Fin m} (h₁ : connRel M e f) (h₂ : connRel M f g) :
    connRel M e g := by
  obtain rfl | ⟨C₁, hC₁, he, hf⟩ := h₁
  · exact h₂
  obtain rfl | ⟨C₂, hC₂, hf', hg⟩ := h₂
  · exact .inr ⟨C₁, hC₁, he, hf⟩
  exact .inr (exists_isCircuit_of_inter_nonempty hC₁ hC₂ he hg ⟨f, hf, hf'⟩)

/-- Lemma `lem:minbases`(4): being equal or lying on a common circuit is an equivalence
relation. -/
theorem connRel_equivalence (M : Matroid (Fin m)) : Equivalence (connRel M) :=
  ⟨connRel_refl M, connRel_symm, connRel_trans⟩

/-! ### Components -/

open Classical in
/-- The connected component of `e`: the elements `f` with `connRel M e f`. -/
noncomputable def comp (M : Matroid (Fin m)) (e : Fin m) : Finset (Fin m) :=
  univ.filter (connRel M e)

/-- The connected components of `M`. -/
noncomputable def components (M : Matroid (Fin m)) : Finset (Finset (Fin m)) :=
  univ.image (comp M)

theorem mem_comp {e f : Fin m} : f ∈ comp M e ↔ connRel M e f := by
  simp [comp]

theorem mem_comp_self (e : Fin m) : e ∈ comp M e :=
  mem_comp.2 (connRel_refl M e)

theorem comp_eq_comp_iff {e f : Fin m} : comp M e = comp M f ↔ connRel M e f := by
  refine ⟨fun h => mem_comp.1 (h ▸ mem_comp_self f), fun h => ?_⟩
  ext g
  simp only [mem_comp]
  exact ⟨connRel_trans (connRel_symm h), connRel_trans h⟩

theorem comp_mem_components (e : Fin m) : comp M e ∈ components M :=
  mem_image_of_mem _ (mem_univ e)

theorem mem_components {K : Finset (Fin m)} : K ∈ components M ↔ ∃ e, comp M e = K := by
  simp [components]

theorem comp_eq_of_mem_components {K : Finset (Fin m)} (hK : K ∈ components M) {e : Fin m}
    (he : e ∈ K) : comp M e = K := by
  obtain ⟨f, rfl⟩ := mem_components.1 hK
  exact comp_eq_comp_iff.2 (connRel_symm (mem_comp.1 he))

/-- Lemma `lem:minbases`(4): the ground set splits into components, every element lies in
exactly one component. -/
theorem existsUnique_mem_components (e : Fin m) : ∃! K, K ∈ components M ∧ e ∈ K :=
  ⟨comp M e, ⟨comp_mem_components e, mem_comp_self e⟩,
    fun _ ⟨hK, he⟩ => (comp_eq_of_mem_components hK he).symm⟩

/-- Distinct components are disjoint. -/
theorem disjoint_of_mem_components {K K' : Finset (Fin m)} (hK : K ∈ components M)
    (hK' : K' ∈ components M) (h : K ≠ K') : Disjoint K K' :=
  disjoint_left.2 fun _ he he' =>
    h ((comp_eq_of_mem_components hK he).symm.trans (comp_eq_of_mem_components hK' he'))

/-- A loop is a component by itself. -/
theorem comp_eq_singleton_of_isLoop {e : Fin m} (he : M.IsLoop e) : comp M e = {e} := by
  ext f
  rw [mem_comp, mem_singleton]
  refine ⟨fun h => ?_, fun h => h ▸ connRel_refl M e⟩
  obtain rfl | ⟨C, hC, heC, hfC⟩ := h
  · rfl
  rw [← he.isCircuit.eq_of_subset_isCircuit hC (Set.singleton_subset_iff.2 heC)] at hfC
  exact hfC

/-- A coloop is a component by itself. -/
theorem comp_eq_singleton_of_isColoop {e : Fin m} (he : M.IsColoop e) : comp M e = {e} := by
  ext f
  rw [mem_comp, mem_singleton]
  refine ⟨fun h => ?_, fun h => h ▸ connRel_refl M e⟩
  obtain rfl | ⟨C, hC, heC, -⟩ := h
  · rfl
  exact absurd heC (he.notMem_isCircuit hC)

/-- Lemma `lem:minbases`(4): two distinct elements lie on a common circuit if and only if they
lie in one component. -/
theorem exists_isCircuit_iff_comp_eq {e f : Fin m} (hef : e ≠ f) :
    (∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C) ↔ comp M e = comp M f := by
  rw [comp_eq_comp_iff, connRel, or_iff_right hef]

/-! ### Circuits, closure and rank -/

/-- A circuit lies in the component of each of its elements. -/
theorem isCircuit_subset_comp {C : Set (Fin m)} {e : Fin m} (hC : M.IsCircuit C) (he : e ∈ C) :
    C ⊆ comp M e :=
  fun _ hf => mem_coe.2 (mem_comp.2 (.inr ⟨C, hC, he, hf⟩))

/-- The fundamental circuit `C(B, e)` of a base lies in the component of `e`. -/
theorem fundCircuit_subset_comp {B : Set (Fin m)} (hB : M.IsBase B) (e : Fin m) :
    M.fundCircuit e B ⊆ comp M e := by
  by_cases heB : e ∈ B
  · rw [Matroid.fundCircuit_eq_of_mem heB, Set.singleton_subset_iff]
    exact mem_comp_self e
  by_cases heE : e ∈ M.E
  · exact isCircuit_subset_comp (hB.fundCircuit_isCircuit heE heB) (M.mem_fundCircuit e B)
  rw [Matroid.fundCircuit_eq_of_notMem_ground heE, Set.singleton_subset_iff]
  exact mem_comp_self e

/-- Lemma `lem:minbases`(4): closure decomposes over components, `e ∈ cl(X)` if and only if
`e ∈ cl(X ∩ K)` for the component `K` of `e`. -/
theorem mem_closure_iff_comp {X : Set (Fin m)} {e : Fin m} :
    e ∈ M.closure X ↔ e ∈ M.closure (X ∩ comp M e) := by
  refine ⟨fun h => ?_, fun h => M.closure_subset_closure Set.inter_subset_left h⟩
  by_cases heX : e ∈ X
  · exact M.mem_closure_of_mem' ⟨heX, mem_comp_self e⟩ (M.mem_ground_of_mem_closure h)
  obtain ⟨C, hCX, hC, heC⟩ := Matroid.exists_isCircuit_of_mem_closure h heX
  rw [Matroid.mem_closure_iff_exists_isCircuit fun h' => heX h'.1]
  refine ⟨C, fun f hf => ?_, hC, heC⟩
  obtain rfl | hfX := Set.mem_insert_iff.1 (hCX hf)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨hfX, isCircuit_subset_comp hC heC hf⟩

/-- Lemma `lem:minbases`(4): closure decomposes over components, `cl(X) = ⋃_K cl(X ∩ K)`. -/
theorem closure_eq_biUnion_comp (X : Set (Fin m)) :
    M.closure X = ⋃ K ∈ components M, M.closure (X ∩ K) := by
  ext e
  simp only [Set.mem_iUnion]
  exact ⟨fun h => ⟨comp M e, comp_mem_components e, mem_closure_iff_comp.1 h⟩,
    fun ⟨_, _, h⟩ => M.closure_subset_closure Set.inter_subset_left h⟩

/-- A basis of `X` meets every component `K` in a basis of `X ∩ K`. -/
theorem isBasis_inter_comp {I X : Set (Fin m)} {K : Finset (Fin m)} (hI : M.IsBasis I X)
    (hK : K ∈ components M) : M.IsBasis (I ∩ K) (X ∩ K) := by
  refine (hI.indep.subset Set.inter_subset_left).isBasis_of_subset_of_subset_closure
    (Set.inter_subset_inter_left _ hI.subset) fun e ⟨heX, heK⟩ => ?_
  have h := mem_closure_iff_comp.1 (hI.subset_closure heX)
  rwa [comp_eq_of_mem_components hK heK] at h

/-- Sums split over the components. -/
theorem sum_eq_sum_comp {β : Type*} [AddCommMonoid β] (S : Finset (Fin m)) (f : Fin m → β) :
    ∑ e ∈ S, f e = ∑ K ∈ components M, ∑ e ∈ S ∩ K, f e := by
  rw [← sum_fiberwise_of_maps_to (s := S) (t := components M) (g := comp M)
    (fun e _ => comp_mem_components e) f]
  refine sum_congr rfl fun K hK => sum_congr ?_ fun _ _ => rfl
  ext e
  simp only [mem_filter, mem_inter]
  exact and_congr_right fun _ => ⟨fun h => h ▸ mem_comp_self e, comp_eq_of_mem_components hK⟩

/-- Lemma `lem:minbases`(4): rank is additive over components, `r(X) = ∑_K r(X ∩ K)`. -/
theorem rk_eq_sum_comp (hE : M.E = Set.univ) (X : Finset (Fin m)) :
    rk M X = ∑ K ∈ components M, rk M (X ∩ K) := by
  obtain ⟨I₀, hI₀⟩ := M.exists_isBasis (X : Set (Fin m)) (by rw [hE]; exact Set.subset_univ _)
  obtain ⟨I, rfl⟩ := exists_finset I₀
  rw [← card_eq_rk M hI₀, card_eq_sum_ones, sum_eq_sum_comp (M := M) I]
  refine sum_congr rfl fun K hK => ?_
  rw [← card_eq_sum_ones]
  exact card_eq_rk M (by simpa only [coe_inter] using isBasis_inter_comp hI₀ hK)

/-! ### Direct sum and bases -/

theorem pairwise_disjoint_components (M : Matroid (Fin m)) :
    Pairwise (Function.onFun Disjoint
      fun K : {K // K ∈ components M} => (M ↾ (K.1 : Set (Fin m))).E) := by
  rintro ⟨K, hK⟩ ⟨K', hK'⟩ hne
  simp only [Function.onFun, Matroid.restrict_ground_eq, disjoint_coe]
  exact disjoint_of_mem_components hK hK' fun h => hne (Subtype.ext h)

/-- Lemma `lem:minbases`(4): `M` is the direct sum of its restrictions to its components. -/
theorem eq_disjointSigma (hE : M.E = Set.univ) :
    M = Matroid.disjointSigma (fun K : {K // K ∈ components M} => M ↾ (K.1 : Set (Fin m)))
      (pairwise_disjoint_components M) := by
  have hcov (e : Fin m) : ∃ K : {K // K ∈ components M}, e ∈ (K.1 : Set (Fin m)) :=
    ⟨⟨comp M e, comp_mem_components e⟩, mem_comp_self e⟩
  refine Matroid.ext_indep ?_ fun I _ => ?_
  · simp only [hE, Matroid.disjointSigma_ground_eq, Matroid.restrict_ground_eq]
    exact (Set.iUnion_eq_univ_iff.2 hcov).symm
  simp only [Matroid.disjointSigma_indep_iff, Matroid.restrict_indep_iff,
    Matroid.restrict_ground_eq]
  refine ⟨fun h => ⟨fun K => ⟨h.subset Set.inter_subset_left, Set.inter_subset_right⟩,
    fun e _ => Set.mem_iUnion.2 (hcov e)⟩, fun ⟨h, _⟩ => ?_⟩
  -- a circuit inside `I` lies in one component `K`, hence inside `I ∩ K`
  rw [Matroid.indep_iff_forall_subset_not_isCircuit (by rw [hE]; exact Set.subset_univ I)]
  intro C hCI hC
  obtain ⟨e, he⟩ := hC.nonempty
  exact hC.not_indep ((h ⟨comp M e, comp_mem_components e⟩).1.subset
    (Set.subset_inter hCI (isCircuit_subset_comp hC he)))

/-- `B` is a base if and only if it meets every component `K` in a base of `M ↾ K`. -/
theorem isBase_iff_comp (hE : M.E = Set.univ) (B : Finset (Fin m)) :
    M.IsBase (B : Set (Fin m)) ↔ ∀ K ∈ components M,
      (M ↾ (K : Set (Fin m))).IsBase ((B ∩ K : Finset (Fin m)) : Set (Fin m)) := by
  conv_lhs => rw [eq_disjointSigma hE]
  simp only [Matroid.disjointSigma_isBase_iff, Matroid.restrict_ground_eq, coe_inter,
    Subtype.forall]
  exact and_iff_left fun e _ =>
    Set.mem_iUnion.2 ⟨⟨comp M e, comp_mem_components e⟩, mem_comp_self e⟩

/-! ### Minimum bases -/

/-- Lemma `lem:minbases`(4): `B` is a minimum base of `u` if and only if `B ∩ K` is a minimum
base of `u` in `M ↾ K` for every component `K`. -/
theorem isMinBase_iff_comp (hE : M.E = Set.univ) {u : Fin m → ℝ} {B : Finset (Fin m)} :
    IsMinBase M u B ↔ ∀ K ∈ components M, IsMinBase (M ↾ (K : Set (Fin m))) u (B ∩ K) := by
  refine ⟨fun ⟨hB, hmin⟩ K hK => ⟨(isBase_iff_comp hE B).1 hB K hK, fun BK hBK => ?_⟩,
    fun h => ⟨(isBase_iff_comp hE B).2 fun K hK => (h K hK).1, fun B' hB' => ?_⟩⟩
  · -- replacing `B ∩ K` by a base `BK` of `M ↾ K` gives the base `(B \ K) ∪ BK` of `M`
    have hBKK : BK ⊆ K := coe_subset.1 hBK.subset_ground
    have hB' : M.IsBase ((B \ K ∪ BK : Finset (Fin m)) : Set (Fin m)) := by
      refine (isBase_iff_comp hE _).2 fun K' hK' => ?_
      obtain rfl | hKK' := eq_or_ne K' K
      · rwa [union_inter_distrib_right, sdiff_inter_self, empty_union, inter_eq_left.2 hBKK]
      have hdisj := disjoint_left.1 (disjoint_of_mem_components hK' hK hKK')
      rw [show (B \ K ∪ BK) ∩ K' = B ∩ K' by
        ext x
        simp only [mem_inter, mem_union, mem_sdiff]
        exact ⟨fun ⟨hx, hxK'⟩ => ⟨hx.elim And.left fun hxBK => absurd (hBKK hxBK)
          (hdisj hxK'), hxK'⟩, fun ⟨hxB, hxK'⟩ => ⟨.inl ⟨hxB, hdisj hxK'⟩, hxK'⟩⟩]
      exact (isBase_iff_comp hE B).1 hB K' hK'
    have h := hmin _ hB'
    rw [sum_union (disjoint_of_subset_right hBKK sdiff_disjoint),
      ← sum_inter_add_sum_sdiff B K u] at h
    linarith
  · rw [sum_eq_sum_comp (M := M) B, sum_eq_sum_comp (M := M) B']
    exact sum_le_sum fun K hK => (h K hK).2 _ ((isBase_iff_comp hE B').1 hB' K hK)

/-- A minimum base admits no improving exchange: `u_f ≤ u_e` for `e ∉ B` and `f ∈ C(B, e)`. -/
theorem le_of_mem_fundCircuit {u : Fin m → ℝ} {B : Finset (Fin m)} (hB : IsMinBase M u B)
    {e f : Fin m} (he : e ∉ B) (hf : f ∈ M.fundCircuit e (B : Set (Fin m))) : u f ≤ u e := by
  by_cases hfe : f = e
  · rw [hfe]
  by_cases heE : e ∈ M.E
  swap
  · rw [Matroid.fundCircuit_eq_of_notMem_ground heE] at hf
    exact absurd hf hfe
  have hfB : f ∈ B := by
    have h := M.fundCircuit_subset_insert e (B : Set (Fin m)) hf
    rw [Set.mem_insert_iff] at h
    exact h.resolve_left hfe
  -- `B - f + e` is a base
  have hI := (hB.1.indep.mem_fundCircuit_iff (by rw [hB.1.closure_eq]; exact heE) he).1 hf
  have hB' : M.IsBase (((insert e B).erase f : Finset (Fin m)) : Set (Fin m)) := by
    rw [coe_erase, coe_insert]
    exact hB.1.exchange_isBase_of_indep' hfB he hI
  have h := hB.2 _ hB'
  rw [sum_erase_eq_sub (mem_insert_of_mem hfB), sum_insert he] at h
  linarith

/-- A base with no improving exchange is a minimum base.  Induction on `|B' \ B|`: an element
`f ∈ B \ B'` and an element `e ≠ f` of `C(B', f)` in the fundamental cocircuit of `f` in `B`
give the base `B' - e + f`, closer to `B` and of no larger weight. -/
theorem isMinBase_of_forall_fundCircuit {u : Fin m → ℝ} {B : Finset (Fin m)}
    (hB : M.IsBase (B : Set (Fin m)))
    (hloc : ∀ e ∉ B, ∀ f ∈ M.fundCircuit e (B : Set (Fin m)), u f ≤ u e) : IsMinBase M u B := by
  refine ⟨hB, fun B' hB' => ?_⟩
  induction hn : (B' \ B).card using Nat.strong_induction_on generalizing B' with
  | _ n ih =>
  by_cases hsub : B ⊆ B'
  · rw [coe_inj.1 (hB.eq_of_subset_isBase hB' (coe_subset.2 hsub))]
  obtain ⟨f, hfB, hfB'⟩ := not_subset.1 hsub
  have hfE : f ∈ M.E := hB.subset_ground hfB
  -- the fundamental circuit of `f` in `B'` meets the fundamental cocircuit of `f` in `B` twice
  have hC := hB'.fundCircuit_isCircuit hfE hfB'
  have hK := Matroid.fundCocircuit_isCocircuit (mem_coe.2 hfB) hB
  obtain ⟨e, ⟨heC, heK⟩, hef⟩ := (hC.isCocircuit_inter_nontrivial hK
    ⟨f, M.mem_fundCircuit f _, M.mem_fundCocircuit f _⟩).exists_ne f
  have heB' : e ∈ B' := by
    have h := M.fundCircuit_subset_insert f (B' : Set (Fin m)) heC
    rw [Set.mem_insert_iff] at h
    exact h.resolve_left hef
  have heB : e ∉ B := by
    have h := M.fundCocircuit_subset_insert_compl f (B : Set (Fin m)) heK
    rw [Set.mem_insert_iff] at h
    exact (h.resolve_left hef).2
  have hfe : u f ≤ u e := hloc e heB f (hB.mem_fundCocircuit_iff_mem_fundCircuit.1 heK)
  have hB'' : M.IsBase (((insert f B').erase e : Finset (Fin m)) : Set (Fin m)) := by
    rw [coe_erase, coe_insert]
    exact hB'.exchange_isBase_of_indep' heB' hfB'
      ((hB'.indep.mem_fundCircuit_iff (by rw [hB'.closure_eq]; exact hfE) hfB').1 heC)
  have hcard : ((insert f B').erase e \ B).card < n := by
    rw [← hn, show (insert f B').erase e \ B = (B' \ B).erase e by
      ext x
      simp only [mem_sdiff, mem_erase, mem_insert]
      constructor
      · rintro ⟨⟨hxe, rfl | hx⟩, hxB⟩
        · exact absurd hfB hxB
        · exact ⟨hxe, hx, hxB⟩
      · rintro ⟨hxe, hx, hxB⟩
        exact ⟨⟨hxe, .inr hx⟩, hxB⟩]
    exact card_erase_lt_of_mem (mem_sdiff.2 ⟨heB', heB⟩)
  have h := ih _ hcard _ hB'' rfl
  rw [sum_erase_eq_sub (mem_insert_of_mem heB'), sum_insert hfB'] at h
  linarith

/-- Lemma `lem:minbases`(1): a base `B` is minimum for `u` if and only if `u_f ≤ u_e`
whenever `e ∉ B` and `f ∈ C(B, e)`. -/
theorem isMinBase_iff_fundCircuit {u : Fin m → ℝ} {B : Finset (Fin m)} :
    IsMinBase M u B ↔ M.IsBase (B : Set (Fin m)) ∧
      ∀ e ∉ B, ∀ f ∈ M.fundCircuit e (B : Set (Fin m)), u f ≤ u e :=
  ⟨fun h => ⟨h.1, fun _ he _ hf => le_of_mem_fundCircuit h he hf⟩,
    fun h => isMinBase_of_forall_fundCircuit h.1 h.2⟩

/-- Lemma `lem:minbases`(4), the form used for PO-SL: the minimum bases of `u` and `u'` agree
when `u_e ≤ u_f ↔ u'_e ≤ u'_f` for all `e`, `f` in one component. -/
theorem isMinBase_congr {u u' : Fin m → ℝ}
    (h : ∀ e f, connRel M e f → (u e ≤ u f ↔ u' e ≤ u' f)) {B : Finset (Fin m)} :
    IsMinBase M u B ↔ IsMinBase M u' B := by
  simp only [isMinBase_iff_fundCircuit]
  refine and_congr_right fun hB => forall₂_congr fun e _ => forall₂_congr fun f hf => h f e ?_
  exact connRel_symm (mem_comp.1 (fundCircuit_subset_comp hB e hf))

/-- If `u` is constant on every component, every base is a minimum base of `u`. -/
theorem isMinBase_iff_isBase {u : Fin m → ℝ} (h : ∀ e f, connRel M e f → u e = u f)
    {B : Finset (Fin m)} : IsMinBase M u B ↔ M.IsBase (B : Set (Fin m)) := by
  rw [isMinBase_congr (u' := 0) fun e f hef => by simp [h e f hef]]
  exact ⟨fun h => h.1, fun hB => ⟨hB, fun _ _ => by simp⟩⟩

theorem minBases_ground (M : Matroid (Fin m)) (u : Fin m → ℝ) : (minBases M u).E = Set.univ := by
  simp [minBases, levelPiece_ground, Set.eq_univ_iff_forall]

end SignedTropical.Rainbow.Conn
