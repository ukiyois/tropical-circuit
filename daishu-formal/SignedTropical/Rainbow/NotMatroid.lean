import SignedTropical.Rainbow.Defs

/-!
# The possibly optimal bases need not form a matroid (Proposition `prop:notmatroid`)

`greedy_intersection.tex`, Section 4.3, Proposition `prop:notmatroid`.

* `unif r m`: the uniform matroid `U_{r,m}` on `Fin m`, with ground set `univ`; a set is
  independent if and only if it has at most `r` elements.  For `r ≤ m` its bases are the sets of
  `r` elements (`isBase_iff`), and the fundamental circuit of `e ∉ B` is `B + e`
  (`fundCircuit_eq`).
* `theta_le_iff`, `theta_eq` (Step 1): in `U_{r,m}`,
  `θ(B) = max(0, max_{f ∈ B} v_f - min_{e ∉ B} v_e)`.
* `U24 = unif 2 4` on `{a, b, c, d} = {0, 1, 2, 3}` with `v24 = (0, 1, 2, 3)`:
  `theta_values`: `θ` is `0, 1, 2, 2, 3, 3` on `ab, ac, ad, bc, bd, cd`;
  `pos_two`: `P_2 = {ab, ac, ad, bc}`;
  `pos_two_not_exchange` (Step 2): `ad`, `bc` and `a` violate the basis exchange axiom;
  `pos_two_not_matroid`: so `P_2` is not the set of bases of any matroid on `Fin 4`
  (`not_exists_matroid`).

The finite checks on `Fin 4` are kernel `decide` on statements about natural numbers.
-/

open Finset

namespace SignedTropical.Rainbow.NotMatroid

variable {r m : ℕ}

/-! ### Uniform matroids -/

/-- Augmentation for sets of at most `r` elements. -/
theorem ncard_augment {I J : Set (Fin m)} (hJ : J.ncard ≤ r) (hIJ : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ (insert e I).ncard ≤ r := by
  obtain ⟨e, heJ, heI⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hIJ
  exact ⟨e, heJ, heI, by rw [Set.ncard_insert_of_notMem heI]; omega⟩

variable (r m) in
/-- The uniform matroid `U_{r,m}` on `Fin m`: a set is independent if and only if it has at most
`r` elements. -/
def unif : Matroid (Fin m) :=
  (IndepMatroid.ofFinite Set.finite_univ (fun I => I.ncard ≤ r) (by simp)
    (fun _ _ hJ hIJ => (Set.ncard_le_ncard hIJ).trans hJ)
    (fun _ _ _ hJ hIJ => ncard_augment hJ hIJ) fun _ _ => Set.subset_univ _).matroid

@[simp] theorem unif_ground : (unif r m).E = Set.univ := rfl

@[simp] theorem unif_indep_iff {I : Set (Fin m)} : (unif r m).Indep I ↔ I.ncard ≤ r := Iff.rfl

/-- For `r ≤ m`, the bases of `U_{r,m}` are the sets of `r` elements. -/
theorem isBase_iff (hr : r ≤ m) {B : Finset (Fin m)} :
    (unif r m).IsBase (B : Set (Fin m)) ↔ #B = r := by
  refine ⟨fun hB => ?_, fun hB => ?_⟩
  · have h := unif_indep_iff.1 hB.indep
    rw [Set.ncard_coe_finset] at h
    refine le_antisymm h (not_lt.1 fun hlt => ?_)
    obtain ⟨e, -, heB⟩ := exists_mem_notMem_of_card_lt_card (s := B) (t := univ)
      (by rw [card_univ, Fintype.card_fin]; omega)
    refine (hB.insert_dep ⟨Set.mem_univ e, heB⟩).not_indep (unif_indep_iff.2 ?_)
    rw [Set.ncard_insert_of_notMem (s := (B : Set (Fin m))) heB, Set.ncard_coe_finset]
    omega
  · refine Matroid.Indep.isBase_of_forall_insert
      (unif_indep_iff.2 (by rw [Set.ncard_coe_finset, hB])) fun e he hI => ?_
    have h := unif_indep_iff.1 hI
    rw [Set.ncard_insert_of_notMem he.2, Set.ncard_coe_finset] at h
    omega

/-- In `U_{r,m}` the fundamental circuit of `e ∉ B` in a base `B` is `B + e`. -/
theorem fundCircuit_eq {B : Set (Fin m)} (hB : (unif r m).IsBase B) {e : Fin m} (he : e ∉ B) :
    (unif r m).fundCircuit e B = insert e B := by
  refine (Matroid.IsCircuit.eq_fundCircuit_of_subset ?_ hB.indep subset_rfl).symm
  refine Matroid.isCircuit_iff_forall_ssubset.2
    ⟨hB.insert_dep ⟨Set.mem_univ e, he⟩, fun I hI => unif_indep_iff.2 ?_⟩
  have h₁ := Set.ncard_lt_ncard hI
  have h₂ := unif_indep_iff.1 hB.indep
  rw [Set.ncard_insert_of_notMem he] at h₁
  omega

/-- Step 1 of Proposition `prop:notmatroid`, as a bound: in `U_{r,m}`, `θ(B) ≤ t` if and only if
`0 ≤ t` and `v_f - v_e ≤ t` for all `f ∈ B` and `e ∉ B`. -/
theorem theta_le_iff (v : Fin m → ℝ) {B : Finset (Fin m)}
    (hB : (unif r m).IsBase (B : Set (Fin m))) {t : ℝ} :
    theta (unif r m) v B ≤ t ↔ 0 ≤ t ∧ ∀ e ∉ B, ∀ f ∈ B, v f - v e ≤ t := by
  rw [theta, fold_max_le]
  simp only [mem_filter, mem_product, mem_univ, true_and, and_imp, Prod.forall]
  refine and_congr_right fun ht => ⟨fun h e he f hf => h e f he ?_, fun h e g he hg => ?_⟩
  · rw [fundCircuit_eq hB he]
    exact Set.mem_insert_of_mem e hf
  · rw [fundCircuit_eq hB he] at hg
    rcases hg with rfl | hg
    · rw [sub_self]
      exact ht
    · exact h e he g hg

/-- Step 1 of Proposition `prop:notmatroid`: in `U_{r,m}`, for a base `B` with `B ≠ ∅` and
`E \ B ≠ ∅`, `θ(B) = max(0, max_{f ∈ B} v_f - min_{e ∉ B} v_e)`. -/
theorem theta_eq (v : Fin m → ℝ) {B : Finset (Fin m)} (hB : (unif r m).IsBase (B : Set (Fin m)))
    (hne : B.Nonempty) (hne' : (univ \ B).Nonempty) :
    theta (unif r m) v B = max 0 (B.sup' hne v - (univ \ B).inf' hne' v) := by
  refine le_antisymm ((theta_le_iff v hB).2 ⟨le_max_left _ _, fun e he f hf => ?_⟩)
    (max_le ((theta_le_iff v hB).1 le_rfl).1 ?_)
  · exact (sub_le_sub (le_sup' v hf) (inf'_le v (mem_sdiff.2 ⟨mem_univ e, he⟩))).trans
      (le_max_right _ _)
  · obtain ⟨f, hf, hf'⟩ := exists_mem_eq_sup' hne v
    obtain ⟨e, he, he'⟩ := exists_mem_eq_inf' hne' v
    rw [hf', he']
    exact ((theta_le_iff v hB).1 le_rfl).2 e (mem_sdiff.1 he).2 f hf

/-! ### A family violating basis exchange is not a matroid -/

/-- A family of sets that violates the basis exchange axiom is not the set of bases of a
matroid. -/
theorem not_exists_matroid {P : Set (Finset (Fin m))}
    (h : ∃ B₁ ∈ P, ∃ B₂ ∈ P, ∃ e ∈ B₁ \ B₂, ∀ f ∈ B₂ \ B₁, insert f (B₁.erase e) ∉ P) :
    ¬∃ N : Matroid (Fin m), ∀ B : Finset (Fin m), N.IsBase (B : Set (Fin m)) ↔ B ∈ P := by
  rintro ⟨N, hN⟩
  obtain ⟨B₁, h₁, B₂, h₂, e, he, hf⟩ := h
  obtain ⟨f, hf', hB⟩ := ((hN B₁).2 h₁).exchange ((hN B₂).2 h₂)
    (by rwa [← coe_sdiff, mem_coe])
  refine hf f (by rwa [← mem_coe, coe_sdiff]) ((hN _).1 ?_)
  rwa [coe_insert, coe_erase]

/-! ### `U_{2,4}` with `v = (0, 1, 2, 3)` -/

/-- `U_{2,4}` on `{a, b, c, d} = {0, 1, 2, 3}`. -/
abbrev U24 : Matroid (Fin 4) := unif 2 4

/-- `v = (0, 1, 2, 3)`. -/
def v24 (i : Fin 4) : ℝ := (i : ℕ)

/-- `v24` is `(0, 1, 2, 3)` on `a, b, c, d`. -/
theorem v24_values : v24 0 = 0 ∧ v24 1 = 1 ∧ v24 2 = 2 ∧ v24 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [v24]

/-- The bases of `U_{2,4}` are the pairs. -/
theorem isBase_U24_iff {B : Finset (Fin 4)} : U24.IsBase (B : Set (Fin 4)) ↔ #B = 2 :=
  isBase_iff (by norm_num)

/-- `v_f - v_e ≤ c` read on natural numbers. -/
theorem v24_sub_le_iff (e f : Fin 4) (c : ℕ) : v24 f - v24 e ≤ c ↔ (f : ℕ) ≤ e + c := by
  rw [v24, v24, sub_le_iff_le_add', ← Nat.cast_add, Nat.cast_le]

/-- `θ(B) ≤ c` read on natural numbers. -/
theorem theta_U24_le_iff {B : Finset (Fin 4)} (hB : #B = 2) (c : ℕ) :
    theta U24 v24 B ≤ c ↔ ∀ e ∉ B, ∀ f ∈ B, (f : ℕ) ≤ e + c := by
  rw [theta_le_iff v24 (isBase_U24_iff.2 hB)]
  simp only [Nat.cast_nonneg, true_and, v24_sub_le_iff]

/-- `θ(B) = c` from an upper bound and an attained value, read on natural numbers. -/
theorem theta_U24_eq {B : Finset (Fin 4)} (hB : #B = 2) (c : ℕ)
    (hup : ∀ e ∉ B, ∀ f ∈ B, (f : ℕ) ≤ e + c)
    (hlow : c = 0 ∨ ∃ e ∉ B, ∃ f ∈ B, (f : ℕ) = e + c) : theta U24 v24 B = c := by
  refine le_antisymm ((theta_U24_le_iff hB c).2 hup) ?_
  have h := (theta_le_iff v24 (isBase_U24_iff.2 hB)).1 le_rfl
  rcases hlow with rfl | ⟨e, he, f, hf, hfe⟩
  · exact_mod_cast h.1
  · have h' := h.2 e he f hf
    simp only [v24, hfe, Nat.cast_add] at h'
    linarith

/-- Proposition `prop:notmatroid`, Step 1: with `a, b, c, d = 0, 1, 2, 3` and `v = (0, 1, 2, 3)`,
`θ` takes the values `0, 1, 2, 2, 3, 3` on `ab, ac, ad, bc, bd, cd`. -/
theorem theta_values :
    theta U24 v24 {0, 1} = 0 ∧ theta U24 v24 {0, 2} = 1 ∧ theta U24 v24 {0, 3} = 2 ∧
      theta U24 v24 {1, 2} = 2 ∧ theta U24 v24 {1, 3} = 3 ∧ theta U24 v24 {2, 3} = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast theta_U24_eq (by decide) 0 (by decide) (by decide)
  · exact_mod_cast theta_U24_eq (by decide) 1 (by decide) (by decide)
  · exact_mod_cast theta_U24_eq (by decide) 2 (by decide) (by decide)
  · exact_mod_cast theta_U24_eq (by decide) 2 (by decide) (by decide)
  · exact_mod_cast theta_U24_eq (by decide) 3 (by decide) (by decide)
  · exact_mod_cast theta_U24_eq (by decide) 3 (by decide) (by decide)

/-- `B ∈ P_2` read on natural numbers. -/
theorem mem_pos_two_iff {B : Finset (Fin 4)} :
    B ∈ Pos U24 v24 2 ↔ #B = 2 ∧ ∀ e ∉ B, ∀ f ∈ B, (f : ℕ) ≤ e + 2 := by
  rw [Pos, Set.mem_setOf_eq, isBase_U24_iff]
  exact and_congr_right fun hB => by exact_mod_cast theta_U24_le_iff hB 2

/-- Proposition `prop:notmatroid`: `P_2 = {ab, ac, ad, bc}`. -/
theorem pos_two : Pos U24 v24 2 = {{0, 1}, {0, 2}, {0, 3}, {1, 2}} := by
  ext B
  rw [mem_pos_two_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert B
  decide

/-- Proposition `prop:notmatroid`, Step 2: `P_2` violates the basis exchange axiom.  For
`B₁ = ad`, `B₂ = bc` and `e = a ∈ B₁ \ B₂`, neither `B₁ - a + b = bd` nor `B₁ - a + c = cd` lies
in `P_2`. -/
theorem pos_two_not_exchange : ∃ B₁ ∈ Pos U24 v24 2, ∃ B₂ ∈ Pos U24 v24 2, ∃ e ∈ B₁ \ B₂,
    ∀ f ∈ B₂ \ B₁, insert f (B₁.erase e) ∉ Pos U24 v24 2 := by
  simp only [pos_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨{0, 3}, by decide, {1, 2}, by decide, 0, by decide, by decide⟩

/-- Proposition `prop:notmatroid`: `P_2` is not the set of bases of any matroid on `Fin 4`. -/
theorem pos_two_not_matroid :
    ¬∃ N : Matroid (Fin 4), ∀ B : Finset (Fin 4), N.IsBase (B : Set (Fin 4)) ↔ B ∈ Pos U24 v24 2 :=
  not_exists_matroid pos_two_not_exchange

end SignedTropical.Rainbow.NotMatroid
