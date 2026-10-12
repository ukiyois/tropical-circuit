import SignedTropical.Rainbow.Connectivity

/-!
# Minimum bases

`greedy_intersection.tex`, Lemma `lem:minbases`(1)–(3) and equation `eq:rank-mu`, for the
definitions of `SignedTropical.Rainbow.Defs`, together with the basic API of those definitions.
Throughout, `M : Matroid (Fin m)` has ground set `univ` and `u : Fin m → ℝ`.

* Lemma `lem:minbases`(1), a base `B` is minimum iff `u_f ≤ u_e` whenever `e ∉ B` and
  `f ∈ C(B, e)`, is `Conn.isMinBase_iff_fundCircuit` (`Rainbow/Connectivity.lean`).
* `isMinBase_iff_forall_subset_closure` (Lemma `lem:minbases`(2)): a base `B` is minimum iff
  `B ∩ {u ≤ c}` spans `{u ≤ c}` for every `c`.
* `isBase_minBases_iff`, `IsMinBase.isMinBase_exchange_iff`, `IsMinBase.fundCircuit_minBases`
  (Lemma `lem:minbases`(3)): the bases of `M^u = minBases M u` are the minimum bases; for a
  minimum base `B`, `e ∉ B` and `f ∈ B`, `B - f + e` is minimum iff `f ∈ C(B, e)` and
  `u_f = u_e`; the fundamental circuit of `e` in `M^u` is `{e} ∪ {f ∈ C(B, e) : u_f = u_e}`.
* `rk_minBases` (equation `eq:rank-mu`):
  `r_{M^u}(A) = ∑_ℓ (r({u < ℓ} ∪ (A ∩ {u = ℓ})) - r({u < ℓ}))` over the values `ℓ` of `u`.

The proofs run through the pointwise condition `e ∈ cl(B ∩ {u ≤ u_e})` for every `e`.  A
minimum base satisfies it through its fundamental circuits (`IsMinBase.mem_closure`); a base
satisfying it is minimum, since then `C(B, e) ⊆ (B ∩ {u ≤ u_e}) + e`
(`isMinBase_of_forall_mem_closure`).  A base of `M^u` satisfies it by induction on the value
of `u`, and spans `M` with `r(M)` elements, so it is a base of `M`.

API for the other definitions: minimum bases exist (`exists_isMinBase`), `β_M(u)` is attained
exactly at them (`isMinBase_iff_sum_eq`), `β_M(u) = -h_M(-u)`
(`minBaseWeight_eq_neg_maxBasisWeight`); `M^u` depends only on the comparisons of `u` within
components (`minBases_congr`), hence only on the order of `u` (`minBases_congr_of_le_iff`), and
is `M` when `u` is constant on components (`minBases_eq_self`); a rainbow independent set of
size `ν` exists (`exists_isRainbowIndep_card_eq_nu`), `ν ≤ k` and `ν ≤ r`, `ν = r` iff a
rainbow base exists (`nu_eq_rank_iff`), a rainbow base of a matroid of rank `k` meets every
block exactly once (`IsRainbowBase.existsUnique`), and `Opt` is attained at a rainbow base
(`exists_isRainbowBase_sum_eq_Opt`).
-/

open Finset

namespace SignedTropical.Rainbow

variable {m k : ℕ} {M : Matroid (Fin m)} {u : Fin m → ℝ} {B : Finset (Fin m)}

/-! ### The least base weight -/

section Weight

variable (M u) in
/-- `β_M(u)` is the least base weight. -/
theorem isLeast_minBaseWeight : IsLeast (basisWeights M u) (minBaseWeight M u) :=
  ⟨(basisWeights_nonempty M u).csInf_mem (basisWeights_finite M u),
    fun _ hx => csInf_le (basisWeights_finite M u).bddBelow hx⟩

/-- `β_M(u) ≤ u(B)` for every base `B`. -/
theorem minBaseWeight_le (hB : M.IsBase (B : Set (Fin m))) : minBaseWeight M u ≤ ∑ e ∈ B, u e :=
  (isLeast_minBaseWeight M u).2 ⟨B, hB, rfl⟩

/-- The minimum bases are the bases at which `β_M(u)` is attained. -/
theorem isMinBase_iff_sum_eq :
    IsMinBase M u B ↔ M.IsBase (B : Set (Fin m)) ∧ ∑ e ∈ B, u e = minBaseWeight M u := by
  refine ⟨fun h => ⟨h.1, le_antisymm ?_ (minBaseWeight_le h.1)⟩,
    fun h => ⟨h.1, fun B' hB' => h.2 ▸ minBaseWeight_le hB'⟩⟩
  obtain ⟨⟨B₀, hB₀, hx⟩, -⟩ := isLeast_minBaseWeight M u
  exact hx ▸ h.2 B₀ hB₀

/-- A minimum base has weight `β_M(u)`. -/
theorem IsMinBase.sum_eq (h : IsMinBase M u B) : ∑ e ∈ B, u e = minBaseWeight M u :=
  (isMinBase_iff_sum_eq.1 h).2

variable (M u) in
/-- Minimum bases exist. -/
theorem exists_isMinBase : ∃ B, IsMinBase M u B := by
  obtain ⟨⟨B, hB, hx⟩, -⟩ := isLeast_minBaseWeight M u
  exact ⟨B, isMinBase_iff_sum_eq.2 ⟨hB, hx.symm⟩⟩

variable (M u) in
/-- `β_M(u) = -h_M(-u)`. -/
theorem minBaseWeight_eq_neg_maxBasisWeight : minBaseWeight M u = -maxBasisWeight M (-u) := by
  obtain ⟨⟨B, hB, hx⟩, hle⟩ := isLeast_minBaseWeight M u
  rw [maxBasisWeight_eq_of_isGreatest M (v := -minBaseWeight M u) ⟨⟨B, hB, by simp [hx]⟩, ?_⟩,
    neg_neg]
  rintro x ⟨B', hB', rfl⟩
  simpa using hle ⟨B', hB', rfl⟩

end Weight

/-! ### Single exchanges -/

section Exchange

/-- `u(B - f + e) = u(B) - u_f + u_e` for `e ∉ B` and `f ∈ B`. -/
theorem sum_exchange {e f : Fin m} (he : e ∉ B) (hf : f ∈ B) :
    ∑ x ∈ insert e (B.erase f), u x = ∑ x ∈ B, u x - u f + u e := by
  rw [sum_insert fun h => he (mem_of_mem_erase h), sum_erase_eq_sub hf]
  ring

/-- For a base `B`, `e ∉ B` and `f ∈ B`, the set `B - f + e` is a base iff `f ∈ C(B, e)`. -/
theorem isBase_exchange_iff {N : Matroid (Fin m)} (hE : N.E = Set.univ)
    (hB : N.IsBase (B : Set (Fin m))) {e f : Fin m} (he : e ∉ B) (hf : f ∈ B) :
    N.IsBase ↑(insert e (B.erase f)) ↔ f ∈ N.fundCircuit e ↑B := by
  have he' : e ∉ (B : Set (Fin m)) := by simpa using he
  rw [hB.indep.mem_fundCircuit_iff (by rw [hB.closure_eq, hE]; trivial) he',
    ← Set.insert_sdiff_singleton_comm (ne_of_mem_of_not_mem hf he).symm, coe_insert, coe_erase]
  exact ⟨Matroid.IsBase.indep, hB.exchange_isBase_of_indep he'⟩

end Exchange

/-! ### Lemma `lem:minbases`(2) and the pointwise condition -/

section Characterizations

/-- If `e` lies in the closure of `J ⊆ I`, then `C(I, e) ⊆ J + e`. -/
theorem fundCircuit_subset_insert_of_mem_closure {I J : Set (Fin m)} {e : Fin m} (hJI : J ⊆ I)
    (he : e ∈ M.closure J) : M.fundCircuit e I ⊆ insert e J := by
  rw [Matroid.fundCircuit_eq_sInter (M.closure_subset_closure hJI he)]
  exact Set.insert_subset_insert (Set.sInter_subset_of_mem ⟨hJI, he⟩)

/-- The pointwise condition `e ∈ cl(B ∩ {u ≤ u_e})` makes a base minimum: it puts `C(B, e)`
inside `(B ∩ {u ≤ u_e}) + e`, and Lemma `lem:minbases`(1) applies. -/
theorem isMinBase_of_forall_mem_closure (hB : M.IsBase (B : Set (Fin m)))
    (h : ∀ e, e ∈ M.closure (↑B ∩ {x | u x ≤ u e})) : IsMinBase M u B :=
  Conn.isMinBase_of_forall_fundCircuit hB fun e _ f hf => by
    obtain rfl | ⟨-, hfe⟩ := fundCircuit_subset_insert_of_mem_closure Set.inter_subset_left (h e) hf
    · exact le_rfl
    · exact hfe

/-- Condition (1) gives the pointwise condition `e ∈ cl(B ∩ {u ≤ u_e})`. -/
theorem mem_closure_of_forall_fundCircuit (hE : M.E = Set.univ) (hB : M.IsBase (B : Set (Fin m)))
    (h : ∀ e ∉ B, ∀ f ∈ M.fundCircuit e ↑B, u f ≤ u e) (e : Fin m) :
    e ∈ M.closure (↑B ∩ {x | u x ≤ u e}) := by
  by_cases he : e ∈ B
  · exact M.mem_closure_of_mem' ⟨by simpa using he, show u e ≤ u e from le_rfl⟩
      (by rw [hE]; trivial)
  have hC := hB.fundCircuit_isCircuit (by rw [hE]; trivial) (by simpa using he)
  refine M.closure_subset_closure ?_
    (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit e ↑B))
  rintro f ⟨hfC, hfe⟩
  have hfe' : f ≠ e := hfe
  exact ⟨by simpa [hfe'] using M.fundCircuit_subset_insert e ↑B hfC, h e he f hfC⟩

/-- A minimum base satisfies the pointwise condition `e ∈ cl(B ∩ {u ≤ u_e})`. -/
theorem IsMinBase.mem_closure (hE : M.E = Set.univ) (h : IsMinBase M u B) (e : Fin m) :
    e ∈ M.closure (↑B ∩ {x | u x ≤ u e}) :=
  mem_closure_of_forall_fundCircuit hE h.1 (fun _ he _ hf => Conn.le_of_mem_fundCircuit h he hf) e

/-- For a minimum base `B` and every `c`, `B ∩ {u ≤ c}` spans `{u ≤ c}`. -/
theorem IsMinBase.subset_closure_le (hE : M.E = Set.univ) (h : IsMinBase M u B) (c : ℝ) :
    {e | u e ≤ c} ⊆ M.closure (↑B ∩ {e | u e ≤ c}) := fun e (he : u e ≤ c) =>
  M.closure_subset_closure (Set.inter_subset_inter_right _ fun _ (hx : _ ≤ u e) => hx.trans he)
    (h.mem_closure hE e)

/-- **Lemma `lem:minbases`(2).**  A base `B` is minimum for `u` iff `B ∩ {u ≤ c}` spans
`{u ≤ c}` for every `c ∈ ℝ`. -/
theorem isMinBase_iff_forall_subset_closure (hE : M.E = Set.univ) :
    IsMinBase M u B ↔ M.IsBase (B : Set (Fin m)) ∧
      ∀ c : ℝ, {e | u e ≤ c} ⊆ M.closure (↑B ∩ {e | u e ≤ c}) :=
  ⟨fun h => ⟨h.1, h.subset_closure_le hE⟩, fun h => isMinBase_of_forall_mem_closure h.1
    fun e => h.2 (u e) (show e ∈ {x | u x ≤ u e} from le_refl (u e))⟩

/-- `B ∩ {u ≤ c}` is a basis of `{u ≤ c}`. -/
theorem IsMinBase.isBasis_le (hE : M.E = Set.univ) (h : IsMinBase M u B) (c : ℝ) :
    M.IsBasis (↑B ∩ {e | u e ≤ c}) {e | u e ≤ c} :=
  (h.1.indep.subset Set.inter_subset_left).isBasis_of_subset_of_subset_closure
    Set.inter_subset_right (h.subset_closure_le hE c)

/-- `B ∩ {u < c}` is a basis of `{u < c}`. -/
theorem IsMinBase.isBasis_lt (hE : M.E = Set.univ) (h : IsMinBase M u B) (c : ℝ) :
    M.IsBasis (↑B ∩ {e | u e < c}) {e | u e < c} :=
  (h.1.indep.subset Set.inter_subset_left).isBasis_of_subset_of_subset_closure
    Set.inter_subset_right fun e (he : u e < c) => M.closure_subset_closure
      (Set.inter_subset_inter_right _ fun _ (hx : _ ≤ u e) => hx.trans_lt he) (h.mem_closure hE e)

end Characterizations

/-! ### The level pieces -/

section LevelPiece

/-- `{u = ℓ} ∪ {u < ℓ} = {u ≤ ℓ}`. -/
theorem setOf_eq_union_lt (u : Fin m → ℝ) (ℓ : ℝ) :
    {e | u e = ℓ} ∪ {e | u e < ℓ} = {e | u e ≤ ℓ} := by
  ext e
  simp [le_iff_eq_or_lt]

/-- The bases in a level piece.  For `X ⊆ {u = ℓ}`, `I ⊆ X` and a basis `J` of `{u < ℓ}`, the
set `I` is a basis of `X` in `(M ↾ {u ≤ ℓ}) ／ {u < ℓ}` iff `I ∪ J` is a basis of
`X ∪ {u < ℓ}` in `M`. -/
theorem levelPiece_isBasis_iff (hE : M.E = Set.univ) {ℓ : ℝ} {I X J : Set (Fin m)}
    (hX : X ⊆ {e | u e = ℓ}) (hIX : I ⊆ X) (hJ : M.IsBasis J {e | u e < ℓ}) :
    (levelPiece M u ℓ).IsBasis I X ↔ M.IsBasis (I ∪ J) (X ∪ {e | u e < ℓ}) := by
  have hCR : {e | u e < ℓ} ⊆ {e | u e ≤ ℓ} := fun e (he : u e < ℓ) => he.le
  have hXR : X ⊆ {e | u e ≤ ℓ} := fun e he => le_of_eq (hX he)
  have hXC : ∀ e ∈ X, ¬u e < ℓ := fun e he h => h.ne (hX he)
  rw [levelPiece, Matroid.isBasis_iff_indep_subset_closure,
    (hJ.isBasis_restrict_of_subset hCR).contract_indep_iff, Matroid.contract_closure_eq,
    Matroid.restrict_closure_eq _ (Set.union_subset (hIX.trans hXR) hCR)
      (by rw [hE]; exact Set.subset_univ _), Matroid.restrict_indep_iff,
    M.closure_union_congr_right hJ.closure_eq_closure.symm]
  refine ⟨fun ⟨⟨⟨hind, _⟩, _⟩, _, hXcl⟩ => hind.isBasis_of_subset_of_subset_closure
    (Set.union_subset_union hIX hJ.subset) (Set.union_subset (fun e he => (hXcl he).1.1)
      (hJ.subset_closure.trans (M.closure_subset_closure Set.subset_union_right))), fun h => ?_⟩
  exact ⟨⟨⟨h.indep, Set.union_subset (hIX.trans hXR) (hJ.subset.trans hCR)⟩,
    Set.disjoint_left.2 fun e he he' => hXC e (hIX he') he⟩, hIX,
    fun e he => ⟨⟨h.subset_closure (Set.mem_union_left _ he), hXR he⟩, hXC e he⟩⟩

/-- For `K ⊆ {u = ℓ}` and a basis `J` of `{u < ℓ}`, the set `K` is a base of the level piece
iff `K ∪ J` is a basis of `{u ≤ ℓ}`. -/
theorem levelPiece_isBase_iff (hE : M.E = Set.univ) {ℓ : ℝ} {K J : Set (Fin m)}
    (hK : K ⊆ {e | u e = ℓ}) (hJ : M.IsBasis J {e | u e < ℓ}) :
    (levelPiece M u ℓ).IsBase K ↔ M.IsBasis (K ∪ J) {e | u e ≤ ℓ} := by
  rw [← Matroid.isBasis_ground_iff, levelPiece_ground,
    levelPiece_isBasis_iff hE subset_rfl hK hJ, setOf_eq_union_lt]

end LevelPiece

/-! ### Lemma `lem:minbases`(3): the matroid `M^u` -/

section MinBases

/-- A base of `M^u` is a set meeting every level set `{u = ℓ}` in a base of the level
piece. -/
theorem isBase_minBases_iff_levelPiece {X : Set (Fin m)} :
    (minBases M u).IsBase X ↔ ∀ ℓ, (levelPiece M u ℓ).IsBase (X ∩ {e | u e = ℓ}) := by
  simp only [minBases, Matroid.disjointSigma_isBase_iff, levelPiece_ground]
  exact and_iff_left fun e _ => Set.mem_iUnion.2 ⟨u e, rfl⟩

/-- A minimum base is a base of `M^u`. -/
theorem IsMinBase.isBase_minBases (hE : M.E = Set.univ) (h : IsMinBase M u B) :
    (minBases M u).IsBase ↑B :=
  isBase_minBases_iff_levelPiece.2 fun ℓ => by
    rw [levelPiece_isBase_iff hE Set.inter_subset_right (h.isBasis_lt hE ℓ),
      ← Set.inter_union_distrib_left, setOf_eq_union_lt]
    exact h.isBasis_le hE ℓ

/-- A base of `M^u` is a minimum base.  Step 1: `e ∈ cl(B ∩ {u ≤ u_e})` for every `e`, by
induction on the number of elements of smaller value.  Step 2: so `B` spans `M`; it has as
many elements as a minimum base, so it is a base of `M`. -/
theorem isMinBase_of_isBase_minBases (hE : M.E = Set.univ) (h : (minBases M u).IsBase ↑B) :
    IsMinBase M u B := by
  have hpiece := isBase_minBases_iff_levelPiece.1 h
  have hcl : ∀ n e, #(univ.filter fun x => u x < u e) = n →
      e ∈ M.closure (↑B ∩ {x | u x ≤ u e}) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro e rfl
      obtain ⟨J, hJ⟩ := M.exists_isBasis {x | u x < u e} (by rw [hE]; exact Set.subset_univ _)
      have hbasis := (levelPiece_isBase_iff hE Set.inter_subset_right hJ).1 (hpiece (u e))
      refine M.closure_subset_closure_of_subset_closure (Set.union_subset ?_ ?_)
        (hbasis.subset_closure (show u e ≤ u e from le_rfl))
      · exact fun x ⟨hxB, hx⟩ =>
          M.mem_closure_of_mem' ⟨hxB, le_of_eq hx⟩ (by rw [hE]; trivial)
      · intro x hxJ
        have hx : u x < u e := hJ.subset hxJ
        refine M.closure_subset_closure
          (Set.inter_subset_inter_right _ fun y (hy : u y ≤ u x) => hy.trans hx.le)
          (ih _ (card_lt_card ((ssubset_iff_of_subset fun y => ?_).2 ⟨x, ?_, ?_⟩)) x rfl)
        · simpa using fun hy : u y < u x => hy.trans hx
        · simpa using hx
        · simp
  have hcl' : ∀ e, e ∈ M.closure (↑B ∩ {x | u x ≤ u e}) := fun e => hcl _ e rfl
  obtain ⟨B₀, hB₀⟩ := exists_isMinBase M u
  have hspan : M.Spanning ↑B := by
    rw [Matroid.spanning_iff_ground_subset_closure (by rw [hE]; exact Set.subset_univ _), hE]
    exact fun e _ => M.closure_subset_closure Set.inter_subset_left (hcl' e)
  obtain ⟨B₁, hB₁, hB₁B⟩ := hspan.exists_isBase_subset
  have hBeq : B₁ = ↑B := (Set.toFinite B₁).eq_of_subset_of_encard_le hB₁B
    ((h.encard_eq_encard_of_isBase (hB₀.isBase_minBases hE)).trans
      (hB₀.1.encard_eq_encard_of_isBase hB₁)).le
  exact isMinBase_of_forall_mem_closure (hBeq ▸ hB₁) hcl'

/-- **Lemma `lem:minbases`(3).**  The minimum bases of `u` are the bases of the matroid
`M^u = minBases M u`, whose ground set is `univ` (`Conn.minBases_ground`). -/
theorem isBase_minBases_iff (hE : M.E = Set.univ) :
    (minBases M u).IsBase ↑B ↔ IsMinBase M u B :=
  ⟨isMinBase_of_isBase_minBases hE, fun h => h.isBase_minBases hE⟩

/-- **Lemma `lem:minbases`(3), exchanges.**  For a minimum base `B`, `e ∉ B` and `f ∈ B`, the
set `B - f + e` is a minimum base iff `f ∈ C(B, e)` and `u_f = u_e`. -/
theorem IsMinBase.isMinBase_exchange_iff (hE : M.E = Set.univ) (hB : IsMinBase M u B)
    {e f : Fin m} (he : e ∉ B) (hf : f ∈ B) :
    IsMinBase M u (insert e (B.erase f)) ↔ f ∈ M.fundCircuit e ↑B ∧ u f = u e := by
  have hw := sum_exchange (u := u) he hf
  refine ⟨fun h => ⟨(isBase_exchange_iff hE hB.1 he hf).1 h.1, ?_⟩, fun ⟨hC, hfe⟩ =>
    ⟨(isBase_exchange_iff hE hB.1 he hf).2 hC, fun B' hB' => ?_⟩⟩
  · have h1 := h.2 B hB.1
    have h2 := hB.2 _ h.1
    linarith
  · rw [hw, hfe, sub_add_cancel]
    exact hB.2 B' hB'

/-- **Lemma `lem:minbases`(3), circuits.**  For a minimum base `B` and `e ∉ B`, the
fundamental circuit of `e` in `M^u`, the circuit in `B + e`, is
`{e} ∪ {f ∈ C(B, e) : u_f = u_e}`. -/
theorem IsMinBase.fundCircuit_minBases (hE : M.E = Set.univ) (hB : IsMinBase M u B)
    {e : Fin m} (he : e ∉ B) :
    (minBases M u).fundCircuit e ↑B = insert e {f | f ∈ M.fundCircuit e ↑B ∧ u f = u e} := by
  ext x
  obtain rfl | hxe := eq_or_ne x e
  · simp [Matroid.mem_fundCircuit]
  by_cases hxB : x ∈ B
  · rw [Set.mem_insert_iff, or_iff_right hxe, Set.mem_setOf_eq,
      ← isBase_exchange_iff (Conn.minBases_ground M u) (hB.isBase_minBases hE) he hxB,
      isBase_minBases_iff hE, hB.isMinBase_exchange_iff hE he hxB]
  refine iff_of_false (fun hx => ?_) fun hx => ?_
  · simpa [hxe, hxB] using (minBases M u).fundCircuit_subset_insert e ↑B hx
  · obtain ⟨hxC, -⟩ : x ∈ M.fundCircuit e ↑B ∧ u x = u e := by simpa [hxe] using hx
    simpa [hxe, hxB] using M.fundCircuit_subset_insert e ↑B hxC

/-- The set `{e} ∪ {f ∈ C(B, e) : u_f = u_e}` is a circuit of `M^u`. -/
theorem IsMinBase.isCircuit_minBases (hE : M.E = Set.univ) (hB : IsMinBase M u B)
    {e : Fin m} (he : e ∉ B) :
    (minBases M u).IsCircuit (insert e {f | f ∈ M.fundCircuit e ↑B ∧ u f = u e}) :=
  hB.fundCircuit_minBases hE he ▸ (hB.isBase_minBases hE).fundCircuit_isCircuit
    (by rw [Conn.minBases_ground]; trivial) (by simpa using he)

/-- A base of `M^u` is a base of `M`. -/
theorem isBase_of_isBase_minBases (hE : M.E = Set.univ) (h : (minBases M u).IsBase ↑B) :
    M.IsBase (B : Set (Fin m)) :=
  ((isBase_minBases_iff hE).1 h).1

/-- A base of `M^u` has `r(M)` elements. -/
theorem card_of_isBase_minBases (hE : M.E = Set.univ) (h : (minBases M u).IsBase ↑B) :
    #B = rank M :=
  card_base M (isBase_of_isBase_minBases hE h)

/-- `M^u` has the rank of `M`. -/
theorem rank_minBases (hE : M.E = Set.univ) (u : Fin m → ℝ) : rank (minBases M u) = rank M := by
  obtain ⟨B, hB⟩ := exists_isMinBase M u
  rw [← card_base _ (hB.isBase_minBases hE), card_base M hB.1]

/-- `M^u` depends only on the comparisons of `u` within components: if `u_e ≤ u_f ↔ u'_e ≤ u'_f`
whenever `e` and `f` lie in one component, then `M^u = M^{u'}`, by Lemma `lem:minbases`(3) and
`Conn.isMinBase_congr`. -/
theorem minBases_congr (hE : M.E = Set.univ) {u' : Fin m → ℝ}
    (h : ∀ e f, connRel M e f → (u e ≤ u f ↔ u' e ≤ u' f)) : minBases M u = minBases M u' := by
  refine Matroid.ext_isBase (by rw [Conn.minBases_ground, Conn.minBases_ground]) fun B _ => ?_
  obtain ⟨B, rfl⟩ := exists_finset B
  rw [isBase_minBases_iff hE, isBase_minBases_iff hE, Conn.isMinBase_congr h]

/-- `M^u` depends only on the order of `u`. -/
theorem minBases_congr_of_le_iff (hE : M.E = Set.univ) {u' : Fin m → ℝ}
    (h : ∀ e f, u e ≤ u f ↔ u' e ≤ u' f) : minBases M u = minBases M u' :=
  minBases_congr hE fun e f _ => h e f

/-- If `u` is constant on every component, then `M^u = M`, by Lemma `lem:minbases`(3) and
`Conn.isMinBase_iff_isBase`. -/
theorem minBases_eq_self (hE : M.E = Set.univ) (h : ∀ e f, connRel M e f → u e = u f) :
    minBases M u = M := by
  refine Matroid.ext_isBase (by rw [Conn.minBases_ground, hE]) fun B _ => ?_
  obtain ⟨B, rfl⟩ := exists_finset B
  rw [isBase_minBases_iff hE, Conn.isMinBase_iff_isBase h]

/-- For constant `u`, `M^u = M`: the bases of `M^u` are the bases of `M`. -/
theorem minBases_eq_self_of_forall_eq (hE : M.E = Set.univ) (h : ∀ e f, u e = u f) :
    minBases M u = M :=
  minBases_eq_self hE fun e f _ => h e f

end MinBases

/-! ### Equation `eq:rank-mu` -/

/-- **Equation `eq:rank-mu`.**  The rank of `A` in `M^u` is
`∑_ℓ (r({u < ℓ} ∪ (A ∩ {u = ℓ})) - r({u < ℓ}))` over the values `ℓ` of `u`.  Each difference
is a difference of natural numbers with the subtrahend at most the minuend, the rank being
monotone, so no truncation occurs. -/
theorem rk_minBases (hE : M.E = Set.univ) (u : Fin m → ℝ) (A : Finset (Fin m)) :
    rk (minBases M u) A = ∑ ℓ ∈ univ.image u,
      (rk M (univ.filter (fun e => u e < ℓ) ∪ A.filter (fun e => u e = ℓ)) -
        rk M (univ.filter fun e => u e < ℓ)) := by
  obtain ⟨I, hI⟩ := (minBases M u).exists_isBasis (A : Set (Fin m)) (by simp [Conn.minBases_ground])
  obtain ⟨I, rfl⟩ := exists_finset I
  rw [← card_eq_rk _ hI, card_eq_sum_card_fiberwise fun e _ => mem_image_of_mem u (mem_univ e)]
  refine sum_congr rfl fun ℓ _ => ?_
  obtain ⟨J, hJ⟩ := M.exists_isBasis {e | u e < ℓ} (by rw [hE]; exact Set.subset_univ _)
  obtain ⟨J, rfl⟩ := exists_finset J
  have hIℓ : (levelPiece M u ℓ).IsBasis (↑I ∩ {e | u e = ℓ}) (↑A ∩ {e | u e = ℓ}) := by
    simpa [levelPiece_ground] using (Matroid.disjointSigma_isBasis_iff.1 hI).1 ℓ
  have h := (levelPiece_isBasis_iff hE Set.inter_subset_right
    (Set.inter_subset_inter_left _ hI.subset) hJ).1 hIℓ
  have hb : M.IsBasis ↑((I.filter fun e => u e = ℓ) ∪ J)
      ↑(univ.filter (fun e => u e < ℓ) ∪ A.filter (fun e => u e = ℓ)) := by
    convert h using 1 <;> ext x <;> simp [or_comm]
  have hJ' : M.IsBasis ↑J ↑(univ.filter fun e => u e < ℓ) := by
    convert hJ using 1; ext x; simp
  rw [← card_eq_rk M hb, ← card_eq_rk M hJ', card_union_of_disjoint, Nat.add_sub_cancel]
  exact disjoint_left.2 fun e he he' =>
    (show u e < ℓ from hJ.subset (mem_coe.2 he')).ne (mem_filter.1 he).2

/-! ### Rainbow sets, `ν`, `Av` and `Opt` -/

section Rainbow

variable {N : Matroid (Fin m)} {blk : Fin m → Fin k} {I S : Finset (Fin m)}

/-- `e ∈ E_Q` iff the block of `e` is in `Q`. -/
@[simp] theorem mem_blockSet {Q : Finset (Fin k)} {e : Fin m} :
    e ∈ blockSet blk Q ↔ blk e ∈ Q := by
  simp [blockSet]

/-- `S` meets the block `b` iff some element of `S` lies in `b`. -/
@[simp] theorem mem_blocksMet {b : Fin k} : b ∈ blocksMet blk S ↔ ∃ e ∈ S, blk e = b := by
  simp [blocksMet]

/-- A subset of a rainbow set is rainbow. -/
theorem IsRainbow.subset (h : IsRainbow blk S) (hIS : I ⊆ S) : IsRainbow blk I :=
  Set.InjOn.mono (coe_subset.2 hIS) h

/-- A rainbow set meets as many blocks as it has elements. -/
theorem IsRainbow.card_blocksMet (h : IsRainbow blk S) : #(blocksMet blk S) = #S :=
  card_image_of_injOn h

/-- A subset of a rainbow independent set is rainbow independent. -/
theorem IsRainbowIndep.subset (h : IsRainbowIndep N blk S) (hIS : I ⊆ S) :
    IsRainbowIndep N blk I :=
  ⟨h.1.subset (coe_subset.2 hIS), h.2.subset hIS⟩

/-- A rainbow independent set has at most `ν(N)` elements. -/
theorem IsRainbowIndep.card_le_nu (h : IsRainbowIndep N blk I) : #I ≤ nu N blk := by
  classical
  exact le_sup (f := card) (mem_filter.2 ⟨mem_univ I, h⟩)

variable (N blk) in
/-- A rainbow independent set of size `ν(N)` exists. -/
theorem exists_isRainbowIndep_card_eq_nu : ∃ I, IsRainbowIndep N blk I ∧ #I = nu N blk := by
  classical
  obtain ⟨I, hI, hsup⟩ := exists_mem_eq_sup (univ.filter (IsRainbowIndep N blk))
    ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [IsRainbowIndep, IsRainbow]⟩⟩ card
  exact ⟨I, (mem_filter.1 hI).2, hsup.symm⟩

variable (N blk) in
/-- `ν(N) ≤ k`. -/
theorem nu_le : nu N blk ≤ k := by
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu N blk
  rw [← hcard, ← hI.2.card_blocksMet]
  simpa using card_le_univ (blocksMet blk I)

variable (N blk) in
/-- `ν(N) ≤ r(N)`. -/
theorem nu_le_rank : nu N blk ≤ rank N := by
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu N blk
  exact hcard ▸ (card_le_rk N hI.1 (subset_univ I)).trans (rk_le_rank N univ)

/-- An independent set meets at most `ν(N)` blocks: one element from each block it meets
gives a rainbow independent set. -/
theorem card_blocksMet_le_nu (hI : N.Indep (I : Set (Fin m))) : #(blocksMet blk I) ≤ nu N blk := by
  obtain ⟨J, hJI, hJ, himg⟩ := exists_subset_injOn_image_eq_of_surjOn (f := blk) (I : Set (Fin m))
    (blocksMet blk I) (by rw [blocksMet, coe_image]; exact Set.surjOn_image blk _)
  rw [← himg, card_image_of_injOn hJ]
  exact IsRainbowIndep.card_le_nu ⟨hI.subset hJI, hJ⟩

/-- If every base of `N` is a base of `N'`, as in (F2), then `ν(N) ≤ ν(N')`. -/
theorem nu_mono {N' : Matroid (Fin m)}
    (h : ∀ B : Finset (Fin m), N.IsBase (B : Set (Fin m)) → N'.IsBase (B : Set (Fin m))) :
    nu N blk ≤ nu N' blk := by
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu N blk
  obtain ⟨B, hB, hIB⟩ := hI.1.exists_isBase_superset
  obtain ⟨B, rfl⟩ := exists_finset B
  exact hcard ▸ IsRainbowIndep.card_le_nu ⟨(h B hB).indep.subset hIB, hI.2⟩

/-- `Av(N)` unfolded: `b` is avoidable iff some rainbow independent set of size `ν(N)` misses
the block `b`. -/
theorem mem_Av {b : Fin k} :
    b ∈ Av N blk ↔ ∃ I, IsRainbowIndep N blk I ∧ #I = nu N blk ∧ b ∉ blocksMet blk I := by
  unfold Av
  simp only [mem_filter, mem_univ, true_and]

/-- A rainbow base of a matroid of rank `k` meets every block. -/
theorem IsRainbowBase.blocksMet_eq_univ (hk : rank N = k) (h : IsRainbowBase N blk B) :
    blocksMet blk B = univ :=
  eq_univ_of_card _ (by rw [h.2.card_blocksMet, card_base N h.1, hk, Fintype.card_fin])

/-- A rainbow base of a matroid of rank `k` meets every block exactly once. -/
theorem IsRainbowBase.existsUnique (hk : rank N = k) (h : IsRainbowBase N blk B) (b : Fin k) :
    ∃! e, e ∈ B ∧ blk e = b := by
  obtain ⟨e, he, rfl⟩ := mem_blocksMet.1 (h.blocksMet_eq_univ hk ▸ mem_univ b)
  exact ⟨e, ⟨he, rfl⟩, fun f hf => h.2 (mem_coe.2 hf.1) (mem_coe.2 he) hf.2⟩

/-- Summing over a rainbow base of a matroid of rank `k` sums over the blocks. -/
theorem IsRainbowBase.sum_comp_blk (hk : rank N = k) (h : IsRainbowBase N blk B) {β : Type*}
    [AddCommMonoid β] (p : Fin k → β) : ∑ e ∈ B, p (blk e) = ∑ b, p b := by
  rw [← h.blocksMet_eq_univ hk, blocksMet, sum_image h.2]

/-- `ν(N) = r(N)` iff `N` has a rainbow base. -/
theorem nu_eq_rank_iff : nu N blk = rank N ↔ ∃ B, IsRainbowBase N blk B := by
  refine ⟨fun h => ?_, fun ⟨B, hB⟩ => le_antisymm (nu_le_rank N blk)
    (card_base N hB.1 ▸ IsRainbowIndep.card_le_nu ⟨hB.1.indep, hB.2⟩)⟩
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu N blk
  refine ⟨I, hI.1.isBase_of_eRk_ge (Set.toFinite _) ?_, hI.2⟩
  rw [hI.1.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, h, rank,
    ENat.coe_toNat (eRank_ne_top N)]

/-- For a matroid of rank `k`, `ν(N) = k` iff `N` has a rainbow base. -/
theorem nu_eq_iff (hk : rank N = k) : nu N blk = k ↔ ∃ B, IsRainbowBase N blk B := by
  rw [← nu_eq_rank_iff, hk]

variable (N blk) in
/-- The weights of the rainbow bases form a finite set. -/
theorem finite_rainbowBaseWeights (w : Fin m → ℝ) :
    {x | ∃ B, IsRainbowBase N blk B ∧ x = ∑ e ∈ B, w e}.Finite :=
  (Set.finite_range fun B : Finset (Fin m) => ∑ e ∈ B, w e).subset
    fun _ ⟨B, _, hx⟩ => ⟨B, hx.symm⟩

variable {w : Fin m → ℝ}

/-- `Opt(w)` is at most the weight of every rainbow base. -/
theorem Opt_le (h : IsRainbowBase N blk B) : Opt N blk w ≤ ∑ e ∈ B, w e :=
  csInf_le (finite_rainbowBaseWeights N blk w).bddBelow ⟨B, h, rfl⟩

/-- If a rainbow base exists, `Opt(w)` is the weight of a rainbow base. -/
theorem exists_isRainbowBase_sum_eq_Opt (h : ∃ B, IsRainbowBase N blk B) :
    ∃ B, IsRainbowBase N blk B ∧ ∑ e ∈ B, w e = Opt N blk w := by
  obtain ⟨B, hB⟩ := h
  have hne : {x | ∃ B, IsRainbowBase N blk B ∧ x = ∑ e ∈ B, w e}.Nonempty := ⟨_, B, hB, rfl⟩
  obtain ⟨B', hB', hx⟩ := hne.csInf_mem (finite_rainbowBaseWeights N blk w)
  exact ⟨B', hB', hx.symm⟩

end Rainbow

end SignedTropical.Rainbow
