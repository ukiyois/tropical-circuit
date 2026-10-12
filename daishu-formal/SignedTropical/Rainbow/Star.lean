import SignedTropical.Classes.Graphic
import SignedTropical.Rainbow.MinBases
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Rainbow spanning trees contain assignment

`greedy_intersection.tex`, Proposition `prop:star`, on the multigraphs and cycle matroids of
`Classes/Graphic.lean`.

* `IsSpanningTree G T`: `T` contains no cycle and has one edge fewer than `G` has vertices.  A
  spanning tree is a base of the cycle matroid (`IsSpanningTree.isBase`), and when `G` is
  connected, that is of rank `|V| - 1`, the spanning trees are the bases
  (`isSpanningTree_iff_isBase`).
* `star rgt`: for the bipartite multigraph `H` on `L = R = Fin n` whose edge `e` joins `ℓ_{lft e}`
  and `ρ_{rgt e}`, the multigraph on `R ∪ {z}` whose edge `e` joins `z` and `ρ_{rgt e}`; the
  color of `e` is `lft e`.  Its cycles are the pairs of parallel edges (`isCycle_star_iff`).
* `isRainbowSpanningTree_star_iff` (Proposition `prop:star`): the rainbow spanning trees of the
  star are the perfect matchings of `H`.  Both are sets of edges of `H`, so the correspondence
  is the identity and keeps every weight.  `isRainbowBase_star_iff`: the same for the rainbow
  bases of the cycle matroid, with the colors as blocks, when every vertex of `R` has an edge.
* `sum_rainbowSpanningTree_star`, `rainbowTreePolynomial_eq_permanent` (Proposition
  `prop:star`): the rainbow spanning tree polynomial is the permanent of the biadjacency matrix
  with variable entries.
-/

open Finset SignedTropical.Classes.Graphic

namespace SignedTropical.Rainbow.Graphs

open SignedTropical.Rainbow

variable {n m : ℕ}

/-! ### Spanning trees -/

section SpanningTree

variable {G : Multigraph n m} {T : Finset (Fin m)}

variable (G) in
/-- `T` is a spanning tree of `G`: it contains no cycle and has one edge fewer than `G` has
vertices. -/
def IsSpanningTree (T : Finset (Fin m)) : Prop :=
  (∀ C, G.IsCycle C → ¬C ⊆ T) ∧ #T + 1 = n

/-- The spanning trees are the independent sets of the cycle matroid with `|V| - 1` edges. -/
theorem isSpanningTree_iff_indep :
    IsSpanningTree G T ↔ G.cycleMatroid.Indep (T : Set (Fin m)) ∧ #T + 1 = n := by
  rw [IsSpanningTree, Multigraph.indep_iff]

/-- A spanning tree is a base of the cycle matroid. -/
theorem IsSpanningTree.isBase (hT : IsSpanningTree G T) :
    G.cycleMatroid.IsBase (T : Set (Fin m)) := by
  obtain ⟨hI, hc⟩ := isSpanningTree_iff_indep.1 hT
  have hr := Multigraph.rank_le (G := G) (by omega)
  refine hI.isBase_of_eRk_ge (Set.toFinite _) ?_
  rw [hI.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, ← ENat.coe_toNat (eRank_ne_top _)]
  exact_mod_cast (show rank G.cycleMatroid ≤ #T by omega)

/-- A multigraph with a spanning tree has rank `|V| - 1`. -/
theorem IsSpanningTree.rank_eq (hT : IsSpanningTree G T) : rank G.cycleMatroid + 1 = n := by
  rw [← card_base _ hT.isBase, hT.2]

/-- In a connected multigraph, of rank `|V| - 1`, the spanning trees are the bases. -/
theorem isSpanningTree_iff_isBase (hG : rank G.cycleMatroid + 1 = n) :
    IsSpanningTree G T ↔ G.cycleMatroid.IsBase (T : Set (Fin m)) :=
  ⟨IsSpanningTree.isBase, fun hB =>
    isSpanningTree_iff_indep.2 ⟨hB.indep, by rw [card_base _ hB, hG]⟩⟩

/-- `Joins` is symmetric in the two ends. -/
theorem joins_comm {e : Fin m} {x y : Fin n} : G.Joins e x y ↔ G.Joins e y x :=
  or_comm

end SpanningTree

/-! ### Proposition `prop:star` -/

section Star

variable {lft rgt : Fin m → Fin n} {T : Finset (Fin m)}

/-- The star multigraph of Proposition `prop:star`, for the bipartite multigraph `H` on
`L = R = Fin n` whose edge `e` joins `ℓ_{lft e}` and `ρ_{rgt e}`: its vertices are `R ∪ {z}`,
with `ρ_j = j` and `z = n`, and its edge `e` joins `z` and `ρ_{rgt e}`.  The color of `e` is
`lft e`. -/
def star (rgt : Fin m → Fin n) : Multigraph (n + 1) m :=
  ⟨fun _ => Fin.last n, fun e => (rgt e).castSucc⟩

/-- An edge set of the star contains no cycle iff it has no two parallel edges. -/
theorem indep_star_iff : (star rgt).cycleMatroid.Indep (T : Set (Fin m)) ↔ Set.InjOn rgt ↑T := by
  rw [Multigraph.indep_iff_odd]
  constructor
  · intro h e he e' he' hee'
    by_contra hne
    obtain ⟨v, hv⟩ := h {e, e'} (by simp [insert_subset_iff, mem_coe.1 he, mem_coe.1 he'])
      (insert_nonempty _ _)
    have hinc : (star rgt).inc v e = (star rgt).inc v e' := by
      have ht : (star rgt).tgt e = (star rgt).tgt e' := congrArg Fin.castSucc hee'
      unfold Multigraph.inc
      rw [ht]
      rfl
    rw [Multigraph.deg, sum_pair hne, hinc] at hv
    exact hv ⟨_, rfl⟩
  · intro h S hS ⟨e, he⟩
    refine ⟨(rgt e).castSucc, ?_⟩
    rw [Multigraph.deg, sum_eq_single e (fun e' he' hne => ?_) (absurd he)]
    · simp [Multigraph.inc, star, (Fin.castSucc_ne_last _).symm]
    · have hne' : rgt e' ≠ rgt e := fun hr => hne (h (mem_coe.2 (hS he')) (mem_coe.2 (hS he)) hr)
      simp [Multigraph.inc, star, (Fin.castSucc_ne_last _).symm, hne']

/-- **The cycles of the star are the pairs of parallel edges.** -/
theorem isCycle_star_iff {C : Finset (Fin m)} :
    (star rgt).IsCycle C ↔ ∃ e e', e ≠ e' ∧ rgt e = rgt e' ∧ C = {e, e'} := by
  rw [← Multigraph.isCircuit_iff]
  constructor
  · intro hC
    have hdep := hC.not_indep
    rw [indep_star_iff] at hdep
    simp only [Set.InjOn, mem_coe, not_forall] at hdep
    obtain ⟨e, he, e', he', hee', hne⟩ := hdep
    have hdep' : ¬(star rgt).cycleMatroid.Indep ↑({e, e'} : Finset (Fin m)) := fun hi =>
      hne (indep_star_iff.1 hi (by simp) (by simp) hee')
    refine ⟨e, e', hne, hee', (coe_inj.1 (hC.eq_of_not_indep_subset hdep' ?_)).symm⟩
    simp [Set.insert_subset_iff, he, he']
  · rintro ⟨e, e', hne, hee', rfl⟩
    refine Matroid.isCircuit_iff_forall_ssubset.2
      ⟨⟨fun hi => hne (indep_star_iff.1 hi (by simp) (by simp) hee'), by simp⟩, fun I hI => ?_⟩
    obtain ⟨I, rfl⟩ := exists_finset I
    have hlt := card_lt_card (coe_ssubset.1 hI)
    rw [card_pair hne] at hlt
    exact indep_star_iff.2 fun a ha b hb _ => card_le_one.1 (by omega) a ha b hb

/-- `T` is a perfect matching of the bipartite multigraph whose edge `e` joins `ℓ_{lft e}` and
`ρ_{rgt e}`: every vertex of `L` and every vertex of `R` is an end of exactly one edge of `T`. -/
def IsPerfectMatching (lft rgt : Fin m → Fin n) (T : Finset (Fin m)) : Prop :=
  (∀ i, ∃! e, e ∈ T ∧ lft e = i) ∧ ∀ j, ∃! e, e ∈ T ∧ rgt e = j

/-- `T` meets every fibre of `f` exactly once iff `f` is injective on `T` and `#T = n`. -/
theorem forall_existsUnique_iff (f : Fin m → Fin n) :
    (∀ i, ∃! e, e ∈ T ∧ f e = i) ↔ Set.InjOn f ↑T ∧ #T = n := by
  constructor
  · intro h
    have hinj : Set.InjOn f ↑T := fun e he e' he' hee' => (h (f e')).unique ⟨he, hee'⟩ ⟨he', rfl⟩
    have himg : T.image f = univ := eq_univ_of_forall fun i => by
      obtain ⟨e, ⟨he, rfl⟩, -⟩ := h i
      exact mem_image_of_mem f he
    rw [← card_image_of_injOn hinj, himg, card_univ, Fintype.card_fin]
    exact ⟨hinj, rfl⟩
  · rintro ⟨hinj, hcard⟩ i
    have himg : T.image f = univ :=
      eq_univ_of_card _ (by rw [card_image_of_injOn hinj, hcard, Fintype.card_fin])
    obtain ⟨e, he, rfl⟩ := mem_image.1 (himg ▸ mem_univ i)
    exact ⟨e, ⟨he, rfl⟩, fun e' he' => hinj (mem_coe.2 he'.1) (mem_coe.2 he) he'.2⟩

/-- The spanning trees of the star are the sets of `n` edges with no two parallel edges. -/
theorem isSpanningTree_star_iff : IsSpanningTree (star rgt) T ↔ Set.InjOn rgt ↑T ∧ #T = n := by
  rw [isSpanningTree_iff_indep, indep_star_iff, add_left_inj]

/-- **Proposition `prop:star`, the trees.**  The rainbow spanning trees of the star of `H`,
colored by `lft`, are exactly the perfect matchings of `H`.  The correspondence is the identity
on sets of edges of `H`, so it keeps every weight. -/
theorem isRainbowSpanningTree_star_iff :
    IsSpanningTree (star rgt) T ∧ IsRainbow lft T ↔ IsPerfectMatching lft rgt T := by
  rw [isSpanningTree_star_iff, IsPerfectMatching, forall_existsUnique_iff, forall_existsUnique_iff,
    IsRainbow]
  tauto

/-- If every vertex of `R` has an edge, the star is connected: its rank is `n`. -/
theorem rank_star (hR : ∀ j, ∃ e, rgt e = j) : rank (star rgt).cycleMatroid = n := by
  choose g hg using hR
  have hinj : Function.Injective g := fun j j' h => by rw [← hg j, ← hg j', h]
  have hT : IsSpanningTree (star rgt) (univ.image g) := isSpanningTree_star_iff.2
    ⟨fun a ha b hb hab => by
      obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
      obtain ⟨j', -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
      rw [hg, hg] at hab
      rw [hab],
      by rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]⟩
  have := hT.rank_eq
  omega

/-- **Proposition `prop:star`, as rainbow bases.**  If every vertex of `R` has an edge, the
rainbow bases of the cycle matroid of the star, with the `n` colors as blocks (`n` is its rank),
are exactly the perfect matchings of `H`. -/
theorem isRainbowBase_star_iff (hR : ∀ j, ∃ e, rgt e = j) :
    IsRainbowBase (star rgt).cycleMatroid lft T ↔ IsPerfectMatching lft rgt T := by
  rw [← isRainbowSpanningTree_star_iff, IsRainbowBase,
    isSpanningTree_iff_isBase (by rw [rank_star hR])]

open Classical in
/-- **Proposition `prop:star`, the polynomial.**  For a bipartite multigraph `H` and edge values
`x e` in a commutative semiring, the sum over the rainbow spanning trees `T` of the star of
`∏_{e ∈ T} x_e` is the permanent of the matrix whose entry `(i, j)` is the sum of `x_e` over the
edges `e` joining `ℓ_i` and `ρ_j`. -/
theorem sum_rainbowSpanningTree_star {S : Type*} [CommSemiring S] (lft rgt : Fin m → Fin n)
    (x : Fin m → S) :
    ∑ T ∈ univ.filter (fun T => IsSpanningTree (star rgt) T ∧ IsRainbow lft T), ∏ e ∈ T, x e =
      (Matrix.of fun i j => ∑ e ∈ univ.filter (fun e => lft e = i ∧ rgt e = j), x e).permanent := by
  rw [filter_congr fun T _ => isRainbowSpanningTree_star_iff, Matrix.permanent]
  simp only [Matrix.of_apply, prod_univ_sum]
  rw [sum_sigma']
  symm
  -- a permutation `σ` and a choice `g j` of an edge from `ℓ_{σ j}` to `ρ_j` give the matching
  -- `{g j}`
  have hmem : ∀ (σ : Equiv.Perm (Fin n)) (g : Fin n → Fin m),
      g ∈ Fintype.piFinset (fun j => univ.filter fun e => lft e = σ j ∧ rgt e = j) ↔
        ∀ j, lft (g j) = σ j ∧ rgt (g j) = j := by
    simp
  refine sum_nbij (fun p => univ.image p.2) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
    (fun T hT => ?_) (fun p hp => ?_)
  · obtain ⟨σ, g⟩ := p
    have hg := (hmem σ g).1 (mem_sigma.1 hp).2
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun i => ⟨g (σ.symm i), ⟨mem_image_of_mem g (mem_univ _), by simp [hg]⟩, ?_⟩,
      fun j => ⟨g j, ⟨mem_image_of_mem g (mem_univ _), (hg j).2⟩, ?_⟩⟩
    · rintro _ ⟨he, rfl⟩
      obtain ⟨j, -, rfl⟩ := mem_image.1 he
      simp [hg]
    · rintro _ ⟨he, rfl⟩
      obtain ⟨j', -, rfl⟩ := mem_image.1 he
      rw [(hg j').2]
  · obtain ⟨σ, g⟩ := p
    obtain ⟨σ', g'⟩ := p'
    have hg := (hmem σ g).1 (mem_sigma.1 hp).2
    have hg' := (hmem σ' g').1 (mem_sigma.1 hp').2
    have h' : univ.image g = univ.image g' := h
    have hgg : g = g' := funext fun j => by
      obtain ⟨j', -, hj'⟩ := mem_image.1 (h' ▸ mem_image_of_mem g (mem_univ j))
      rw [← hj', show j = j' by rw [← (hg j).2, ← hj', (hg' j').2]]
    subst hgg
    have hσ : σ = σ' := Equiv.ext fun j => by rw [← (hg j).1, (hg' j).1]
    subst hσ
    rfl
  · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hT
    obtain ⟨hrow, hcol⟩ := hT
    choose g hg using fun j => (hcol j).exists
    have hinj : Function.Injective (lft ∘ g) := fun j j' h =>
      by rw [← (hg j).2, ← (hg j').2, (hrow _).unique ⟨(hg j).1, rfl⟩ ⟨(hg j').1, h.symm⟩]
    let σ := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    refine ⟨⟨σ, g⟩, mem_sigma.2 ⟨mem_univ _, (hmem σ g).2 fun j => ⟨rfl, (hg j).2⟩⟩, ?_⟩
    ext e
    simp only [mem_image, mem_univ, true_and]
    exact ⟨by rintro ⟨j, rfl⟩; exact (hg j).1,
      fun he => ⟨rgt e, (hcol _).unique ⟨(hg _).1, (hg _).2⟩ ⟨he, rfl⟩⟩⟩
  · obtain ⟨σ, g⟩ := p
    have hg := (hmem σ g).1 (mem_sigma.1 hp).2
    exact (prod_image fun j _ j' _ (h : g j = g j') => by rw [← (hg j).2, ← (hg j').2, h]).symm

/-- The edges of a bipartite graph `E ⊆ L × R` (`L = R = Fin n`), numbered by `Fin #E`. -/
noncomputable def bipEdge (E : Finset (Fin n × Fin n)) (e : Fin #E) : Fin n × Fin n :=
  E.equivFin.symm e

open Classical in
/-- **Proposition `prop:star`, the permanent.**  For a bipartite graph `E ⊆ L × R`, the rainbow
spanning tree polynomial of its star, the sum over the rainbow spanning trees `T` of
`∏_{ij ∈ T} x_{ij}`, is the permanent of the biadjacency matrix of `E` with the variable `x_{ij}`
at every edge `ij`. -/
theorem rainbowTreePolynomial_eq_permanent (R : Type*) [CommSemiring R]
    (E : Finset (Fin n × Fin n)) :
    ∑ T ∈ univ.filter (fun T => IsSpanningTree (star fun e => (bipEdge E e).2) T ∧
        IsRainbow (fun e => (bipEdge E e).1) T),
        ∏ e ∈ T, (MvPolynomial.X (bipEdge E e) : MvPolynomial (Fin n × Fin n) R) =
      (Matrix.of fun i j => if (i, j) ∈ E then MvPolynomial.X (i, j) else 0).permanent := by
  rw [sum_rainbowSpanningTree_star]
  refine congrArg Matrix.permanent (Matrix.ext fun i j => ?_)
  simp only [Matrix.of_apply]
  have hfilter : univ.filter (fun e => (bipEdge E e).1 = i ∧ (bipEdge E e).2 = j) =
      univ.filter (fun e => bipEdge E e = (i, j)) := by
    simp [Prod.ext_iff]
  rw [hfilter]
  split_ifs with hij
  · rw [sum_eq_single (E.equivFin ⟨(i, j), hij⟩)]
    · simp [bipEdge]
    · intro e he hne
      simp only [mem_filter, mem_univ, true_and] at he
      exact absurd (E.equivFin.symm_apply_eq.1 (Subtype.ext (by simpa [bipEdge] using he))) hne
    · simp [bipEdge]
  · refine sum_eq_zero fun e he => absurd ?_ hij
    simp only [mem_filter, mem_univ, true_and] at he
    exact he ▸ (E.equivFin.symm e).2

end Star

end SignedTropical.Rainbow.Graphs
