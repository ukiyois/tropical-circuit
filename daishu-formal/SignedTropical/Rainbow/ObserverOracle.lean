import SignedTropical.Rainbow.POSLRank
import SignedTropical.Rainbow.MICircuit
import SignedTropical.BoolAlg.Rel

/-!
# The observer, Steps 1 to 3: exchange tests for `N_G`

`greedy_intersection.tex`, Lemma `lem:observer`, Steps 1 to 3.  A Boolean circuit reads a
relation `G ⊆ E × E` (`relR m`, entry `(g, f)` the bit `[(g, f) ∈ G]`, `relBits`) and computes once
a *context* (`Ctx`, `ctxR`), from which a second circuit for each `y`, the *exchange test* of `y`,
decides independence in `N_G` of the sets `A ∋ y` with `A - y` independent, the only sets on which
the matroid intersection circuit (`Rainbow/MICircuit.lean`) uses the test of `y`.  The rank
circuit of `M` (size `s`, the hypothesis of Theorem `thm:A`) is run on computed wires (`runB`,
`rankB`).

**The context** (`ctxB`, `ctxB_impl`, `ctxCost m s = 2m³ + 8m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1`
gates), with its value `ctxV`:

* Step 1 (`poB`): `f ∈ PO_G` iff `r({g : (g, f) ∉ G}) < r({g : (g, f) ∉ G} + f)` (`poV_relBits`),
  two rank runs and a comparison for each `f`;
* Step 2: the links `(x, y), (y, x) ∈ G` for `x, y ∈ PO_G` in one component (`linksB`; the
  components are fixed, so this choice costs no gate), Warshall's algorithm for the clusters
  (`clB`, `clV_relBits`), and the order bits `ordV` (`ordB`), which at `G = G_t`, `t ≥ 0`, are
  `[u_G(x) < u_G(y)]` within components (`ordP_iff`);
* Step 3, the part independent of the set: the ranks `r(Below(y))` (`rkbB`), where `Below(y)` is
  the set of elements below `y` in the order (`belowP`, equal to `Below_G(x)` of `rk_NG` for the
  representative `x` of the cluster of `y`, `belowP_eq_of_mem_clusterG`, `belowP_eq_belowG`).

For every relation `G`, the context computed from `G` is `ctxOf M G` (`ctxV_relBits`), whose
fields are the sets above, read from `G`.

**The exchange test of `y`** (Step 3; `locB`, `locB_impl`,
`locCost m s = s + 2m + 18⌈log₂(m+1)⌉ + popCost m + 3 ≤ s + 42(m + 1)` gates per test):
`[y ∈ PO]` and `r(Below(y) ∪ (A ∩ Lev(y))) - r(Below(y)) = |A ∩ Lev(y)|`, with `Lev(y)` the
cluster of `y` (`locV`), one rank run.  By the rank formula `rk_NG`, `r_{N_G}(A)` is the sum of
these terms over the representatives `x` of the clusters, each term is at most `|A ∩ Lev(x)|`
(`rk_union_le_add_card`), and the clusters partition `PO_G` (`clusterG_eq`, `eq_of_mem_clusterG`,
`exists_repsG`, `sum_card_inter_clusterG_le`).  So `A` is independent iff `A ⊆ PO_G` and every
term is tight, and when `A - y` is independent only the term of the cluster of `y` can fail:
the test answers every exchange question of `N_{G_t}` at the context of `G_t`, `t ≥ 0`
(`locV_exchOracle`, `locV_correct`).  `lem_observer_oracle` collects the two implementations,
their sizes and the correctness.
-/

open Finset

namespace SignedTropical.Rainbow.Observer

open SignedTropical SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.POSL

variable {m n : ℕ} {M : Matroid (Fin m)}

/-! ### The context of a relation -/

/-- The bits of a relation `G ⊆ E × E`: entry `(g, f)` is `[(g, f) ∈ G]`. -/
def relBits (G : Finset (Fin m × Fin m)) : Fin m → Fin m → Bool := fun g f => decide ((g, f) ∈ G)

/-- The order of Step 2 read from `G`: `x`, `y` lie in one component, `x ∈ PO_G`, and `y ∉ PO_G`
or `x`, `y` lie in different clusters with `(x, y) ∉ G`.  At `G = G_t`, `t ≥ 0`, this is
`u_G(x) < u_G(y)` within a component (`ordP_iff`). -/
def OrdP (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) (x y : Fin m) : Prop :=
  connRel M x y ∧ x ∈ POG M G ∧
    (y ∉ POG M G ∨ (¬SameCluster M (POG M G) (linkG G) x y ∧ (x, y) ∉ G))

open Classical in
/-- `Below(x)`: the elements below `x` in the order of Step 2. -/
noncomputable def belowP (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) (x : Fin m) :
    Finset (Fin m) :=
  univ.filter fun y => OrdP M G y x

/-- A context: the data computed once from `G` and read by every exchange test. -/
@[ext]
structure Ctx (m : ℕ) where
  /-- The bits of `PO_G`. -/
  po : Fin m → Bool
  /-- The cluster bits: `x` and `y` lie in one cluster. -/
  cl : Fin m → Fin m → Bool
  /-- The order bits of Step 2. -/
  ord : Fin m → Fin m → Bool
  /-- The ranks `r(Below(x))`. -/
  rkb : Fin m → ℕ

open Classical in
/-- **The context of a relation `G`**: `PO_G`, the clusters, the order of Step 2, and the ranks of
the sets `Below(x)`. -/
noncomputable def ctxOf (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Ctx m where
  po f := decide (f ∈ POG M G)
  cl x y := decide (SameCluster M (POG M G) (linkG G) x y)
  ord x y := decide (OrdP M G x y)
  rkb x := rk M (belowP M G x)

/-! ### The values computed by the circuits -/

/-- Step 1: the bit `[f ∈ PO]` read from the bits `R` of `G`, two rank queries:
`r({g : ¬R g f}) < r({g : ¬R g f} + f)`. -/
noncomputable def poV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) (f : Fin m) : Bool :=
  decide (rk M (univ.filter fun g => (!R g f) = true) <
    rk M (univ.filter fun g => (if g = f then true else !R g f) = true))

open Classical in
/-- Step 2, the link bits: `x`, `y` lie in one component (a fixed choice), `R x y`, `R y x`,
and `x, y ∈ P`. -/
noncomputable def linkV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) (P : Fin m → Bool)
    (x y : Fin m) : Bool :=
  if connRel M x y then (R x y && R y x) && (P x && P y) else false

/-- Step 2, the cluster bits: `P x` on the diagonal, the transitive closure of the links
(Warshall's algorithm) elsewhere. -/
noncomputable def clV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) (P : Fin m → Bool)
    (x y : Fin m) : Bool :=
  if x = y then P x else warshallV (linkV M R P) x y

open Classical in
/-- Step 2, the order bits: for `x`, `y` in one component,
`P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))`. -/
noncomputable def ordV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) (P : Fin m → Bool)
    (Cl : Fin m → Fin m → Bool) (x y : Fin m) : Bool :=
  if connRel M x y then P x && !(P y && (Cl x y || R x y)) else false

/-- Step 3, the ranks of the sets `{y : Ord y x}`. -/
noncomputable def rkbV (M : Matroid (Fin m)) (Ord : Fin m → Fin m → Bool) (x : Fin m) : ℕ :=
  rk M (univ.filter fun y => Ord y x = true)

/-- The context computed from the bits `R` of a relation. -/
noncomputable def ctxV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) : Ctx m :=
  let P := poV M R
  let Cl := clV M R P
  let Ord := ordV M R P Cl
  ⟨P, Cl, Ord, rkbV M Ord⟩

/-- Step 3, the rank query of the exchange test of `y`, at a context `D` and a set `A'`:
`r({z : D.ord z y} ∪ A') - D.rkb y`. -/
noncomputable def locRankV (M : Matroid (Fin m)) (y : Fin m) (P : Ctx m × (Fin m → Bool)) : ℕ :=
  rk M (univ.filter fun z => (P.1.ord z y || P.2 z) = true) - P.1.rkb y

/-- **Step 3, the exchange test of `y`** at a context `D` and a set `A`: `[y ∈ PO]` and the rank
query at `A' = A ∩ {z : D.cl y z}`, fitted to `⌈log₂(m+1)⌉` bits, equals `|A'|`
(`indepOfRankV` of `BoolAlg/Count.lean`).  At the context of `G_t`, `t ≥ 0`, this is
`[y ∈ PO_G] ∧ [r(Below(y) ∪ (A ∩ Lev(y))) - r(Below(y)) = |A ∩ Lev(y)|]` (`locV_ctxOf`). -/
noncomputable def locV (M : Matroid (Fin m)) (y : Fin m) (P : Ctx m × (Fin m → Bool)) : Bool :=
  P.1.po y && indepOfRankV (locRankV M y) (P.1, fun z => P.2 z && P.1.cl y z)

/-! ### Steps 1 and 2: the context computed from `G` is the context of `G` -/

section Context

variable (G : Finset (Fin m × Fin m))

/-- The complement of column `f`: `{g : (g, f) ∉ G}`. -/
theorem filter_not_relBits (f : Fin m) :
    (univ.filter fun g => (!relBits G g f) = true) = univ.filter fun g => (g, f) ∉ G := by
  ext g
  simp [relBits]

/-- The complement of column `f` with entry `f` set: `{g : (g, f) ∉ G} ∪ {f}`. -/
theorem filter_ite_relBits (f : Fin m) :
    (univ.filter fun g => (if g = f then true else !relBits G g f) = true) =
      insert f (univ.filter fun g => (g, f) ∉ G) := by
  ext g
  by_cases h : g = f <;> simp [relBits, h]

open Classical in
/-- **Step 1**: the bits computed from `G` are the bits of `PO_G` (`mem_POG_iff`). -/
theorem poV_relBits (hE : M.E = Set.univ) : poV M (relBits G) = fun f => decide (f ∈ POG M G) := by
  funext f
  rw [poV, filter_not_relBits, filter_ite_relBits]
  exact decide_eq_decide.2 (mem_POG_iff hE G f).symm

/-- A nonempty chain of links starts in `P`, so for `x ≠ y`, `x` and `y` lie in one cluster iff
the transitive closure of the links relates them. -/
theorem sameCluster_iff_transGen_of_ne {P : Set (Fin m)} {J : Fin m → Fin m → Prop} {x y : Fin m}
    (hxy : x ≠ y) : SameCluster M P J x y ↔ Relation.TransGen (Link M P J) x y := by
  refine ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨?_, h.to_reflTransGen⟩⟩
  · exact (Relation.reflTransGen_iff_eq_or_transGen.1 h).resolve_left (Ne.symm hxy)
  · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 h
    exact hb.1

open Classical in
/-- **Step 2, the links**: the link bits computed from `G` and `PO_G` are the links. -/
theorem linkV_eq_true_iff {x y : Fin m} :
    linkV M (relBits G) (fun f => decide (f ∈ POG M G)) x y = true ↔
      Link M (POG M G) (linkG G) x y := by
  unfold linkV Link linkG relBits
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  · simp only [false_iff]
    tauto

open Classical in
/-- **Step 2, the clusters**: Warshall's algorithm on the links, with the diagonal set to the
bits of `PO_G`, gives the clusters. -/
theorem clV_relBits : clV M (relBits G) (fun f => decide (f ∈ POG M G)) =
    fun x y => decide (SameCluster M (POG M G) (linkG G) x y) := by
  funext x y
  unfold clV
  split_ifs with hxy
  · subst hxy
    exact decide_eq_decide.2 ⟨SameCluster.refl, SameCluster.mem_left⟩
  · rw [Bool.eq_iff_iff, warshallV_eq_true_iff, decide_eq_true_iff,
      sameCluster_iff_transGen_of_ne hxy]
    have h : (fun a b => linkV M (relBits G) (fun f => decide (f ∈ POG M G)) a b = true) =
        Link M (POG M G) (linkG G) := by
      funext a b
      exact propext (linkV_eq_true_iff G)
    rw [h]

open Classical in
/-- **Step 2, the order bits**, for every relation `G`. -/
theorem ordV_relBits : ordV M (relBits G) (fun f => decide (f ∈ POG M G))
    (fun x y => decide (SameCluster M (POG M G) (linkG G) x y)) =
      fun x y => decide (OrdP M G x y) := by
  funext x y
  unfold ordV OrdP relBits
  split_ifs with h
  · rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      decide_eq_true_eq, decide_eq_false_iff_not]
    tauto
  · rw [Bool.eq_iff_iff]
    simp only [Bool.false_eq_true, false_iff, decide_eq_true_eq]
    tauto

open Classical in
/-- The ranks read from the order bits are the ranks of the sets `Below(x)`. -/
theorem rkbV_eq : rkbV M (fun x y => decide (OrdP M G x y)) = fun x => rk M (belowP M G x) := by
  funext x
  rw [rkbV, belowP]
  congr 1
  ext y
  simp

/-- **Steps 1 and 2**: for every relation `G`, the context computed from the bits of `G` is the
context of `G`. -/
theorem ctxV_relBits (hE : M.E = Set.univ) : ctxV M (relBits G) = ctxOf M G := by
  simp only [ctxV, poV_relBits G hE, clV_relBits G, ordV_relBits G, rkbV_eq G]
  rfl

end Context

/-! ### The order of Step 2 and the sets `Below(x)` -/

section Order

variable {G : Finset (Fin m × Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y : Fin m}

/-- **The order bits of Step 2** (Lemma `lem:observer`, Step 2, with `uG_lt_uG_iff`): at
`G = G_t`, `t ≥ 0`, for `x`, `y` in one component, `x` lies below `y` iff
`u_G(x) < u_G(y)`. -/
theorem ordP_iff (ht : 0 ≤ t) :
    OrdP M (Gt v t) x y ↔ connRel M x y ∧ uG M (Gt v t) x < uG M (Gt v t) y := by
  unfold OrdP
  refine and_congr_right fun hxy => ?_
  rw [uG_lt_uG_iff ht hxy]
  tauto

/-- `Below(x)` at `G = G_t`: the elements of the component of `x` with smaller `u_G`. -/
theorem mem_belowP_Gt (ht : 0 ≤ t) :
    y ∈ belowP M (Gt v t) x ↔ connRel M x y ∧ uG M (Gt v t) y < uG M (Gt v t) x := by
  simp only [belowP, mem_filter, mem_univ, true_and, ordP_iff ht]
  exact ⟨fun h => ⟨Conn.connRel_symm h.1, h.2⟩, fun h => ⟨Conn.connRel_symm h.1, h.2⟩⟩

/-- For `x ∈ PO_G`, `Below(x)` is the set `Below_G(x)` of the rank formula `rk_NG`. -/
theorem belowP_eq_belowG (hx : x ∈ POG M G) : belowP M G x = belowG M G x := by
  have hs : ∀ {a b}, SameCluster M (POG M G) (linkG G) a b →
      SameCluster M (POG M G) (linkG G) b a := fun h => h.symm linkG_comm
  ext y
  simp only [belowP, mem_filter, mem_univ, true_and, mem_belowG, OrdP]
  constructor
  · rintro ⟨hyx, hy, hx' | ⟨hn, hG⟩⟩
    · exact absurd hx hx'
    · exact ⟨hy, Conn.connRel_symm hyx, fun h => hn (hs h), hG⟩
  · rintro ⟨hy, hxy, hn, hG⟩
    exact ⟨Conn.connRel_symm hxy, hy, .inr ⟨fun h => hn (hs h), hG⟩⟩

end Order

/-! ### Step 3: the exchange tests -/

section Clusters

variable {G : Finset (Fin m × Fin m)} {x x' y : Fin m}

/-- Two clusters that share an element are equal. -/
theorem clusterG_eq (h : y ∈ clusterG M G x) : clusterG M G y = clusterG M G x := by
  have hxy : SameCluster M (POG M G) (linkG G) x y := mem_cluster.1 h
  ext z
  simp only [clusterG, mem_cluster]
  exact ⟨fun hyz => hxy.trans hyz, fun hxz => (hxy.symm linkG_comm).trans hxz⟩

/-- Distinct representatives have disjoint clusters. -/
theorem eq_of_mem_clusterG (hx : x ∈ repsG M G) (hx' : x' ∈ repsG M G)
    (hy : y ∈ clusterG M G x) (hy' : y ∈ clusterG M G x') : x = x' := by
  have h1 : clusterG M G x = clusterG M G x' := (clusterG_eq hy).symm.trans (clusterG_eq hy')
  have h2 : x' ∈ clusterG M G x := by rw [h1]; exact mem_cluster.2 (.refl (mem_repsG.1 hx').1)
  have h3 : x ∈ clusterG M G x' := by rw [← h1]; exact mem_cluster.2 (.refl (mem_repsG.1 hx).1)
  exact le_antisymm ((mem_repsG.1 hx).2 x' h2) ((mem_repsG.1 hx').2 x h3)

/-- Every element of `PO_G` lies in the cluster of a representative. -/
theorem exists_repsG (hy : y ∈ POG M G) : ∃ x ∈ repsG M G, y ∈ clusterG M G x := by
  have hne : (clusterG M G y).Nonempty := ⟨y, mem_cluster.2 (.refl hy)⟩
  have hx : (clusterG M G y).min' hne ∈ clusterG M G y := min'_mem _ hne
  have hcl := clusterG_eq hx
  refine ⟨_, mem_repsG.2 ⟨(mem_cluster.1 hx).mem_right, fun z hz => ?_⟩, ?_⟩
  · rw [hcl] at hz
    exact min'_le _ _ hz
  · rw [hcl]
    exact mem_cluster.2 (.refl hy)

/-- The clusters of the representatives are disjoint, so their parts of `A` add to at most
`|A|`. -/
theorem sum_card_inter_clusterG_le (A : Finset (Fin m)) :
    ∑ x ∈ repsG M G, #(A ∩ clusterG M G x) ≤ #A := by
  classical
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.2 fun x _ => inter_subset_left)
  · intro x hx x' hx' hne
    exact disjoint_left.2 fun z hz hz' =>
      hne (eq_of_mem_clusterG (mem_coe.1 hx) (mem_coe.1 hx') (mem_inter.1 hz).2 (mem_inter.1 hz').2)

/-- `A ∩ cluster(x) = (A - y) ∩ cluster(x)` for `y` outside the cluster. -/
theorem inter_clusterG_erase (A : Finset (Fin m)) (h : y ∉ clusterG M G x) :
    A ∩ clusterG M G x = A.erase y ∩ clusterG M G x := by
  rw [erase_inter, erase_eq_of_notMem fun hy => h (mem_inter.1 hy).2]

end Clusters

section Local

variable {v : Fin m → ℝ} {t : ℝ}

/-- `r(S ∪ B) ≤ r(S) + |B|`. -/
theorem rk_union_le_add_card (S B : Finset (Fin m)) : rk M (S ∪ B) ≤ rk M S + #B := by
  have h := M.eRk_union_le_eRk_add_encard (S : Set (Fin m)) (B : Set (Fin m))
  rw [← coe_union, ← coe_rk, ← coe_rk, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- At `G = G_t`, `t ≥ 0`, the elements of one cluster have the same set `Below` (`u_G` is
constant on clusters). -/
theorem belowP_eq_of_mem_clusterG (ht : 0 ≤ t) {x y : Fin m} (h : y ∈ clusterG M (Gt v t) x) :
    belowP M (Gt v t) y = belowP M (Gt v t) x := by
  have hxy : SameCluster M (POG M (Gt v t)) (linkG (Gt v t)) x y := mem_cluster.1 h
  have hc : connRel M x y := hxy.conn
  have hu : uG M (Gt v t) y = uG M (Gt v t) x := by
    rw [← PO_eq_POG, ← near_eq_linkG] at hxy
    rw [← u_eq_uG ht]
    exact (clusterRank_eq_of_sameCluster ht hxy).symm
  ext z
  rw [mem_belowP_Gt ht, mem_belowP_Gt ht, hu]
  exact and_congr_left fun _ =>
    ⟨fun h => Conn.connRel_trans hc h, fun h => Conn.connRel_trans (Conn.connRel_symm hc) h⟩

/-- A finite set is independent iff its rank is its size. -/
theorem indep_iff_rk_eq_card (N : Matroid (Fin m)) (S : Finset (Fin m)) :
    N.Indep (S : Set (Fin m)) ↔ rk N S = S.card := by
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _), ← coe_rk,
    Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj]

open Classical in
/-- **The exchange test at the context of `G`**: `[y ∈ PO_G]` and
`r(Below(y) ∪ (A ∩ Lev(y))) - r(Below(y)) = |A ∩ Lev(y)|`. -/
theorem locV_ctxOf (G : Finset (Fin m × Fin m)) (y : Fin m) (A : Finset (Fin m)) :
    locV M y (ctxOf M G, indicator A) = (decide (y ∈ POG M G) &&
      decide (rk M (belowP M G y ∪ (A ∩ clusterG M G y)) - rk M (belowP M G y) =
        #(A ∩ clusterG M G y))) := by
  have h1 : (univ.filter fun z => ((ctxOf M G).ord z y ||
      (indicator A z && (ctxOf M G).cl y z)) = true) = belowP M G y ∪ (A ∩ clusterG M G y) := by
    ext z
    simp [ctxOf, belowP, clusterG, mem_cluster, indicator]
  have h2 : (univ.filter fun z => (indicator A z && (ctxOf M G).cl y z) = true) =
      A ∩ clusterG M G y := by
    ext z
    simp [ctxOf, clusterG, mem_cluster, indicator]
  have h3 : rk M (belowP M G y ∪ (A ∩ clusterG M G y)) - rk M (belowP M G y) < 2 ^ Nat.size m :=
    lt_of_le_of_lt (Nat.sub_le _ _) (rk_lt_two_pow M _)
  simp only [locV, indepOfRankV, locRankV]
  rw [h1, h2, Nat.mod_eq_of_lt (by rw [show (ctxOf M G).rkb y = rk M (belowP M G y) from rfl]; exact h3)]
  rfl

open Classical in
/-- **Lemma `lem:observer`, Step 3, the exchange tests are correct**: at the context of `G_t`,
`t ≥ 0`, for every `y` and every set `A ∋ y` with `A - y` independent in `N_{G_t}`, the test of
`y` answers `[A independent in N_{G_t}]`.  By `rk_NG`, `r_{N_G}(B)` is the sum over the
representatives `x` of `T_x(B) = r(Below(x) ∪ (B ∩ Lev(x))) - r(Below(x)) ≤ |B ∩ Lev(x)|`, and
the clusters are disjoint, so `B` is independent iff every term is tight and
`Σ_x |B ∩ Lev(x)| = |B|`.  If `y ∉ PO_G`, then `y` lies in no cluster and the parts of `A` add to
`|A - y| < |A|`.  If `y ∈ Lev(x₀)`, the terms of `A` and `A - y` agree at every `x ≠ x₀`, and the
test is the tightness of the term of `x₀`. -/
theorem locV_exchOracle (hE : M.E = Set.univ) (ht : 0 ≤ t) :
    MI.ExchOracle (fun y => locV M y) (NG M (Gt v t)) (ctxOf M (Gt v t)) := by
  intro y A hyA hA
  set G := Gt v t with hG
  set R := repsG M G with hR
  have hrk : ∀ B : Finset (Fin m), rk (NG M G) B = ∑ x ∈ R,
      (rk M (belowG M G x ∪ (B ∩ clusterG M G x)) - rk M (belowG M G x)) :=
    fun B => rk_NG hE ht B
  have hT : ∀ x B, rk M (belowG M G x ∪ (B ∩ clusterG M G x)) - rk M (belowG M G x) ≤
      #(B ∩ clusterG M G x) := fun x B => by
    have := rk_union_le_add_card (M := M) (belowG M G x) (B ∩ clusterG M G x)
    omega
  have tight : ∀ B : Finset (Fin m), (NG M G).Indep (B : Set (Fin m)) →
      (∀ x ∈ R, rk M (belowG M G x ∪ (B ∩ clusterG M G x)) - rk M (belowG M G x) =
        #(B ∩ clusterG M G x)) ∧ ∑ x ∈ R, #(B ∩ clusterG M G x) = #B := fun B hB => by
    rw [indep_iff_rk_eq_card, hrk] at hB
    have h1 := sum_le_sum fun x (_ : x ∈ R) => hT x B
    have h2 : ∑ x ∈ R, #(B ∩ clusterG M G x) ≤ #B := sum_card_inter_clusterG_le B
    exact ⟨(sum_eq_sum_iff_of_le fun x _ => hT x B).1 (by omega), by omega⟩
  obtain ⟨hT', hc'⟩ := tight _ hA
  have hcard : #(A.erase y) + 1 = #A := card_erase_add_one hyA
  dsimp only
  rw [locV_ctxOf]
  by_cases hy : y ∈ POG M G
  · obtain ⟨x₀, hx₀, hyx₀⟩ := exists_repsG hy
    have hB : belowP M G y = belowG M G x₀ :=
      (belowP_eq_of_mem_clusterG ht hyx₀).trans (belowP_eq_belowG (mem_repsG.1 hx₀).1)
    rw [hB, clusterG_eq hyx₀]
    simp only [hy, decide_true, Bool.true_and]
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h => (tight A h).1 x₀ hx₀⟩
    have hoth : ∀ x ∈ R.erase x₀, rk M (belowG M G x ∪ (A ∩ clusterG M G x)) -
        rk M (belowG M G x) = #(A.erase y ∩ clusterG M G x) := fun x hx => by
      have hyx : y ∉ clusterG M G x := fun h' =>
        (mem_erase.1 hx).1 (eq_of_mem_clusterG (mem_erase.1 hx).2 hx₀ h' hyx₀)
      rw [inter_clusterG_erase A hyx]
      exact hT' x (mem_erase.1 hx).2
    have h0 : #(A.erase y ∩ clusterG M G x₀) + 1 = #(A ∩ clusterG M G x₀) := by
      rw [erase_inter]
      exact card_erase_add_one (mem_inter.2 ⟨hyA, hyx₀⟩)
    rw [indep_iff_rk_eq_card, hrk, ← add_sum_erase R _ hx₀, sum_congr rfl hoth, h]
    rw [← add_sum_erase R _ hx₀] at hc'
    omega
  · simp only [hy, decide_false, Bool.false_and]
    refine (decide_eq_false fun hind => ?_).symm
    have h1 := (tight A hind).2
    have h2 : ∀ x ∈ R, #(A ∩ clusterG M G x) = #(A.erase y ∩ clusterG M G x) := fun x _ => by
      rw [inter_clusterG_erase A fun h' => hy (mem_cluster.1 h').mem_right]
    rw [sum_congr rfl h2, hc'] at h1
    omega

/-- **Lemma `lem:observer`, Steps 1 to 3, correctness**: for every `v` and `t ≥ 0`, the exchange
tests read at the context computed from the bits of `G_t` answer every exchange question of
`N_{G_t}`. -/
theorem locV_correct (hE : M.E = Set.univ) (ht : 0 ≤ t) :
    MI.ExchOracle (fun y => locV M y) (NG M (Gt v t)) (ctxV M (relBits (Gt v t))) := by
  rw [ctxV_relBits _ hE]
  exact locV_exchOracle hE ht

/-! ### Step 5: the full relation -/

/-- `G_t = E × E` once `t` bounds every difference `v_f - v_e`. -/
theorem Gt_eq_univ (h : ∀ e f, v f - v e ≤ t) : Gt v t = univ := by
  ext p
  simp [h p.1 p.2]

/-- **`E × E = G_t` for `t ≥ max v - min v`** (Lemma `lem:observer`, Step 5, and Lemma
`lem:oneupdate`, Step 2). -/
theorem Gt_eq_univ_of_le (ht : (⨆ e, v e) - (⨅ e, v e) ≤ t) : Gt v t = univ :=
  Gt_eq_univ fun e f => (sub_le_sub (le_ciSup (Set.finite_range v).bddAbove f)
    (ciInf_le (Set.finite_range v).bddBelow e)).trans ht

end Local

/-! ### The representation of a context -/

/-- The operands of a context. -/
structure CtxA (m n : ℕ) where
  /-- The bits of `PO_G`. -/
  po : Fin m → Arg n
  /-- The cluster bits. -/
  cl : Fin m → Fin m → Arg n
  /-- The order bits. -/
  ord : Fin m → Fin m → Arg n
  /-- The ranks `r(Below(x))`, on `⌈log₂(m+1)⌉` bits each. -/
  rkb : Fin m → List (Arg n)

/-- In the gate list `gs`, every field of `s` carries the corresponding field of `T`. -/
structure CtxRep (gs : List (Gate BoolOp n)) (s : CtxA m n) (T : (Fin n → Bool) → Ctx m) :
    Prop where
  /-- The bits of `PO_G`. -/
  po : (vecR m).rep gs s.po fun x => (T x).po
  /-- The cluster bits. -/
  cl : (relR m).rep gs s.cl fun x => (T x).cl
  /-- The order bits. -/
  ord : (relR m).rep gs s.ord fun x => (T x).ord
  /-- The ranks `r(Below(x))`. -/
  rkb : (Rep.pi (Fin m) (numR (Nat.size m))).rep gs s.rkb fun x => (T x).rkb

/-- **The representation of contexts**: bits for the relations and sets, `⌈log₂(m+1)⌉` bits for
each rank. -/
def ctxR (m : ℕ) : Rep BoolOp Bool n (CtxA m n) (Ctx m) :=
  ⟨CtxRep, fun hp h => ⟨(vecR m).mono hp h.po, (relR m).mono hp h.cl, (relR m).mono hp h.ord,
    (Rep.pi (Fin m) (numR (Nat.size m))).mono hp h.rkb⟩⟩

/-! ### The circuits -/

section Circuits

variable (M) (C : Circuit BoolOp m)

/-- A rank query: run the rank circuit on a vector and fit its outputs to `⌈log₂(m+1)⌉` bits. -/
def rankB : (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (runB C) (pureB (fit (Nat.size m)))

variable {M C}

/-- **A rank query** costs `s` gates and carries `r(V)` on `⌈log₂(m+1)⌉` bits. -/
theorem rankB_impl
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    Impl (vecR m) (numR (n := n) (Nat.size m)) (rankB C) C.size
      (fun V => rk M (univ.filter fun i => V i = true)) :=
  runB_set_fit C (fun S => Nat.cast_injective ((hB S).trans (coe_rk M S).symm))
    (rk_lt_two_pow M)

variable (M C)

/-! #### Step 1 -/

/-- Step 1 for one `f`, from `(R, true)`: the complement of column `f` of `R`, two rank queries
(without and with `f`) and a comparison. -/
def poOneB (f : Fin m) : (Fin m → Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (fun p => vecNotB fun g => p.1 g f) (pureB Prod.snd))
    (seqB (pairB (fun q => rankB C q.1) fun q => rankB C fun g => if g = f then q.2 else q.1 g)
      numLtB)

/-- Step 1: the bits of `PO`, from the bits `R` of `G`; one gate `true` is shared. -/
def poB : (Fin m → Fin m → Arg n) → Bld BoolOp n (Fin m → Arg n) :=
  seqB (pairB (pureB fun s => s) fun _ => emit .not .const .const)
    fun p => tabB fun f => poOneB C f p

/-! #### Step 2 -/

/-- The link bit of one pair before the choice of the component, three gates:
`(R x y ∧ R y x) ∧ (P x ∧ P y)`. -/
def linkOneB (x y : Fin m) : (Fin m → Fin m → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (fun q => emit .and (q.1 x y) (q.1 y x)) fun q => emit .and (q.2 x) (q.2 y))
    fun p => emit .and p.1 p.2

open Classical in
/-- Keep the entries `(x, y)` of a relation with `x`, `y` in one component and replace the others
by the constant `false`.  The components are fixed data of `M`, so this costs no gate. -/
noncomputable def connMaskB {σ : Type} (b : σ → Bld BoolOp n (Fin m → Fin m → Arg n)) (s : σ) :
    Bld BoolOp n (Fin m → Fin m → Arg n) := fun gs =>
  ((b s gs).1, fun x y => if connRel M x y then (b s gs).2 x y else .const)

/-- Step 2, the link bits, from `(R, P)`. -/
noncomputable def linksB : (Fin m → Fin m → Arg n) × (Fin m → Arg n) →
    Bld BoolOp n (Fin m → Fin m → Arg n) :=
  connMaskB M fun q => tabB fun x => tabB fun y => linkOneB x y q

/-- Step 2, the cluster bits, from `(R, P)`: Warshall's algorithm on the links, and the
diagonal set to `P`. -/
noncomputable def clB : (Fin m → Fin m → Arg n) × (Fin m → Arg n) →
    Bld BoolOp n (Fin m → Fin m → Arg n) :=
  seqB (pairB (pureB Prod.snd) (seqB (linksB M) warshallB))
    (pureB fun q x y => if x = y then q.1 x else q.2 x y)

/-- The order bit of one pair before the choice of the component, four gates:
`P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))`, from `(R, P, Cl)`. -/
def ordOneB (x y : Fin m) :
    (Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n) →
      Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun q => q.2.1 x)
    (seqB (seqB (pairB (pureB fun q => q.2.1 y) fun q => emit .or (q.2.2 x y) (q.1 x y))
      fun p => emit .and p.1 p.2) fun a => emit .not a .const))
    fun p => emit .and p.1 p.2

/-- Step 2, the order bits, from `(R, P, Cl)`. -/
noncomputable def ordB :
    (Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n) →
      Bld BoolOp n (Fin m → Fin m → Arg n) :=
  connMaskB M fun q => tabB fun x => tabB fun y => ordOneB x y q

/-- Step 3, the ranks of the sets `{y : Ord y x}`, from `Ord`. -/
def rkbB (Ord : Fin m → Fin m → Arg n) : Bld BoolOp n (Fin m → List (Arg n)) :=
  tabB fun x => rankB C fun y => Ord y x

/-- **The context**, from the bits `R` of `G`: Step 1, then Step 2 (clusters and order), then the
ranks of the sets `Below(x)`. -/
noncomputable def ctxB (R : Fin m → Fin m → Arg n) : Bld BoolOp n (CtxA m n) := fun gs =>
  let p₁ := poB C R gs
  let p₂ := clB M (R, p₁.2) p₁.1
  let p₃ := ordB M (R, p₁.2, p₂.2) p₂.1
  let p₄ := rkbB C p₃.2 p₃.1
  (p₄.1, ⟨p₁.2, p₂.2, p₃.2, p₄.2⟩)

/-- The gates of the context: `2m³ + 8m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1`. -/
def ctxCost (m s : ℕ) : ℕ := 2 * m ^ 3 + 8 * m ^ 2 + m * (3 * s + 5 * Nat.size m + 2) + 1

/-! #### Step 3, the exchange tests -/

/-- The rank query of the test of `y`, from `(D, A')`: `r({z : D.ord z y} ∪ A') - D.rkb y`. -/
def locRankB (y : Fin m) : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB (seqB (seqB (pairB (pureB fun p z => p.1.ord z y) (pureB Prod.snd)) vecOrB)
    (rankB C)) (pureB fun p => p.1.rkb y)) numSubB

/-- **The exchange test of `y`**, from `(D, A)`: `A' = A ∩ {z : D.cl y z}` (`m` gates), the rank
query compared with `|A'|` (`indepOfRankB`), and the conjunction with `D.po y`. -/
def locB (y : Fin m) : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun p => p.1.po y)
    (seqB (pairB (pureB Prod.fst) fun p => vecAndB (p.2, p.1.cl y)) (indepOfRankB (locRankB C y))))
    fun q => emit .and q.1 q.2

/-- The gates of one exchange test: `s + 2m + 18⌈log₂(m+1)⌉ + popCost m + 3`. -/
def locCost (m s : ℕ) : ℕ := s + 2 * m + 18 * Nat.size m + popCost m + 3

/-! #### The implementations -/

variable {M C}
variable (hB : ∀ S : Finset (Fin m),
  (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
include hB

/-- Step 1 for one `f`: `m + 2s + 5⌈log₂(m+1)⌉ + 2` gates. -/
theorem poOneB_impl (f : Fin m) :
    Impl ((relR m).prod bitR) (bitR (n := n)) (poOneB C f)
      (m + 2 * C.size + 5 * Nat.size m + 2)
      (fun P => decide (rk M (univ.filter fun g => (!P.1 g f) = true) <
        rk M (univ.filter fun g => (if g = f then P.2 else !P.1 g f) = true))) :=
  (((vecNotB_impl.pre (R := (relR m).prod bitR) (g := fun p g => p.1 g f)
      (G := fun P g => P.1 g f) fun _ _ _ hs g => hs.1 g f).pair Impl.snd).comp
    ((((rankB_impl hB).pre (R := (vecR m).prod bitR) (g := Prod.fst) (G := Prod.fst)
      fun _ _ _ hs => hs.1).pair
      ((rankB_impl hB).pre (R := (vecR m).prod bitR) (g := fun q g => if g = f then q.2 else q.1 g)
        (G := fun Q g => if g = f then Q.2 else Q.1 g) fun _ _ _ hs g => by
          dsimp only
          split_ifs
          exacts [hs.2, hs.1 g])).comp (numLtB_impl _ _))).cost (by rw [max_self]; ring)

/-- **Step 1** (Lemma `lem:observer`): the bits of `PO`, `1 + m(m + 2s + 5⌈log₂(m+1)⌉ + 2)`
gates. -/
theorem poB_impl :
    Impl (relR m) (vecR (n := n) m) (poB C) (1 + m * (m + 2 * C.size + 5 * Nat.size m + 2))
      (poV M) :=
  (Impl.extend (true_impl (relR m))).comp (Impl.tab fun f => poOneB_impl hB f)

omit hB

/-- The link bit of one pair, three gates. -/
theorem linkOneB_impl (x y : Fin m) :
    Impl ((relR m).prod (vecR m)) (bitR (n := n)) (linkOneB x y) 3
      (fun Q => (Q.1 x y && Q.1 y x) && (Q.2 x && Q.2 y)) :=
  ((emitAnd_impl.pre (R := (relR m).prod (vecR m)) (g := fun q => (q.1 x y, q.1 y x))
      (G := fun Q => (Q.1 x y, Q.1 y x)) fun _ _ _ hs => ⟨hs.1 x y, hs.1 y x⟩).pair
    (emitAnd_impl.pre (R := (relR m).prod (vecR m)) (g := fun q => (q.2 x, q.2 y))
      (G := fun Q => (Q.2 x, Q.2 y)) fun _ _ _ hs => ⟨hs.2 x, hs.2 y⟩)).comp emitAnd_impl

variable (M) in
open Classical in
/-- Choosing the entries of one component is free. -/
theorem connMask_impl {σ τ : Type} {R : Rep BoolOp Bool n σ τ}
    {b : σ → Bld BoolOp n (Fin m → Fin m → Arg n)} {c : ℕ} {F : τ → Fin m → Fin m → Bool}
    (h : Impl R (relR m) b c F) :
    Impl R (relR m) (connMaskB M b) c (fun t x y => if connRel M x y then F t x y else false) :=
  h.post (g := fun L x y => if connRel M x y then L x y else .const)
    (G := fun L x y => if connRel M x y then L x y else false) fun gs _ _ hs x y => by
      dsimp only
      split_ifs
      exacts [hs x y, den_const gs]

variable (M) in
/-- The link bits, `3m²` gates. -/
theorem linksB_impl :
    Impl ((relR m).prod (vecR m)) (relR (n := n) m) (linksB M) (m * (m * 3))
      (fun Q => linkV M Q.1 Q.2) :=
  connMask_impl M (Impl.tab fun x => Impl.tab fun y => linkOneB_impl x y)

variable (M) in
/-- **Step 2, the clusters** (Lemma `lem:observer`): the links and Warshall's algorithm,
`3m² + 2m³` gates. -/
theorem clB_impl :
    Impl ((relR m).prod (vecR m)) (relR (n := n) m) (clB M) (m * (m * 3) + 2 * m ^ 3)
      (fun Q => clV M Q.1 Q.2) :=
  ((Impl.snd.pair ((linksB_impl M).comp warshallB_impl)).comp
    (Impl.free (R₁ := (vecR m).prod (relR m)) (R₂ := relR m)
      (g := fun q x y => if x = y then q.1 x else q.2 x y)
      (F := fun Q x y => if x = y then Q.1 x else Q.2 x y) fun _ _ _ hs x y => by
        dsimp only
        split_ifs
        exacts [hs.1 x, hs.2 x y])).cost (by ring)

/-- The order bit of one pair, four gates. -/
theorem ordOneB_impl (x y : Fin m) :
    Impl ((relR m).prod ((vecR m).prod (relR m))) (bitR (n := n)) (ordOneB x y) 4
      (fun Q => Q.2.1 x && !(Q.2.1 y && (Q.2.2 x y || Q.1 x y))) :=
  ((Impl.free (R₁ := (relR m).prod ((vecR m).prod (relR m))) (R₂ := bitR)
      (g := fun q => q.2.1 x) (F := fun Q => Q.2.1 x) fun _ _ _ hs => hs.2.1 x).pair
    ((((Impl.free (R₁ := (relR m).prod ((vecR m).prod (relR m))) (R₂ := bitR)
      (g := fun q => q.2.1 y) (F := fun Q => Q.2.1 y) fun _ _ _ hs => hs.2.1 y).pair
      (emitOr_impl.pre (R := (relR m).prod ((vecR m).prod (relR m)))
        (g := fun q => (q.2.2 x y, q.1 x y)) (G := fun Q => (Q.2.2 x y, Q.1 x y))
        fun _ _ _ hs => ⟨hs.2.2 x y, hs.1 x y⟩)).comp emitAnd_impl).comp
      emitNot_impl)).comp emitAnd_impl

variable (M) in
/-- **Step 2, the order bits** (Lemma `lem:observer`), `4m²` gates. -/
theorem ordB_impl :
    Impl ((relR m).prod ((vecR m).prod (relR m))) (relR (n := n) m) (ordB M) (m * (m * 4))
      (fun Q => ordV M Q.1 Q.2.1 Q.2.2) :=
  connMask_impl M (Impl.tab fun x => Impl.tab fun y => ordOneB_impl x y)

include hB

/-- **Step 3, the ranks of the sets `Below(x)`**, `ms` gates. -/
theorem rkbB_impl :
    Impl (relR m) (Rep.pi (Fin m) (numR (n := n) (Nat.size m))) (rkbB C) (m * C.size)
      (rkbV M) :=
  Impl.tab fun x => (rankB_impl hB).pre (R := relR m) (g := fun O y => O y x)
    (G := fun O y => O y x) fun _ _ _ hs y => hs y x

/-- **The context** (Lemma `lem:observer`, Steps 1 and 2, and the part of Step 3 independent of
the set): from the bits of `G`, `ctxB` computes `ctxV`, the context of `G` (`ctxV_relBits`), with
`ctxCost m s = 2m³ + 8m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1` gates. -/
theorem ctxB_impl : Impl (relR m) (ctxR (n := n) m) (ctxB M C) (ctxCost m C.size) (ctxV M) := by
  intro gs R T hR
  obtain ⟨hp₁, hl₁, hr₁⟩ := poB_impl hB hR
  obtain ⟨hp₂, hl₂, hr₂⟩ := clB_impl M (s := (R, (poB C R gs).2))
    (T := fun x => (T x, poV M (T x))) ⟨(relR m).mono hp₁ hR, hr₁⟩
  obtain ⟨hp₃, hl₃, hr₃⟩ := ordB_impl M
    (s := (R, (poB C R gs).2, (clB M (R, (poB C R gs).2) (poB C R gs).1).2))
    (T := fun x => (T x, poV M (T x), clV M (T x) (poV M (T x))))
    ⟨(relR m).mono (hp₁.trans hp₂) hR, (vecR m).mono hp₂ hr₁, hr₂⟩
  obtain ⟨hp₄, hl₄, hr₄⟩ := rkbB_impl hB hr₃
  -- the results of the stages persist to the end
  have q₂ := hp₃.trans hp₄
  have q₁ := hp₂.trans q₂
  refine ⟨hp₁.trans q₁, ?_, (⟨(vecR m).mono q₁ hr₁, (relR m).mono q₂ hr₂, (relR m).mono hp₄ hr₃,
    hr₄⟩ : CtxRep _ _ _)⟩
  refine hl₄.trans ?_
  rw [hl₃, hl₂, hl₁, ctxCost]
  ring

/-- The rank query of the test of `y`: `m + s + 13⌈log₂(m+1)⌉ + 1` gates. -/
theorem locRankB_impl (y : Fin m) :
    Impl ((ctxR m).prod (vecR m)) (numR (n := n) (Nat.size m)) (locRankB C y)
      (m + C.size + 13 * Nat.size m + 1) (locRankV M y) :=
  (((((Impl.free (R₁ := (ctxR m).prod (vecR m)) (R₂ := vecR m) (g := fun p z => p.1.ord z y)
      (F := fun P z => P.1.ord z y) fun _ _ _ hs z => hs.1.ord z y).pair Impl.snd).comp
      vecOrB_impl).comp (rankB_impl hB)).pair
    (Impl.free (R₁ := (ctxR m).prod (vecR m)) (R₂ := numR (Nat.size m))
      (g := fun p => p.1.rkb y) (F := fun P => P.1.rkb y) fun _ _ _ hs => hs.1.rkb y)).comp
    (numSubB_impl _ _) |>.cost (by rw [max_self]; ring)

/-- **The exchange test of `y`** (Lemma `lem:observer`, Step 3): from a context `D` and a set `A`,
`locB` computes `locV M y (D, A)` with `locCost m s` gates (`locCost_le`). -/
theorem locB_impl (y : Fin m) :
    Impl ((ctxR m).prod (vecR m)) (bitR (n := n)) (locB C y) (locCost m C.size) (locV M y) :=
  (((Impl.free (R₁ := (ctxR m).prod (vecR m)) (R₂ := bitR) (g := fun p => p.1.po y)
      (F := fun P => P.1.po y) fun _ _ _ hs => hs.1.po y).pair
    ((Impl.fst.pair (vecAndB_impl.pre (R := (ctxR m).prod (vecR m))
      (g := fun p => (p.2, p.1.cl y)) (G := fun P => (P.2, P.1.cl y))
      fun _ _ _ hs => ⟨hs.2, hs.1.cl y⟩)).comp
      (indepOfRankB_impl (locRankB_impl hB y)))).comp emitAnd_impl).cost
    (by unfold locCost; ring)

omit hB in
/-- The context costs `O(m(s + log m) + m³)` gates; explicitly at most `3ms + 17m³ + 1`. -/
theorem ctxCost_le (m s : ℕ) : ctxCost m s ≤ 3 * m * s + 17 * m ^ 3 + 1 := by
  have hW : m * Nat.size m ≤ m * m := Nat.mul_le_mul_left m (size_le_self m)
  have h₁ : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h₂ : m ^ 2 ≤ m ^ 3 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Nat.pow_le_pow_right hm (by norm_num)
  unfold ctxCost
  nlinarith

omit hB in
/-- One exchange test costs `s + O(m)` gates; explicitly at most `s + 42(m + 1)`. -/
theorem locCost_le (m s : ℕ) : locCost m s ≤ s + 42 * (m + 1) := by
  have hW := size_le_self m
  have hp := popCost_le m
  unfold locCost
  omega

open Classical in
/-- **Lemma `lem:observer`, Steps 1 to 3.**  Let `M` have ground set `E = Fin m`, and let the
Boolean circuit `C` of size `s` output the binary digits of the rank of `M`.  Then:

1. a circuit of `ctxCost m s ≤ 3ms + 17m³ + 1` gates computes, from the bits of a relation
   `G ⊆ E × E`, the context `ctxV M`, which is the context of `G` (`ctxV_relBits`);
2. for each `y`, a circuit of `locCost m s ≤ s + 42(m + 1)` gates computes, from a context `D`
   and a set `A ⊆ E`, the bit `locV M y (D, A)`;
3. at the context of `G_t`, for every `v` and every `t ≥ 0`, these tests answer the exchange
   questions of `N_{G_t}`: for `y ∈ A` with `A - y` independent, the bit is
   `[A independent in N_{G_t}]`. -/
theorem lem_observer_oracle (hE : M.E = Set.univ) :
    Impl (relR m) (ctxR (n := n) m) (ctxB M C) (ctxCost m C.size) (ctxV M) ∧
      (∀ y, Impl ((ctxR m).prod (vecR m)) (bitR (n := n)) (locB C y) (locCost m C.size)
        (locV M y)) ∧
      ctxCost m C.size ≤ 3 * m * C.size + 17 * m ^ 3 + 1 ∧
      locCost m C.size ≤ C.size + 42 * (m + 1) ∧
      ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        MI.ExchOracle (fun y => locV M y) (NG M (Gt v t)) (ctxV M (relBits (Gt v t))) :=
  ⟨ctxB_impl hB, locB_impl hB, ctxCost_le _ _, locCost_le _ _, fun _ _ ht => locV_correct hE ht⟩

end Circuits

end SignedTropical.Rainbow.Observer
