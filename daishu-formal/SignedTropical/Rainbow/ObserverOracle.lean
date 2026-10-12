import SignedTropical.Rainbow.POSLRank
import SignedTropical.BoolAlg.Count
import SignedTropical.BoolAlg.Rel

/-!
# The observer, Steps 1 to 3: an independence oracle for `N_G`

`greedy_intersection.tex`, Lemma `lem:observer`, Steps 1 to 3.  A Boolean circuit reads a
relation `G ⊆ E × E` (`relR m`, entry `(g, f)` the bit `[(g, f) ∈ G]`, `relBits`) and computes once
a *context* (`Ctx`, `ctxR`), from which a second circuit, the *oracle*, tests independence in
`N_G` for any set `A` (`vecR m`).  The rank circuit of `M` (size `s`, the hypothesis of
Theorem `thm:A`) is run on computed wires (`runB`, `rankB`).

**The context** (`ctxB`, `ctxB_impl`, `ctxCost m s = 2m³ + 12m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1`
gates), with its value `ctxV`:

* Step 1 (`poB`): `f ∈ PO_G` iff `r({g : (g, f) ∉ G}) < r({g : (g, f) ∉ G} + f)` (`poV_relBits`),
  two rank runs and a comparison for each `f`;
* Step 2: the links `(x, y), (y, x) ∈ G` for `x, y ∈ PO_G` in one component (`linksB`; the
  components are fixed, so this choice costs no gate), Warshall's algorithm for the clusters
  (`clB`, `clV_relBits`), the order bits `ordV` (`ordB`), which at `G = G_t`, `t ≥ 0`, are
  `[u_G(x) < u_G(y)]` within components (`ordP_iff`), the representatives, the elements of
  least index of the clusters (`repB`, `repV_eq`), and the clusters of the representatives
  (`levB`, `levV_eq`);
* Step 3, the part independent of `A`: the ranks `r(Below(x))` (`rkbB`), where `Below(x)` is the
  set of elements below `x` in the order (`belowP`, equal to `Below_G(x)` of `rk_NG` for
  `x ∈ PO_G`, `belowP_eq_belowG`).

For every relation `G`, the context computed from `G` is `ctxOf M G` (`ctxV_relBits`), whose
fields are the sets above, read from `G`.

**The rank query** (Step 3; `rankNB`, `rankNB_impl`,
`rankNCost m s = m(2m + s + 13⌈log₂(m+1)⌉ + 1) + 22m⌈log₂(m+1)⌉ ≤ ms + 38m²` gates): for each
`x`, one rank run on `Below(x) ∪ (A ∩ Lev(x))`, with `Lev(x)` the cluster of `x` if `x` is a
representative and `∅` otherwise, minus `r(Below(x))`, and the sum of these terms (`rankNV`),
which is `r_{N_G}(A)` at `G = G_t`, `t ≥ 0` (`rankNV_ctxOf`, `rankNV_correct`, from `rk_NG`).

**The oracle** (`oracleB`, `oracleB_impl`,
`oracleCost m s = rankNCost m s + popCost m + 5⌈log₂(m+1)⌉ + 1 ≤ ms + 70m² + 1` gates per
query) compares the rank query with `|A|`; it is the independence oracle from a rank query of
`BoolAlg/Count.lean` (`indepOfRankB`, `indepOfRank_correct`).  Its value is `decide (N_G.Indep A)` at the context of
`G_t` for every `v` and `t ≥ 0` (`oracle_correct`), in particular at `G = E × E = G_t` for
`t ≥ max v - min v` (`Gt_eq_univ_of_le`), where `N_{E × E} = M` (`NG_univ`, `oracle_univ`).
`lem_observer_oracle` collects the two implementations, their sizes and the correctness.
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

/-- A context: the data computed once from `G` and read by every query of the oracle. -/
@[ext]
structure Ctx (m : ℕ) where
  /-- The bits of `G`. -/
  rel : Fin m → Fin m → Bool
  /-- The bits of `PO_G`. -/
  po : Fin m → Bool
  /-- The cluster bits: `x` and `y` lie in one cluster. -/
  cl : Fin m → Fin m → Bool
  /-- The order bits of Step 2. -/
  ord : Fin m → Fin m → Bool
  /-- The representatives: the element of least index of each cluster. -/
  rep : Fin m → Bool
  /-- The clusters of the representatives: `lev x y` iff `x` is a representative and `y` lies
  in its cluster. -/
  lev : Fin m → Fin m → Bool
  /-- The ranks `r(Below(x))`. -/
  rkb : Fin m → ℕ

open Classical in
/-- **The context of a relation `G`**: `G`, `PO_G`, the clusters, the order of Step 2, the
representatives, their clusters, and the ranks of the sets `Below(x)`. -/
noncomputable def ctxOf (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Ctx m where
  rel := relBits G
  po f := decide (f ∈ POG M G)
  cl x y := decide (SameCluster M (POG M G) (linkG G) x y)
  ord x y := decide (OrdP M G x y)
  rep x := decide (x ∈ repsG M G)
  lev x y := decide (x ∈ repsG M G ∧ y ∈ clusterG M G x)
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

/-- Step 2, the representative bits: `x` is the element of least index of its row of `Cl`. -/
def repV (Cl : Fin m → Fin m → Bool) (x : Fin m) : Bool :=
  leadV (Cl x) x

/-- Step 2, the clusters of the representatives. -/
def levV (Cl : Fin m → Fin m → Bool) (x y : Fin m) : Bool :=
  repV Cl x && Cl x y

/-- Step 3, the ranks of the sets `{y : Ord y x}`. -/
noncomputable def rkbV (M : Matroid (Fin m)) (Ord : Fin m → Fin m → Bool) (x : Fin m) : ℕ :=
  rk M (univ.filter fun y => Ord y x = true)

/-- The context computed from the bits `R` of a relation. -/
noncomputable def ctxV (M : Matroid (Fin m)) (R : Fin m → Fin m → Bool) : Ctx m :=
  let P := poV M R
  let Cl := clV M R P
  let Ord := ordV M R P Cl
  ⟨R, P, Cl, Ord, repV Cl, levV Cl, rkbV M Ord⟩

/-- Step 3, the rank query at a context `D` and a set `A`:
`Σ_x (r({y : D.ord y x} ∪ (A ∩ {y : D.lev x y})) - D.rkb x)`, which is `r_{N_G}(A)` at the
context of `G = G_t`, `t ≥ 0` (`rankNV_correct`). -/
noncomputable def rankNV (M : Matroid (Fin m)) (D : Ctx m) (A : Fin m → Bool) : ℕ :=
  ∑ x, (rk M (univ.filter fun y => (D.ord y x || (A y && D.lev x y)) = true) - D.rkb x)

/-- The value of the oracle at a context `D` and a set `A`: the rank query, fitted to
`⌈log₂(m+1)⌉` bits, equals `|A|` (`indepOfRankV` of `BoolAlg/Count.lean`). -/
noncomputable def oracleV (M : Matroid (Fin m)) (D : Ctx m) (A : Fin m → Bool) : Bool :=
  indepOfRankV (fun P : Ctx m × (Fin m → Bool) => rankNV M P.1 P.2) (D, A)

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
/-- **Step 2, the representatives**: the element of least index of each cluster. -/
theorem repV_eq : repV (fun x y => decide (SameCluster M (POG M G) (linkG G) x y)) =
    fun x => decide (x ∈ repsG M G) := by
  funext x
  rw [Bool.eq_iff_iff, repV, leadV_eq_true_iff]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, mem_repsG, clusterG, mem_cluster]
  refine ⟨fun ⟨hx, h⟩ => ⟨hx.mem_left, fun y hy => not_lt.1 fun hlt => h y hlt hy⟩,
    fun ⟨hx, h⟩ => ⟨.refl hx, fun y hlt hy => absurd (h y hy) (not_le.2 hlt)⟩⟩

open Classical in
/-- **Step 2, the clusters of the representatives.** -/
theorem levV_eq : levV (fun x y => decide (SameCluster M (POG M G) (linkG G) x y)) =
    fun x y => decide (x ∈ repsG M G ∧ y ∈ clusterG M G x) := by
  funext x y
  rw [levV, repV_eq, Bool.eq_iff_iff]
  simp [clusterG, mem_cluster]

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
  simp only [ctxV, poV_relBits G hE, clV_relBits G, ordV_relBits G, repV_eq G, levV_eq G, rkbV_eq G]
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

/-! ### Step 3: the rank of `N_G` and independence, read from the context -/

section Oracle

variable {v : Fin m → ℝ} {t : ℝ}

/-- A finite set is independent iff its rank is its size. -/
theorem indep_iff_rk_eq_card (N : Matroid (Fin m)) (S : Finset (Fin m)) :
    N.Indep (S : Set (Fin m)) ↔ rk N S = S.card := by
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _), ← coe_rk,
    Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj]

open Classical in
/-- The set of the rank query of `x`: `Below(x) ∪ (A ∩ cluster(x))` if `x` is a representative,
and `Below(x)` otherwise. -/
theorem filter_term_ctxOf (G : Finset (Fin m × Fin m)) (A : Fin m → Bool) (x : Fin m) :
    (univ.filter fun y => ((ctxOf M G).ord y x || (A y && (ctxOf M G).lev x y)) = true) =
      belowP M G x ∪
        if x ∈ repsG M G then (univ.filter fun y => A y = true) ∩ clusterG M G x else ∅ := by
  ext y
  by_cases hx : x ∈ repsG M G <;> simp [ctxOf, belowP, hx]

/-- **Step 3, the rank of `N_G`** (Lemma `lem:observer`, Step 3): at the context of
`G = G_t`, `t ≥ 0`, the sum over all `x` of `r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x))`, with
`Lev(x)` the cluster of `x` for a representative and `∅` otherwise, is `r_{N_G}(A)`
(`rk_NG`). -/
theorem rankNV_ctxOf (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Fin m → Bool) :
    rankNV M (ctxOf M (Gt v t)) A = rk (NG M (Gt v t)) (univ.filter fun y => A y = true) := by
  classical
  have h : ∀ x, rk M (univ.filter fun y =>
      ((ctxOf M (Gt v t)).ord y x || (A y && (ctxOf M (Gt v t)).lev x y)) = true) -
        (ctxOf M (Gt v t)).rkb x = if x ∈ repsG M (Gt v t) then
          rk M (belowG M (Gt v t) x ∪ ((univ.filter fun y => A y = true) ∩
            clusterG M (Gt v t) x)) - rk M (belowG M (Gt v t) x) else 0 := fun x => by
    rw [filter_term_ctxOf, show (ctxOf M (Gt v t)).rkb x = rk M (belowP M (Gt v t) x) from rfl]
    split_ifs with hx
    · rw [belowP_eq_belowG (mem_repsG.1 hx).1]
    · rw [union_empty, Nat.sub_self]
  rw [rankNV, sum_congr rfl fun x _ => h x, sum_ite_mem, univ_inter, rk_NG hE ht]

/-- **Lemma `lem:observer`, Step 3, the rank queries**: for every `v` and `t ≥ 0`, the rank query
at the context computed from the bits of `G_t` is `r_{N_{G_t}}(A)`. -/
theorem rankNV_correct (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Fin m → Bool) :
    rankNV M (ctxV M (relBits (Gt v t))) A = rk (NG M (Gt v t)) (univ.filter fun y => A y = true) :=
  by rw [ctxV_relBits _ hE, rankNV_ctxOf hE ht]

open Classical in
/-- **The oracle is correct at the context of `G_t`**: for `t ≥ 0`, its value is
`[A independent in N_{G_t}]`. -/
theorem oracleV_ctxOf (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Fin m → Bool) :
    oracleV M (ctxOf M (Gt v t)) A =
      decide ((NG M (Gt v t)).Indep ((univ.filter fun i => A i = true : Finset (Fin m)) :
        Set (Fin m))) :=
  indepOfRank_correct (fun S => by rw [rankNV_ctxOf hE ht, filter_indicator]) A

open Classical in
/-- **Lemma `lem:observer`, Steps 1 to 3, correctness**: for every `v` and `t ≥ 0`, the oracle
read at the context computed from the bits of `G_t` decides independence in `N_{G_t}`. -/
theorem oracle_correct (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Fin m → Bool) :
    oracleV M (ctxV M (relBits (Gt v t))) A =
      decide ((NG M (Gt v t)).Indep ((univ.filter fun i => A i = true : Finset (Fin m)) :
        Set (Fin m))) := by
  rw [ctxV_relBits _ hE, oracleV_ctxOf hE ht]

/-- `rankNV_correct` at the indicator vector of a set `S` (the hypothesis `hFr` of
`indepOfRank_correct`). -/
theorem rankNV_correct_indicator (hE : M.E = Set.univ) (ht : 0 ≤ t) (S : Finset (Fin m)) :
    rankNV M (ctxV M (relBits (Gt v t))) (indicator S) = rk (NG M (Gt v t)) S := by
  rw [rankNV_correct hE ht, filter_indicator]

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

open Classical in
/-- **Lemma `lem:observer`, Step 5**: at `G = E × E` the oracle decides independence in
`N_{E × E} = M` (`NG_univ`). -/
theorem oracle_univ (hE : M.E = Set.univ) (A : Fin m → Bool) :
    oracleV M (ctxV M (relBits univ)) A =
      decide (M.Indep ((univ.filter fun i => A i = true : Finset (Fin m)) : Set (Fin m))) := by
  have h := oracle_correct (M := M) (v := 0) (t := 0) hE le_rfl A
  rwa [Gt_eq_univ fun _ _ => by simp, NG_univ hE] at h

end Oracle

/-! ### The representation of a context -/

/-- The operands of a context. -/
structure CtxA (m n : ℕ) where
  /-- The bits of `G`. -/
  rel : Fin m → Fin m → Arg n
  /-- The bits of `PO_G`. -/
  po : Fin m → Arg n
  /-- The cluster bits. -/
  cl : Fin m → Fin m → Arg n
  /-- The order bits. -/
  ord : Fin m → Fin m → Arg n
  /-- The representative bits. -/
  rep : Fin m → Arg n
  /-- The clusters of the representatives. -/
  lev : Fin m → Fin m → Arg n
  /-- The ranks `r(Below(x))`, on `⌈log₂(m+1)⌉` bits each. -/
  rkb : Fin m → List (Arg n)

/-- In the gate list `gs`, every field of `s` carries the corresponding field of `T`. -/
structure CtxRep (gs : List (Gate BoolOp n)) (s : CtxA m n) (T : (Fin n → Bool) → Ctx m) :
    Prop where
  /-- The bits of `G`. -/
  rel : (relR m).rep gs s.rel fun x => (T x).rel
  /-- The bits of `PO_G`. -/
  po : (vecR m).rep gs s.po fun x => (T x).po
  /-- The cluster bits. -/
  cl : (relR m).rep gs s.cl fun x => (T x).cl
  /-- The order bits. -/
  ord : (relR m).rep gs s.ord fun x => (T x).ord
  /-- The representative bits. -/
  rep : (vecR m).rep gs s.rep fun x => (T x).rep
  /-- The clusters of the representatives. -/
  lev : (relR m).rep gs s.lev fun x => (T x).lev
  /-- The ranks `r(Below(x))`. -/
  rkb : (Rep.pi (Fin m) (numR (Nat.size m))).rep gs s.rkb fun x => (T x).rkb

/-- **The representation of contexts**: bits for the relations and sets, `⌈log₂(m+1)⌉` bits for
each rank. -/
def ctxR (m : ℕ) : Rep BoolOp Bool n (CtxA m n) (Ctx m) :=
  ⟨CtxRep, fun hp h => ⟨(relR m).mono hp h.rel, (vecR m).mono hp h.po, (relR m).mono hp h.cl,
    (relR m).mono hp h.ord, (vecR m).mono hp h.rep, (relR m).mono hp h.lev,
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

/-- Step 2, the representative bits, from `Cl`: least-index selection in every row, and the
diagonal. -/
def repB (Cl : Fin m → Fin m → Arg n) : Bld BoolOp n (Fin m → Arg n) := fun gs =>
  ((tabB (fun x => vecFirstB (Cl x)) gs).1, fun x => (tabB (fun x => vecFirstB (Cl x)) gs).2 x x)

/-- Step 2, the clusters of the representatives, from `(Rep, Cl)`. -/
def levB (q : (Fin m → Arg n) × (Fin m → Fin m → Arg n)) : Bld BoolOp n (Fin m → Fin m → Arg n) :=
  tabB fun x => vecMaskB (q.1 x, q.2 x)

/-- Step 3, the ranks of the sets `{y : Ord y x}`, from `Ord`. -/
def rkbB (Ord : Fin m → Fin m → Arg n) : Bld BoolOp n (Fin m → List (Arg n)) :=
  tabB fun x => rankB C fun y => Ord y x

/-- **The context**, from the bits `R` of `G`: Step 1, then Step 2 (clusters, order,
representatives, their clusters), then the ranks of the sets `Below(x)`. -/
noncomputable def ctxB (R : Fin m → Fin m → Arg n) : Bld BoolOp n (CtxA m n) := fun gs =>
  let p₁ := poB C R gs
  let p₂ := clB M (R, p₁.2) p₁.1
  let p₃ := ordB M (R, p₁.2, p₂.2) p₂.1
  let p₄ := repB p₂.2 p₃.1
  let p₅ := levB (p₄.2, p₂.2) p₄.1
  let p₆ := rkbB C p₃.2 p₅.1
  (p₆.1, ⟨R, p₁.2, p₂.2, p₃.2, p₄.2, p₅.2, p₆.2⟩)

/-- The gates of the context: `2m³ + 12m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1`. -/
def ctxCost (m s : ℕ) : ℕ := 2 * m ^ 3 + 12 * m ^ 2 + m * (3 * s + 5 * Nat.size m + 2) + 1

/-! #### Step 3, the oracle -/

/-- The term of `x`, from `(D, A)`: `r({y : D.ord y x} ∪ (A ∩ {y : D.lev x y})) - D.rkb x`. -/
def rankTermB (x : Fin m) : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB (seqB (seqB (pairB (pureB fun p y => p.1.ord y x) fun p => vecAndB (p.2, p.1.lev x))
    vecOrB) (rankB C)) (pureB fun p => p.1.rkb x)) numSubB

/-- **The rank query**, from `(D, A)`: the terms of all `x` and their sum. -/
def rankNB : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (fun p => tabB fun x => rankTermB C x p) (numSumB (Nat.size m))

/-- **The oracle**, from `(D, A)`: the rank query compared with the size of `A`
(`indepOfRankB` of `BoolAlg/Count.lean`). -/
def oracleB : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  indepOfRankB (rankNB C)

/-- The gates of one rank query: `m(2m + s + 13⌈log₂(m+1)⌉ + 1) + 22m⌈log₂(m+1)⌉`. -/
def rankNCost (m s : ℕ) : ℕ := m * (2 * m + s + 13 * Nat.size m + 1) + 22 * m * Nat.size m

/-- The gates of one query of the oracle: `rankNCost m s + popCost m + 5⌈log₂(m+1)⌉ + 1`. -/
def oracleCost (m s : ℕ) : ℕ := rankNCost m s + popCost m + (5 * Nat.size m + 1)

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

/-- **Step 2, the representatives** (Lemma `lem:observer`): least-index selection in every row,
`3m²` gates. -/
theorem repB_impl : Impl (relR m) (vecR (n := n) m) repB (m * (3 * m)) repV :=
  (vecFirstB_impl.map m).post (g := fun L x => L x x) (G := fun L x => L x x)
    fun _ _ _ hs x => hs x x

/-- **Step 2, the clusters of the representatives**, `m²` gates. -/
theorem levB_impl :
    Impl ((vecR m).prod (relR m)) (relR (n := n) m) levB (m * m)
      (fun Q x y => Q.1 x && Q.2 x y) :=
  Impl.tab fun x => vecMaskB_impl.pre (R := (vecR m).prod (relR m)) (g := fun q => (q.1 x, q.2 x))
    (G := fun Q => (Q.1 x, Q.2 x)) fun _ _ _ hs => ⟨hs.1 x, hs.2 x⟩

include hB

/-- **Step 3, the ranks of the sets `Below(x)`**, `ms` gates. -/
theorem rkbB_impl :
    Impl (relR m) (Rep.pi (Fin m) (numR (n := n) (Nat.size m))) (rkbB C) (m * C.size)
      (rkbV M) :=
  Impl.tab fun x => (rankB_impl hB).pre (R := relR m) (g := fun O y => O y x)
    (G := fun O y => O y x) fun _ _ _ hs y => hs y x

/-- **The context** (Lemma `lem:observer`, Steps 1 and 2, and the part of Step 3 independent of
`A`): from the bits of `G`, `ctxB` computes `ctxV`, the context of `G` (`ctxV_relBits`), with
`ctxCost m s = 2m³ + 12m² + m(3s + 5⌈log₂(m+1)⌉ + 2) + 1` gates. -/
theorem ctxB_impl : Impl (relR m) (ctxR (n := n) m) (ctxB M C) (ctxCost m C.size) (ctxV M) := by
  intro gs R T hR
  obtain ⟨hp₁, hl₁, hr₁⟩ := poB_impl hB hR
  obtain ⟨hp₂, hl₂, hr₂⟩ := clB_impl M (s := (R, (poB C R gs).2))
    (T := fun x => (T x, poV M (T x))) ⟨(relR m).mono hp₁ hR, hr₁⟩
  obtain ⟨hp₃, hl₃, hr₃⟩ := ordB_impl M
    (s := (R, (poB C R gs).2, (clB M (R, (poB C R gs).2) (poB C R gs).1).2))
    (T := fun x => (T x, poV M (T x), clV M (T x) (poV M (T x))))
    ⟨(relR m).mono (hp₁.trans hp₂) hR, (vecR m).mono hp₂ hr₁, hr₂⟩
  obtain ⟨hp₄, hl₄, hr₄⟩ := repB_impl ((relR m).mono hp₃ hr₂)
  obtain ⟨hp₅, hl₅, hr₅⟩ := levB_impl (s := (_, (clB M (R, (poB C R gs).2) (poB C R gs).1).2))
    (T := fun x => (repV (clV M (T x) (poV M (T x))), clV M (T x) (poV M (T x))))
    ⟨hr₄, (relR m).mono (hp₃.trans hp₄) hr₂⟩
  obtain ⟨hp₆, hl₆, hr₆⟩ := rkbB_impl hB ((relR m).mono (hp₄.trans hp₅) hr₃)
  -- the results of the stages persist to the end
  have q₄ := hp₅.trans hp₆
  have q₃ := hp₄.trans q₄
  have q₂ := hp₃.trans q₃
  have q₁ := hp₂.trans q₂
  refine ⟨hp₁.trans q₁, ?_, (⟨(relR m).mono (hp₁.trans q₁) hR, (vecR m).mono q₁ hr₁,
    (relR m).mono q₂ hr₂, (relR m).mono q₃ hr₃, (vecR m).mono q₄ hr₄, (relR m).mono hp₆ hr₅,
    hr₆⟩ : CtxRep _ _ _)⟩
  refine hl₆.trans ?_
  rw [hl₅, hl₄, hl₃, hl₂, hl₁, ctxCost]
  ring

/-- The term of `x`: `2m + s + 13⌈log₂(m+1)⌉ + 1` gates. -/
theorem rankTermB_impl (x : Fin m) :
    Impl ((ctxR m).prod (vecR m)) (numR (n := n) (Nat.size m)) (rankTermB C x)
      (2 * m + C.size + 13 * Nat.size m + 1)
      (fun P => rk M (univ.filter fun y => (P.1.ord y x || (P.2 y && P.1.lev x y)) = true) -
        P.1.rkb x) :=
  (((((Impl.free (R₁ := (ctxR m).prod (vecR m)) (R₂ := vecR m) (g := fun p y => p.1.ord y x)
      (F := fun P y => P.1.ord y x) fun _ _ _ hs y => hs.1.ord y x).pair
    (vecAndB_impl.pre (R := (ctxR m).prod (vecR m)) (g := fun p => (p.2, p.1.lev x))
      (G := fun P => (P.2, P.1.lev x)) fun _ _ _ hs => ⟨hs.2, hs.1.lev x⟩)).comp vecOrB_impl).comp
    (rankB_impl hB)).pair
    (Impl.free (R₁ := (ctxR m).prod (vecR m)) (R₂ := numR (Nat.size m))
      (g := fun p => p.1.rkb x) (F := fun P => P.1.rkb x) fun _ _ _ hs => hs.1.rkb x)).comp
    (numSubB_impl _ _) |>.cost (by rw [max_self]; ring)

omit hB in
/-- The context costs `O(m(s + log m) + m³)` gates; explicitly at most `3ms + 21m³ + 1`. -/
theorem ctxCost_le (m s : ℕ) : ctxCost m s ≤ 3 * m * s + 21 * m ^ 3 + 1 := by
  have hW : m * Nat.size m ≤ m * m := Nat.mul_le_mul_left m (size_le_self m)
  have h₁ : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h₂ : m ^ 2 ≤ m ^ 3 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Nat.pow_le_pow_right hm (by norm_num)
  unfold ctxCost
  nlinarith

omit hB in
/-- One rank query costs `ms + O(m²)` gates; explicitly at most `ms + 38m²`. -/
theorem rankNCost_le (m s : ℕ) : rankNCost m s ≤ m * s + 38 * m ^ 2 := by
  have hW : m * Nat.size m ≤ m * m := Nat.mul_le_mul_left m (size_le_self m)
  have h₁ : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  unfold rankNCost
  nlinarith

omit hB in
/-- One query of the oracle costs `ms + O(m²)` gates; explicitly at most `ms + 70m² + 1`. -/
theorem oracleCost_le (m s : ℕ) : oracleCost m s ≤ m * s + 70 * m ^ 2 + 1 := by
  have hR := rankNCost_le m s
  have hW := size_le_self m
  have hp := popCost_le m
  have h₁ : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  unfold oracleCost
  omega

/-- **The rank query** (Lemma `lem:observer`, Step 3): from a context `D` and a set `A`,
`rankNB` computes `rankNV M D A` on `2⌈log₂(m+1)⌉` bits with `rankNCost m s ≤ ms + 38m²` gates
(`rankNCost_le`); at the context of `G = G_t`, `t ≥ 0`, this is `r_{N_G}(A)`
(`rankNV_correct`). -/
theorem rankNB_impl :
    Impl ((ctxR m).prod (vecR m)) (numR (n := n) (Nat.size m + Nat.size m)) (rankNB C)
      (rankNCost m C.size) (fun P => rankNV M P.1 P.2) :=
  ((Impl.tab fun x => rankTermB_impl hB x).comp (numSumB_impl (Nat.size m))).cost
    (by rw [rankNCost]; ring)

/-- **The oracle** (Lemma `lem:observer`, Step 3 and the independence tests of Step 4): from a
context `D` and a set `A`, `oracleB` computes `oracleV M D A` with
`oracleCost m s ≤ ms + 70m² + 1` gates (`oracleCost_le`).  Its value is `[A independent in N_G]`
at the context of `G = G_t`, `t ≥ 0` (`oracle_correct`). -/
theorem oracleB_impl :
    Impl ((ctxR m).prod (vecR m)) (bitR (n := n)) (oracleB C) (oracleCost m C.size)
      (fun P => oracleV M P.1 P.2) :=
  indepOfRankB_impl (rankNB_impl hB)

open Classical in
/-- **Lemma `lem:observer`, Steps 1 to 3, and the fact used in Step 5.**  Let `M` have ground set
`E = Fin m`, and let the Boolean circuit `C` of size `s` output the binary digits of the rank of
`M`.  Then:

1. a circuit of `ctxCost m s ≤ 3ms + 21m³ + 1` gates computes, from the bits of a relation
   `G ⊆ E × E`, the context `ctxV M`, which is the context of `G` (`ctxV_relBits`);
2. a circuit of `oracleCost m s ≤ ms + 70m² + 1` gates computes, from a context `D` and a set
   `A ⊆ E`, the bit `oracleV M D A`;
3. at the context of `G_t`, for every `v`, every `t ≥ 0` and every `A`, this bit is
   `[A independent in N_{G_t}]`;
4. at the context of `E × E`, it is `[A independent in M]`. -/
theorem lem_observer_oracle (hE : M.E = Set.univ) :
    Impl (relR m) (ctxR (n := n) m) (ctxB M C) (ctxCost m C.size) (ctxV M) ∧
      Impl ((ctxR m).prod (vecR m)) (bitR (n := n)) (oracleB C) (oracleCost m C.size)
        (fun P => oracleV M P.1 P.2) ∧
      ctxCost m C.size ≤ 3 * m * C.size + 21 * m ^ 3 + 1 ∧
      oracleCost m C.size ≤ m * C.size + 70 * m ^ 2 + 1 ∧
      (∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t → ∀ A : Fin m → Bool,
        oracleV M (ctxV M (relBits (Gt v t))) A = decide ((NG M (Gt v t)).Indep
          ((univ.filter fun i => A i = true : Finset (Fin m)) : Set (Fin m)))) ∧
      ∀ A : Fin m → Bool, oracleV M (ctxV M (relBits univ)) A =
        decide (M.Indep ((univ.filter fun i => A i = true : Finset (Fin m)) : Set (Fin m))) :=
  ⟨ctxB_impl hB, oracleB_impl hB, ctxCost_le _ _, oracleCost_le _ _,
    fun _ _ ht A => oracle_correct hE ht A, oracle_univ hE⟩

end Circuits

end SignedTropical.Rainbow.Observer
