import SignedTropical.Rainbow.POSLRank
import SignedTropical.Rainbow.MICircuit
import SignedTropical.Rainbow.Events
import SignedTropical.BoolAlg.Rel

/-!
# The observer, Steps 1 and 2: the context from the event bits, and the exchange tests

`greedy_intersection.tex`, Lemma `lem:observer`, Steps 1 and 2.  A Boolean circuit reads the
*event bits* (`Events.qn m` inputs: the entry bits `[t_x ≤ t]`, the merge bits `[T_xy ≤ t]` and
the order bits `[U_xy ≤ t]` of `Rainbow/Events.lean`) and computes once a *context* (`Ctx`,
`ctxR`), from which a second circuit for each `y`, the *exchange test* of `y`, decides
independence in `N_G` of the sets `A ∋ y` with `A - y` independent, the only sets on which the
matroid intersection circuit (`Rainbow/MICircuit.lean`) uses the test of `y`.  The rank circuit
of `M` (size `s`, the hypothesis of Theorem `thm:A`) is run on computed wires (`runB`, `rankB`).

**The context** (`evCtxB`, `evCtxB_impl`, `m(2m + s)` gates), with its value `evCtxV`:

* Step 1: the bits of `PO` are the entry bits, `false` at the loops; the cluster bits are the
  merge bits within components (`Events.Kr`), and the bits of `PO` on the diagonal; the order
  bits are `P_x ∧ ¬[U_xy ≤ t]` within components (`andNotB`, two gates each).  The components and
  the loops are fixed data of `M`, so these choices cost no gate.
* The part of Step 2 independent of the set: the ranks `r(Below(x))` (`rkbB`), one rank query
  each, where `Below(x)` is the set of elements below `x` in the order (`belowP`, equal to
  `Below_G(x)` of `rk_NG` for the representative `x` of the cluster of `y`,
  `belowP_eq_of_mem_clusterG`, `belowP_eq_belowG`).

At the event bits of `t ≥ 0` the context is the context `ctxOf M G_t` of the relation
`G_t = {(e, f) : v_f - v_e ≤ t}` (`evCtxV_eq`): the set `PO_t`, the clusters, the order of the
clusters within components (`OrdP`, `ordP_iff`) and the ranks of the sets `Below(x)`, by
`Events.mem_PO_iff`, `Events.sameCluster_iff` and `Events.ord_iff`.

**The exchange test of `y`** (Step 2; `locB`, `locB_impl`,
`locCost m s = s + 2m + 18⌈log₂(m+1)⌉ + popCost m + 3 ≤ s + 42(m + 1)` gates per test):
`[y ∈ PO]` and `r(Below(y) ∪ (A ∩ Lev(y))) - r(Below(y)) = |A ∩ Lev(y)|`, with `Lev(y)` the
cluster of `y` (`locV`), one rank run.  By the rank formula `rk_NG`, `r_{N_G}(A)` is the sum of
these terms over the representatives `x` of the clusters, each term is at most `|A ∩ Lev(x)|`
(`rk_union_le_add_card`), and the clusters partition `PO_G` (`clusterG_eq`, `eq_of_mem_clusterG`,
`exists_repsG`, `sum_card_inter_clusterG_le`).  So `A` is independent iff `A ⊆ PO_G` and every
term is tight, and when `A - y` is independent only the term of the cluster of `y` can fail:
the test answers every exchange question of `N_{G_t}` at the context of `G_t`, `t ≥ 0`
(`locV_exchOracle`).  `lem_observer_oracle` collects the two implementations, their sizes and
the correctness at the event bits.
-/

open Finset

namespace SignedTropical.Rainbow.Observer

open SignedTropical SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.POSL
  SignedTropical.Rainbow.Events

variable {m n : ℕ} {M : Matroid (Fin m)}

/-! ### The context of a relation -/

/-- The order of Step 1 read from `G`: `x`, `y` lie in one component, `x ∈ PO_G`, and `y ∉ PO_G`
or `x`, `y` lie in different clusters with `(x, y) ∉ G`.  At `G = G_t`, `t ≥ 0`, this is
`u_G(x) < u_G(y)` within a component (`ordP_iff`). -/
def OrdP (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) (x y : Fin m) : Prop :=
  connRel M x y ∧ x ∈ POG M G ∧
    (y ∉ POG M G ∨ (¬SameCluster M (POG M G) (linkG G) x y ∧ (x, y) ∉ G))

open Classical in
/-- `Below(x)`: the elements below `x` in the order of Step 1. -/
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
  /-- The order bits of Step 1. -/
  ord : Fin m → Fin m → Bool
  /-- The ranks `r(Below(x))`. -/
  rkb : Fin m → ℕ

open Classical in
/-- **The context of a relation `G`**: `PO_G`, the clusters, the order of Step 1, and the ranks of
the sets `Below(x)`. -/
noncomputable def ctxOf (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Ctx m where
  po f := decide (f ∈ POG M G)
  cl x y := decide (SameCluster M (POG M G) (linkG G) x y)
  ord x y := decide (OrdP M G x y)
  rkb x := rk M (belowP M G x)

/-! ### The values computed by the circuits -/

/-- Step 2, the ranks of the sets `{y : Ord y x}`. -/
noncomputable def rkbV (M : Matroid (Fin m)) (Ord : Fin m → Fin m → Bool) (x : Fin m) : ℕ :=
  rk M (univ.filter fun y => Ord y x = true)

open Classical in
/-- **The context read from the event bits** `X` (Step 1): the bits of `PO` are the entry bits
(`false` at a loop), the cluster bits are the merge bits within components (the bit of `PO` on
the diagonal), the order bits are `P_x ∧ ¬X(qU x y)` within components, and the ranks are those
of the sets `{y : ord y x}`. -/
noncomputable def evCtxV (M : Matroid (Fin m)) (X : Fin (qn m) → Bool) : Ctx m :=
  let P : Fin m → Bool := fun x => if x ∈ M.closure ∅ then false else X (qT x)
  let Ord : Fin m → Fin m → Bool := fun x y => if Kr M x y then P x && !X (qU x y) else false
  ⟨P, fun x y => if x = y then P x else if Kr M x y then X (qB x y) else false, Ord, rkbV M Ord⟩

/-- Step 2, the rank query of the exchange test of `y`, at a context `D` and a set `A'`:
`r({z : D.ord z y} ∪ A') - D.rkb y`. -/
noncomputable def locRankV (M : Matroid (Fin m)) (y : Fin m) (P : Ctx m × (Fin m → Bool)) : ℕ :=
  rk M (univ.filter fun z => (P.1.ord z y || P.2 z) = true) - P.1.rkb y

/-- **Step 2, the exchange test of `y`** at a context `D` and a set `A`: `[y ∈ PO]` and the rank
query at `A' = A ∩ {z : D.cl y z}`, fitted to `⌈log₂(m+1)⌉` bits, equals `|A'|`
(`indepOfRankV` of `BoolAlg/Count.lean`).  At the context of `G_t`, `t ≥ 0`, this is
`[y ∈ PO_G] ∧ [r(Below(y) ∪ (A ∩ Lev(y))) - r(Below(y)) = |A ∩ Lev(y)|]` (`locV_ctxOf`). -/
noncomputable def locV (M : Matroid (Fin m)) (y : Fin m) (P : Ctx m × (Fin m → Bool)) : Bool :=
  P.1.po y && indepOfRankV (locRankV M y) (P.1, fun z => P.2 z && P.1.cl y z)

/-! ### The order of Step 1 and the sets `Below(x)` -/

section Order

variable {G : Finset (Fin m × Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y : Fin m}

/-- **The order bits of Step 1** (Lemma `lem:observer`, Step 1, with `uG_lt_uG_iff`): at
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

/-! ### Step 2: the exchange tests -/

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
  rw [h1, h2, Nat.mod_eq_of_lt (by
    rw [show (ctxOf M G).rkb y = rk M (belowP M G y) from rfl]; exact h3)]
  rfl

open Classical in
/-- **Lemma `lem:observer`, Step 2, the exchange tests are correct**: at the context of `G_t`,
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

end Local

/-! ### Step 1: the context from the event bits is the context of `G_t` -/

section EventContext

variable {v : Fin m → ℝ} {t : ℝ}

open Classical in
/-- The bits of `PO_t` from the entry bits. -/
theorem evPO_eq (ht : 0 ≤ t) (x : Fin m) :
    (if x ∈ M.closure ∅ then false else decide (Qv M v (qT x) ≤ t)) =
      decide (x ∈ POG M (Gt v t)) := by
  rw [← PO_eq_POG, Qv_qT, tz]
  by_cases hx : x ∈ M.closure ∅
  · rw [if_pos hx, eq_comm, decide_eq_false_iff_not]
    exact notMem_PO_of_loop hx
  · rw [if_neg hx, if_neg hx]
    exact decide_eq_decide.2 (mem_PO_iff hx ht).symm

open Classical in
/-- The order bits of `G_t` from the event bits. -/
theorem evOrd_eq (ht : 0 ≤ t) (x y : Fin m) :
    (if Kr M x y then (if x ∈ M.closure ∅ then false else decide (Qv M v (qT x) ≤ t)) &&
        !decide (Qv M v (qU x y) ≤ t) else false) = decide (OrdP M (Gt v t) x y) := by
  rw [evPO_eq ht]
  unfold OrdP
  rw [← PO_eq_POG, ← near_eq_linkG]
  by_cases hK : Kr M x y
  · rw [if_pos hK, Qv_qU, uq, if_pos hK, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      mem_Gt]
    rw [ord_iff ht hK, mem_PO_iff hK.2.1 ht]
    exact ⟨fun h => ⟨hK.1, h⟩, fun h => h.2⟩
  · rw [if_neg hK, eq_comm, decide_eq_false_iff_not]
    rintro ⟨hxy, hx, -⟩
    have hx' : x ∉ M.closure ∅ := fun h => notMem_PO_of_loop h hx
    by_cases he : x = y
    · subst he
      exact hK (Kr.refl hx')
    · exact hK (kr_of_connRel hxy he)

open Classical in
/-- **Step 1**: at the event bits of `t ≥ 0`, the context computed from the bits is the context of
`G_t`. -/
theorem evCtxV_eq (ht : 0 ≤ t) :
    evCtxV M (fun j => decide (Qv M v j ≤ t)) = ctxOf M (Gt v t) := by
  have hord : (fun x y => if Kr M x y then
      (if x ∈ M.closure ∅ then false else decide (Qv M v (qT x) ≤ t)) &&
        !decide (Qv M v (qU x y) ≤ t) else false) = fun x y => decide (OrdP M (Gt v t) x y) :=
    funext fun x => funext fun y => evOrd_eq ht x y
  refine Ctx.ext (funext fun x => evPO_eq ht x) (funext fun x => funext fun y => ?_) hord ?_
  · show (if x = y then _ else _) = decide (SameCluster M (POG M (Gt v t)) (linkG (Gt v t)) x y)
    rw [← PO_eq_POG, ← near_eq_linkG]
    by_cases he : x = y
    · subst he
      rw [if_pos rfl, evPO_eq ht, ← PO_eq_POG]
      exact decide_eq_decide.2 ⟨SameCluster.refl, SameCluster.mem_left⟩
    · rw [if_neg he]
      by_cases hK : Kr M x y
      · rw [if_pos hK]
        simp only [Qv_qB, bq, if_pos hK]
        exact decide_eq_decide.2 ⟨fun h => (sameCluster_iff ht).2 ⟨hK, h⟩,
          fun h => ((sameCluster_iff ht).1 h).2⟩
      · rw [if_neg hK, eq_comm, decide_eq_false_iff_not]
        exact fun h => hK ((sameCluster_iff ht).1 h).1
  · show rkbV M _ = fun x => rk M (belowP M (Gt v t) x)
    rw [hord]
    funext x
    rw [rkbV, belowP]
    congr 1
    ext y
    simp

end EventContext

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

/-- Step 2, the ranks of the sets `{y : Ord y x}`, from `Ord`. -/
def rkbB (Ord : Fin m → Fin m → Arg n) : Bld BoolOp n (Fin m → List (Arg n)) :=
  tabB fun x => rankB C fun y => Ord y x

/-- The order bit of one pair, two gates: `P ∧ ¬u`. -/
def andNotB : Arg n × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB Prod.fst) fun p => emit .not p.2 .const) fun q => emit .and q.1 q.2

open Classical in
/-- The operand of the bit of `PO` at `x`: the entry bit, and `false` at a loop. -/
noncomputable def poArg (X : Fin (qn m) → Arg n) (x : Fin m) : Arg n :=
  if x ∈ M.closure ∅ then .const else X (qT x)

open Classical in
/-- The order bits within components, from the event bits: `P_x ∧ ¬X(qU x y)`, two gates per
pair, and the constant `false` outside the components. -/
noncomputable def ordsB (X : Fin (qn m) → Arg n) : Bld BoolOp n (Fin m → Fin m → Arg n) :=
  fun gs =>
    let p := (tabB fun x => tabB fun y => andNotB (poArg M X x, X (qU x y))) gs
    (p.1, fun x y => if Kr M x y then p.2 x y else .const)

open Classical in
/-- **The context from the event bits** (Step 1): the bits of `PO` and the cluster bits are chosen
from the event bits (no gate), the order bits within components cost two gates each, then the
ranks of the sets `Below(x)`, one rank query each. -/
noncomputable def evCtxB : (Fin (qn m) → Arg n) → Bld BoolOp n (CtxA m n) :=
  seqB (pairB (pureB fun X => X) (seqB (ordsB M) (pairB (pureB fun O => O) (rkbB C))))
    (pureB fun q => ⟨poArg M q.1, fun x y => if x = y then poArg M q.1 x
      else if Kr M x y then q.1 (qB x y) else .const, q.2.1, q.2.2⟩)

/-! #### Step 2, the exchange tests -/

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

/-- **Step 2, the ranks of the sets `Below(x)`**, `ms` gates. -/
theorem rkbB_impl :
    Impl (relR m) (Rep.pi (Fin m) (numR (n := n) (Nat.size m))) (rkbB C) (m * C.size)
      (rkbV M) :=
  Impl.tab fun x => (rankB_impl hB).pre (R := relR m) (g := fun O y => O y x)
    (G := fun O y => O y x) fun _ _ _ hs y => hs y x

omit hB in
/-- `P ∧ ¬u`, two gates. -/
theorem andNotB_impl :
    Impl (bitR.prod bitR) (bitR (n := n)) andNotB 2 (fun P => P.1 && !P.2) :=
  ((Impl.fst.pair (emitNot_impl.pre (R := bitR.prod bitR) (g := Prod.snd) (G := Prod.snd)
    fun _ _ _ hs => hs.2)).comp emitAnd_impl).cost (by norm_num)

omit hB in
open Classical in
theorem poArg_rep {gs : List (Gate BoolOp n)} {X : Fin (qn m) → Arg n}
    {T : (Fin n → Bool) → Fin (qn m) → Bool} (hX : (vecR (qn m)).rep gs X T) :
    (vecR m).rep gs (poArg M X) fun z => (evCtxV M (T z)).po := fun x => by
  unfold poArg
  split_ifs with h
  · exact Rep.congr bitR (den_const gs) fun z => by simp [evCtxV, h, boolInterp]
  · exact Rep.congr bitR (hX (qT x)) fun z => by simp [evCtxV, h]

omit hB in
open Classical in
theorem clArg_rep {gs : List (Gate BoolOp n)} {X : Fin (qn m) → Arg n}
    {T : (Fin n → Bool) → Fin (qn m) → Bool} (hX : (vecR (qn m)).rep gs X T) :
    (relR m).rep gs (fun x y => if x = y then poArg M X x else if Kr M x y then X (qB x y)
      else .const) fun z => (evCtxV M (T z)).cl := fun x y => by
  by_cases he : x = y
  · subst he
    simp only [if_true]
    exact Rep.congr bitR (poArg_rep hX x) fun z => by simp [evCtxV]
  · simp only [he, if_false]
    by_cases hK : Kr M x y
    · simp only [hK, if_true]
      exact Rep.congr bitR (hX (qB x y)) fun z => by simp [evCtxV, he, hK]
    · simp only [hK, if_false]
      exact Rep.congr bitR (den_const gs) fun z => by simp [evCtxV, he, hK, boolInterp]

omit hB in
open Classical in
/-- The order bits within components, `2m²` gates. -/
theorem ordsB_impl :
    Impl (vecR (qn m)) (relR (n := n) m) (ordsB M) (m * (m * 2)) fun T => (evCtxV M T).ord := by
  intro gs X T hX
  obtain ⟨hp, hl, hr⟩ := (Impl.tab (R := vecR (qn m)) fun x => Impl.tab fun y =>
    andNotB_impl.pre (R := vecR (qn m)) (g := fun X => (poArg M X x, X (qU x y)))
      (G := fun T => ((evCtxV M T).po x, T (qU x y)))
      fun _ _ _ hs => ⟨poArg_rep hs x, hs (qU x y)⟩) hX
  refine ⟨hp, hl, fun x y => ?_⟩
  show Den boolInterp _ (if Kr M x y then _ else .const) _
  by_cases hK : Kr M x y
  · rw [if_pos hK]
    exact Rep.congr bitR (hr x y) fun z => by simp [evCtxV, hK]
  · rw [if_neg hK]
    exact Rep.congr bitR (den_const _) fun z => by simp [evCtxV, hK, boolInterp]

open Classical in
/-- **The context from the event bits** (Lemma `lem:observer`, Step 1, and the part of Step 2
independent of the set): `evCtxB` computes `evCtxV` with `m(2m + s)` gates. -/
theorem evCtxB_impl :
    Impl (vecR (qn m)) (ctxR (n := n) m) (evCtxB M C) (m * (m * 2) + m * C.size) (evCtxV M) :=
  (((Impl.self (R := vecR (qn m))).pair ((ordsB_impl (M := M)).comp
    ((Impl.self (R := relR m)).pair (rkbB_impl hB)))).comp
    (Impl.free (R₁ := (vecR (qn m)).prod ((relR m).prod (Rep.pi (Fin m) (numR (Nat.size m)))))
      (R₂ := ctxR m)
      (g := fun q => ⟨poArg M q.1, fun x y => if x = y then poArg M q.1 x
        else if Kr M x y then q.1 (qB x y) else .const, q.2.1, q.2.2⟩)
      (F := fun t => ⟨(evCtxV M t.1).po, (evCtxV M t.1).cl, t.2.1, t.2.2⟩)
      fun _ _ _ hs => ⟨poArg_rep hs.1, clArg_rep hs.1, hs.2.1, hs.2.2⟩)).cost (by ring)
    |>.congr fun _ => rfl

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

/-- **The exchange test of `y`** (Lemma `lem:observer`, Step 2): from a context `D` and a set `A`,
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
/-- One exchange test costs `s + O(m)` gates; explicitly at most `s + 42(m + 1)`. -/
theorem locCost_le (m s : ℕ) : locCost m s ≤ s + 42 * (m + 1) := by
  have hW := size_le_self m
  have hp := popCost_le m
  unfold locCost
  omega

open Classical in
/-- **Lemma `lem:observer`, Steps 1 and 2.**  Let `M` have ground set `E = Fin m`, and let the
Boolean circuit `C` of size `s` output the binary digits of the rank of `M`.  Then:

1. a circuit of `m(2m + s)` gates computes, from the event bits, the context `evCtxV M`, which at
   the event bits of `t ≥ 0` is the context of `G_t` (`evCtxV_eq`);
2. for each `y`, a circuit of `locCost m s ≤ s + 42(m + 1)` gates computes, from a context `D`
   and a set `A ⊆ E`, the bit `locV M y (D, A)`;
3. at the event bits of `t ≥ 0`, for every `v`, these tests answer the exchange questions of
   `N_{G_t}`: for `y ∈ A` with `A - y` independent, the bit is `[A independent in N_{G_t}]`. -/
theorem lem_observer_oracle (hE : M.E = Set.univ) :
    Impl (vecR (qn m)) (ctxR (n := n) m) (evCtxB M C) (m * (m * 2) + m * C.size) (evCtxV M) ∧
      (∀ y, Impl ((ctxR m).prod (vecR m)) (bitR (n := n)) (locB C y) (locCost m C.size)
        (locV M y)) ∧
      locCost m C.size ≤ C.size + 42 * (m + 1) ∧
      ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        MI.ExchOracle (fun y => locV M y) (NG M (Gt v t))
          (evCtxV M fun j => decide (Qv M v j ≤ t)) :=
  ⟨evCtxB_impl hB, locB_impl hB, locCost_le _ _, fun _ _ ht => by
    rw [evCtxV_eq ht]
    exact locV_exchOracle hE ht⟩

end Circuits

end SignedTropical.Rainbow.Observer
