# P4: PO-SL (Definition `def:posl`, Proposition `prop:posl`, the rank of `N_G`)

Natural-language companion of `SignedTropical/Rainbow/POSL.lean` and
`SignedTropical/Rainbow/POSLRank.lean`, namespace `SignedTropical.Rainbow.POSL`.  Source:
`daishu/paper/greedy_intersection.tex`, Section 4.5 (Definition `def:posl`, Proposition
`prop:posl`, Steps 1 to 5 of its proof) and Lemma `lem:observer`, Steps 1, 2, 3 and 5 (the
mathematical content, not the circuit); the referee-corrected Steps 1 to 3 are in
`daishu/docs/phase2a-rainbow-2026-10-11.md`, Section 4.2.

Build status: `lake build SignedTropical.Rainbow.POSL` and `lake build
SignedTropical.Rainbow.POSLRank` succeed with no error and no warning.  No `sorry`, `admit`,
`axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.  Every theorem below
depends only on `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`).

Imports: `Rainbow/PossiblyOptimal.lean` (coordinator: `theta_le_iff`, `tfae_pos`,
`mem_pos_zero`, `mem_of_mem_fundCircuit`), `Rainbow/MinBases.lean` (P0a),
`Rainbow/Connectivity.lean` (P0b), and, in `POSLRank.lean`, Phase 1's `Subtractionfree.lean`
for `rk_mono`.  The 144-line draft of the first run duplicated Lemma `lem:minbases`(3) before
P0a existed; it was replaced, and only its induction on the value (`value_induction`) was kept.


## Notation

`E = Fin m`, `M` a matroid on `E` with ground set `E` (hypothesis `hE`), `v : E → ℝ`, `t ∈ ℝ`.
`cl` is `M.closure`, `r` is `rk M`, `C(B, e)` is `M.fundCircuit e B`, `K_e` is the component
`Conn.comp M e` of `e`, and `connRel M x y` says that `x` and `y` lie in one component (equal or
on a common circuit, P0b).  `M^w = minBases M w`, whose bases are the minimum bases of `w`
(P0a, `isBase_minBases_iff`).  `P_t = Pos M v t`.

**Single linkage, generic** (`P ⊆ E`, a link predicate `J`, an order predicate `L`):

* `Link M P J x y`: `x, y ∈ P`, `connRel M x y`, `J x y`.
* `SameCluster M P J x y`: `x ∈ P` and a chain of links, possibly empty, leads from `x` to `y`
  (`x ∈ P ∧ ReflTransGen (Link M P J) x y`); `cluster M P J x` is the set of such `y`.
* `lowerSet M P J L e`: the `y ∈ P` with `connRel M y e`, `y` outside the cluster of `e`, and
  `L y e`.
* `clusterRank M P J L e`: `#{cluster y : y ∈ lowerSet M P J L e} + 1` for `e ∈ P`, `m + 1`
  for `e ∉ P`.

**Definition `def:posl`.**

* `PO M v t = {f : f ∉ cl{g : v_g < v_f - t}}` (strict inequality);
* `near v t x y : |v_x - v_y| ≤ t` (non-strict), the links; the clusters at scale `t` are the
  classes of `SameCluster M (PO M v t) (near v t)`;
* `u M v t = clusterRank M (PO M v t) (near v t) (fun y e => v_y < v_e)`, with values in `ℕ`;
* `N M v t = minBases M (fun e => (u M v t e : ℝ))`, that is `N(t) = M^{u_t}`.

**The relation `G`.**  For `G : Finset (E × E)`:

* `POG M G = {f : f ∉ cl{g : (g, f) ∉ G}}`;
* `linkG G x y : (x, y) ∈ G ∧ (y, x) ∈ G`;
* `uG M G = clusterRank M (POG M G) (linkG G) (fun y e => (y, e) ∉ G)`;
* `NG M G = minBases M (fun e => (uG M G e : ℝ))`;
* `Gt v t = {(e, f) : v_f - v_e ≤ t}`; `levels v = {0} ∪ {|v_e - v_f| : e, f ∈ E}`.

Every set in the definition of `N_G` is a formula in `G`, the relation `connRel M` (the fixed
components of `M`) and the closure of `M`, which rank queries decide (`mem_POG_iff`).


## 1. Results

### 1.1 The facts stated in Definition `def:posl`

In this section `P ⊆ E` is arbitrary and the links are `near v t`; in Definition `def:posl`,
`P = PO_t`.

**Proposition 1.**  `SameCluster.refl`, `.of_link`, `.mem_left`, `.mem_right`, `.conn`,
`.trans`, `.symm`, `mem_cluster`.  `SameCluster` is reflexive on `P`, symmetric (for symmetric
links), transitive, relates only elements of `P`, and only elements of one component.

*Proof.*  Step 1, a nonempty chain ends with a link, whose second end lies in `P`.  Step 2, each
link joins elements of one component, and `connRel` is transitive (P0b).  Step 3, reversing a
chain of symmetric links gives a chain.

**Proposition 2.**  `sameCluster_iff_transGen`.  For `t ≥ 0`, `SameCluster M P (near v t) x y`
holds iff `(x, y)` lies in the transitive closure of the links.  So the clusters are the classes
of the transitive closure, as in the definition.

*Proof.*  Step 1, for `x ∈ P` the link `x, x` exists since `|v_x - v_x| = 0 ≤ t`; prepending it
makes a chain nonempty.  Step 2, a nonempty chain starts with a link, whose first end lies in
`P`.

**Proposition 3 (clusters are intervals).**  `SameCluster.of_le_of_le`.  Let `t ≥ 0`, let `x`
and `z` lie in one cluster, and let `y ∈ P` lie in the component of `x` with
`v_x ≤ v_y ≤ v_z`.  Then `y` lies in the cluster of `x`.

*Proof.*  Induction on the chain from `x` to `z`.  Step 1, empty chain: `z = x`, so `v_y = v_x`
and `x`, `y` are linked.  Step 2, a chain from `x` to `w` followed by a link `w, z`: if
`v_y ≤ v_w`, the induction hypothesis applies; otherwise `0 < v_y - v_w ≤ v_z - v_w ≤ t`, and
`w`, `y` lie in `P` and in the component of `x`, so the link `w, y` extends the chain.

**Proposition 4 (consecutive values).**  `SameCluster.exists_link`, `SameCluster.sub_le`.
(a) If `x` and `z` lie in one cluster and `v_x ≤ c < v_z`, some link of the cluster crosses `c`:
there are `a`, `b` in the cluster with `v_a ≤ c < v_b` and `v_b - v_a ≤ t`.  (b) If `x` and `z`
lie in one cluster, `v_x < v_z`, and no element of the cluster has a value strictly between, then
`v_z - v_x ≤ t`.

*Proof.*  Step 1, (a) by induction on the chain: the empty chain is excluded by
`v_x ≤ c < v_x`; for a chain to `w` followed by a link `w, z`, either `c < v_w` and the
induction hypothesis applies, or `v_w ≤ c < v_z` and the link `w, z` crosses `c`.  Step 2, (b):
apply (a) at `c = v_x`; then `v_x < v_b`, so `v_z ≤ v_b` by hypothesis, and
`v_z - v_x ≤ v_b - v_a ≤ t`.

**Proposition 5 (separation and order).**  `lt_abs_sub`, `lt_sub_of_not_sameCluster`.  Let `x`
and `y` lie in one component and in different clusters, `x'` in the cluster of `x` and `y'` in
the cluster of `y`.  (a) `|v_{x'} - v_{y'}| > t`.  (b) If `t ≥ 0` and `v_x < v_y`, then
`v_{y'} - v_{x'} > t`: two clusters of a component differ by more than `t`, so they are ordered.

*Proof.*  Step 1, (a): otherwise `x'` and `y'`, which lie in `P` and in one component, are
linked, and `x, x', y', y` lie in one cluster.  Step 2, `v_{x'} < v_y`: otherwise
`v_x < v_y ≤ v_{x'}`, and Proposition 3 puts `y` in the cluster of `x`.  Step 3,
`v_{x'} < v_{y'}`: otherwise `v_{y'} ≤ v_{x'} < v_y`, and Proposition 3, applied to the cluster
of `y` from `y'` to `y`, puts `x'` in the cluster of `y`.  Step 4, (a) and Step 3 give (b).

**Proposition 6 (`u_t` is the rank of the cluster).**  `lowerSet_eq`, `image_lowerSet_ssubset`,
`clusterRank_eq_of_sameCluster`, `clusterRank_lt_of_lt`, and for `u`: `u_of_notMem`,
`one_le_u`, `u_le_iff_mem`, `u_le_succ`, `u_eq_u_of_sameCluster`, `u_le_u_iff`, `u_eq_u_iff`,
`u_lt_u_iff`, `u_eq_card_add_one`.  Let `t ≥ 0`.

(a) `u_t(e) ≤ m` iff `e ∈ PO_t`, and `u_t(e) = m + 1` for `e ∉ PO_t`.
(b) For `x, y ∈ PO_t` in one component: `u_t(x) ≤ u_t(y)` iff `x`, `y` share a cluster or
`v_x < v_y`; `u_t(x) = u_t(y)` iff they share a cluster; `u_t(x) < u_t(y)` iff they lie in
different clusters and `v_x < v_y`.
(c) For `x`, `y` in one component: `u_t(x) < u_t(y)` iff `x ∈ PO_t ∌ y`, or `x, y ∈ PO_t` lie in
different clusters with `v_x < v_y`.
(d) For `e ∈ PO_t`, `u_t(e) - 1` is the number of clusters of the component of `e` all of whose
values are smaller than all values of the cluster of `e`.

*Proof.*  Write `L(e)` for `lowerSet` with the order `v_y < v_e`.  Step 1, (a): `L(e)` misses
`e`, so it has at most `m - 1` elements, and so do their clusters.  Step 2, if `x`, `y` share a
cluster, `L(x) = L(y)`: for `z ∈ L(x)`, `z` is not in the cluster of `y`, and Proposition 5(b)
for `z` and `x`, with `y` in the cluster of `x`, gives `v_y - v_z > t ≥ 0`.  Step 3, if `x`, `y`
lie in different clusters with `v_x < v_y`, the clusters of `L(x)` form a proper subset of those
of `L(y)`: `L(x) ⊆ L(y)`, since a `z ∈ L(x)` in the cluster of `y` would give
`v_x - v_y > t ≥ 0` by Proposition 5(b); and the cluster of `x ∈ L(y)` is the cluster of no
`z ∈ L(x)`.  Step 4, (b): Steps 2 and 3, and if `v_x = v_y` then `x`, `y` are linked.  Step 5,
(c): (a) and (b).  Step 6, (d): a cluster `cluster y`, `y ∈ L(e)`, lies below the cluster of `e`
by Proposition 5(b); conversely, if every value of `C = cluster y` is below every value of the
cluster of `e`, then `v_y < v_e`, and `y` is not in the cluster of `e`, else `v_e < v_e`.

**Proposition 7.**  `SameCluster.eq_of_scale_zero`, `SameCluster.mono`.  At scale `0` a cluster
has one value.  Clusters grow with `P` and `t`.

### 1.2 `PO_t`

**Lemma 8.**  `value_induction`, `PO_mono`, `subset_PO_of_isMinBase`, `mem_PO_zero_iff`,
`mem_closure_PO`, `subset_PO_of_isMinBase_u`, `isBase_N_iff`, `subset_PO_of_isBase_N`,
`subset_PO_of_isBase_minBases`, `notMem_closure_empty`.

(a) `PO_t ⊆ PO_{t'}` for `t ≤ t'`.
(b) For `t ≥ 0`, every minimum base of `v` lies in `PO_t`.
(c) `PO_0` is the set of elements of minimum bases of `v`.
(d) For `t ≥ 0`, every `e` lies in `cl(PO_t ∩ K_e)`.
(e) For `t ≥ 0`, every minimum base of `u_t` (every base of `N(t)`) lies in `PO_t`.

*Proof.*  Step 1, (a): `{g : v_g < v_f - t'} ⊆ {g : v_g < v_f - t}`.  Step 2, (b): by (a) take
`t = 0`.  For `f ∈ B`, `B ∩ {v < v_f}` is a basis of `{v < v_f}` (P0a,
`IsMinBase.isBasis_lt`), so `cl{v < v_f} ⊆ cl(B - f)`, which misses `f` since `B` is
independent.  Step 3, (c): let `f ∈ PO_0` and `B` a minimum base with `f ∉ B`.  If every
`g ≠ f` of `C(B, f)` had `v_g < v_f`, then `f ∈ cl(C(B, f) - f) ⊆ cl{v < v_f}`.  So some
`g ∈ C(B, f) - f` has `v_g ≥ v_f`, and `v_g ≤ v_f` (Lemma `lem:minbases`(1)); then `B - g + f`
is a minimum base containing `f` (Lemma `lem:minbases`(3), P0a
`IsMinBase.isMinBase_exchange_iff`).  Step 4, (d): a minimum base `B` of `v` spans `e`, so
`e ∈ cl(B ∩ K_e)` (P0b, `mem_closure_iff_comp`), and `B ⊆ PO_t` by (b).  Step 5, (e): by
Proposition 6(a) `{u_t ≤ m} = PO_t`, so Lemma `lem:minbases`(2) (P0a,
`IsMinBase.subset_closure_le`) gives `PO_t ⊆ cl(B ∩ PO_t)`; by (d) every `f` lies in
`cl(B ∩ PO_t)`; an `f ∈ B - PO_t` would lie in `cl(B - f)`.

### 1.3 Proposition `prop:posl`

**Theorem 9 ((F3)).**  `isBase_N_of_mem_Pos`.  Every `B ∈ P_t` is a base of `N(t)`.

*Proof.*  Step 1, `t ≥ θ(B) ≥ 0`.  Step 2, `B ⊆ PO_t`: for `f ∈ B` and `v_g < v_f - t`,
Proposition `prop:pos`(4) (`Pos.tfae_pos`) gives `g ∈ cl(B ∩ {v ≤ v_g + t}) ⊆ cl(B - f)`, as
`v_g + t < v_f`; so `cl{g : v_g < v_f - t} ⊆ cl(B - f)`, which misses `f`.  Step 3, let `e ∉ B`
and `f ∈ C(B, e)`, `f ≠ e`; then `f ∈ B ⊆ PO_t`, and `f`, `e` lie in one component (P0b,
`fundCircuit_subset_comp`).  If `e ∉ PO_t`, `u_t(f) ≤ m + 1 = u_t(e)`.  If `e ∈ PO_t` and
`v_f < v_e`, Proposition 6(b) gives `u_t(f) ≤ u_t(e)`.  If `e ∈ PO_t` and `v_f ≥ v_e`, then
`v_f - v_e ≤ θ(B) ≤ t` (`Pos.theta_le_iff`), so `f`, `e` are linked and `u_t(f) = u_t(e)`.
Step 4, Lemma `lem:minbases`(1) (P0b, `isMinBase_of_forall_fundCircuit`) makes `B` minimum for
`u_t`, a base of `M^{u_t}` (P0a, `isBase_minBases_iff`).

**Theorem 10 ((F1)).**  `N_zero`.  `N(0) = M^v`.

*Proof.*  Step 1, it suffices that `u_0` and `v` have the same minimum bases (`minBases_ext`).
Step 2, a minimum base of `v` lies in `P_0` (`Pos.mem_pos_zero`), so it is minimum for `u_0` by
Theorem 9.  Step 3, let `B` be minimum for `u_0`; `B ⊆ PO_0` (Lemma 8(e)).  By induction on the
value (`value_induction`), `e ∈ cl(B ∩ {v ≤ v_e})` for every `e`.  If `e ∈ B`, this is clear.
If `e ∈ PO_0 - B`, every `f ≠ e` of `C(B, e)` lies in `B ⊆ PO_0`, in the component of `e`,
with `u_0(f) ≤ u_0(e)` (Lemma `lem:minbases`(1)); by Proposition 6(b), `f` and `e` share a
cluster at scale `0`, so `v_f = v_e` (Proposition 7), or `v_f < v_e`; so
`C(B, e) - e ⊆ B ∩ {v ≤ v_e}`, which spans `e`.  If `e ∉ PO_0`, `e ∈ cl{g : v_g < v_e}`, and by
induction each such `g` lies in `cl(B ∩ {v ≤ v_g}) ⊆ cl(B ∩ {v ≤ v_e})`.  Step 4, a base with
this property is minimum for `v` (P0a, `isMinBase_of_forall_mem_closure`).

**Theorem 11 ((F2)).**  `isBase_N_mono`.  For `0 ≤ t ≤ t'`, every base of `N(t)` is a base of
`N(t')`.

*Proof.*  Step 1, `B` is minimum for `u_t` and `B ⊆ PO_t` (Lemma 8(e)).  Let `e ∉ B` and
`f ∈ C(B, e)`, `f ≠ e`; then `f ∈ B ⊆ PO_t ⊆ PO_{t'}` and `f`, `e` lie in one component.  We
show `u_{t'}(f) ≤ u_{t'}(e)`.  Step 2, if `e ∉ PO_{t'}`, `u_{t'}(e) = m + 1`.  Step 3, if
`e ∈ PO_t`, then `u_t(f) ≤ u_t(e)` (Lemma `lem:minbases`(1)), that is (Proposition 6(b)) `f`, `e`
share a cluster at `t` or `v_f < v_e`; both persist at `t'` (Proposition 7), so
`u_{t'}(f) ≤ u_{t'}(e)`.  Step 4, if `e ∈ PO_{t'} - PO_t` and `v_f ≤ v_e`: `v_f < v_e`, or
`v_f = v_e` and `f`, `e` are linked at `t'`.  Step 5, let `e ∈ PO_{t'} - PO_t` and `v_e < v_f`,
`K` the component of `e`, and `Z` the set of `h ∈ B` with `u_t(h) ≤ u_t(x)` for some
`x ∈ PO_t ∩ K` with `v_x < v_e - t`.  By induction on the value, every `g ∈ K` with
`v_g < v_e - t` lies in `cl(Z)`: if `g ∈ B`, then `g ∈ PO_t` and `g ∈ Z` (take `x = g`); if
`g ∈ PO_t - B`, every `h ≠ g` of `C(B, g)` lies in `B` with `u_t(h) ≤ u_t(g)`, so in `Z`, and
`g ∈ cl(C(B, g) - g)`; if `g ∉ PO_t`, then `g ∈ cl{h ∈ K : v_h < v_g - t}` (Lemma
`lem:minbases`(4)), and every such `h` has `v_h < v_g` and `v_h < v_e - t`.  Step 6, `e ∉ PO_t`
gives `e ∈ cl{g ∈ K : v_g < v_e - t} ⊆ cl(Z)`; as `Z ⊆ B`, `C(B, e) ⊆ Z + e` (P0a,
`fundCircuit_subset_insert_of_mem_closure`), so `f ∈ Z`: `u_t(f) ≤ u_t(x)` for some
`x ∈ PO_t ∩ K` with `v_x < v_e - t`.  Step 7, `v_x < v_e - t ≤ v_e < v_f`, so by
Proposition 6(b) `f` and `x` share a cluster at `t`, hence at `t'`; `e ∈ PO_{t'}` lies in `K`
with `v_x ≤ v_e ≤ v_f`, so Proposition 3 at scale `t'` puts `e` in that cluster and
`u_{t'}(f) = u_{t'}(e)`.  Step 8, Lemma `lem:minbases`(1) makes `B` minimum for `u_{t'}`.

**Theorem 12 ((F4)).**  `N_eq_self`.  If `v_f - v_e ≤ t` for all `e, f`, then `N(t) = M`.

*Proof.*  Step 1, `t ≥ 0` (take `e = f`).  Step 2, by P0a's `minBases_eq_self` it suffices that
`u_t(e) = u_t(f)` whenever `e ≠ f` lie on a common circuit `C`.  Step 3,
`{g : v_g < v_e - t} = ∅`, so `e ∈ PO_t` iff `e` is not a loop; and `e` is not a loop, since
`{e}` would then be a circuit inside `C`, hence equal to `C`, which contains `f`
(`notMem_closure_empty`).  The same holds for `f`.  Step 4, `|v_e - v_f| ≤ t`, so `e`, `f` are
linked and `u_t(e) = u_t(f)`.

**Theorem 13 ((F5)).**  `PO_eq_of_levels`, `near_eq_of_levels`, `N_eq_N_of_levels`.  If
`0 ≤ t ≤ t'` and no element of `levels v = {0} ∪ {|v_e - v_f|}` lies in `(t, t']`, then
`PO_t = PO_{t'}`, the links at `t` and `t'` agree, and `N(t) = N(t')`.

*Proof.*  Step 1, if `v_g < v_f - t` but `v_g ≥ v_f - t'`, then `t < v_f - v_g ≤ t'` and
`v_f - v_g = |v_f - v_g|` is a level in `(t, t']`; so the sets `{g : v_g < v_f - t}` and
`{g : v_g < v_f - t'}` agree.  Step 2, likewise `|v_x - v_y| ≤ t` iff `|v_x - v_y| ≤ t'`.
Step 3, `u_t` depends on `t` only through `PO_t` and the links.

**Theorem 14 (determined by `G_t`).**  `PO_eq_POG`, `near_eq_linkG`, `lt_iff_notMem_Gt`,
`u_eq_uG`, `N_eq_NG`, `N_eq_of_Gt_eq`, `NG_univ`.  For `t ≥ 0`, `u_t = u_{G_t}` and
`N(t) = N_{G_t}`; so `G_t(v) = G_{t'}(v')` implies `N_v(t) = N_{v'}(t')`.  At the full relation,
`N_{E × E} = M`.

*Proof.*  Step 1, `v_g < v_f - t` iff `(g, f) ∉ G_t`, so `PO_t = PO_{G_t}`.  Step 2,
`|v_x - v_y| ≤ t` iff `(x, y), (y, x) ∈ G_t`, so the links and the clusters agree.  Step 3, for
`y, e ∈ PO_t` in one component and in different clusters, `|v_y - v_e| > t` (Proposition 5(a)),
so `v_y < v_e` iff `v_e - v_y > t` iff `(y, e) ∉ G_t`.  Step 4, `clusterRank` reads its order
predicate only on such pairs (`clusterRank_congr`), so `u_t = u_{G_t}`.  Step 5, at `G = E × E`,
`PO_G` is the set of non-loops and no pair lies outside `G`, so `u_G = 1` on `PO_G`; two distinct
elements on a common circuit are non-loops, and P0a's `minBases_eq_self` gives `N_G = M`.

**Theorem 15 (Proposition `prop:posl`, first two sentences).**  `isAdmissible`, `prop_posl`.  Let
`M` have ground set `E` and a rainbow base.  For every `v`: the family `N(t)` is admissible
(`IsAdmissible M blk v (N M v)`: ground sets `E`, (F1) to (F5)); `N(t) = N(t')` whenever
`0 ≤ t ≤ t'` and no level of `levels v` lies in `(t, t']`; and `N(t) = N_{G_t}` for `t ≥ 0`.

*Proof.*  Step 1, the ground set of `M^w` is `E` (P0b, `minBases_ground`).  Step 2, (F1), (F2),
(F3) are Theorems 10, 11, 9.  Step 3, (F4): for `t ≥ T = max levels v`, `v_f - v_e ≤ |v_f - v_e|
≤ t`, so `N(t) = M` (Theorem 12), which has a rainbow base.  Step 4, (F5) with the levels
`levels v`, which contain `0`: Theorem 13.  Step 5, Theorem 14.

### 1.4 The rank of `N(t)` and of `N_G` (`POSLRank.lean`)

**Theorem 16 (equation `eq:rank-mu` within components).**  `rk_minBases_eq_sum_comp`.  For every
`w : E → ℝ` and `A ⊆ E`,
`r_{M^w}(A) = Σ_{x ∈ R} (r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x)))`, where
`Lev(x) = {y ∈ K_x : w_y = w_x}` (`compLevel`), `Below(x) = {y ∈ K_x : w_y < w_x}`
(`compBelow`), and `R` (`compReps`) is the set of least elements of the sets `Lev(x)`.  Each
difference is a difference of natural numbers with the subtrahend at most the minuend.

*Proof.*  Step 1, equation `eq:rank-mu` (P0a, `rk_minBases`):
`r_{M^w}(A) = Σ_ℓ (r(U_ℓ ∪ A_ℓ) - r(U_ℓ))` over the values `ℓ` of `w`, with `U_ℓ = {w < ℓ}`,
`A_ℓ = A ∩ {w = ℓ}`.  Step 2, rank is additive over components (P0b, `rk_eq_sum_comp`) and
monotone, so each term is `Σ_K T(ℓ, K)` with
`T(ℓ, K) = r((U_ℓ ∪ A_ℓ) ∩ K) - r(U_ℓ ∩ K)`.  Step 3, `T(ℓ, K) = 0` unless some `y ∈ A ∩ K`
has `w_y = ℓ`, and then the least element `x` of `Lev(y)` lies in `R` with `w_x = ℓ` and
`K_x = K`.  Step 4, `x ↦ (w_x, K_x)` is injective on `R`: two representatives with one value
and one component lie in each other's `Lev`, so each is at most the other.  Step 5, for
`x ∈ R`, `(U_{w_x} ∪ A_{w_x}) ∩ K_x = Below(x) ∪ (A ∩ Lev(x))` and `U_{w_x} ∩ K_x = Below(x)`.

**Theorem 17 (the rank of `N(t)`).**  `rk_N`, with `compLevel_u`, `compBelow_u`,
`rk_compBelow_union_u`, `rk_union_of_subset_closure`.  For `t ≥ 0` and `A ⊆ E`,
`r_{N(t)}(A) = Σ_x (r(Below(x) ∪ (A ∩ cluster(x))) - r(Below(x)))`, the sum over the least
element `x` of each cluster at scale `t` (`reps`), with `Below(x)` the elements of the component
of `x` with smaller `u_t` (`below`).

*Proof.*  Step 1, Theorem 16 for `w = u_t`; split the representatives by `x ∈ PO_t`.  Step 2,
for `x ∈ PO_t`, `Lev(x)` is the cluster of `x` (`u_t(y) = u_t(x) ≤ m` forces `y ∈ PO_t`, then
Proposition 6(b)), so the representatives in `PO_t` are the least elements of the clusters.
Step 3, for `x ∉ PO_t`, `Below(x) = PO_t ∩ K_x`, which spans `K_x` (Lemma 8(d)), so
`r(Below(x) ∪ (A ∩ Lev(x))) = r(Below(x))` and the term vanishes.

**Theorem 18 (the rank of `N_G` read from `G`).**  `rk_NG`, with `clusterG`, `repsG`, `belowG`,
`below_eq_belowG`.  For `G = G_t`, `t ≥ 0`, and `A ⊆ E`,
`r_{N_G}(A) = Σ_x (r(Below_G(x) ∪ (A ∩ cluster_G(x))) - r(Below_G(x)))`, the sum over the least
element `x` of each cluster of the links `linkG G` on `PO_G`, where `Below_G(x)` is the set of
`y ∈ PO_G` in the component of `x`, outside the cluster of `x`, with `(y, x) ∉ G`.

*Proof.*  Step 1, `N_{G_t} = N(t)` and the clusters agree (Theorem 14).  Step 2, for
`x ∈ PO_t`, a `y` of the component of `x` has `u_t(y) < u_t(x)` iff `y ∈ PO_t`, `y` is outside
the cluster of `x` and `v_y < v_x` (Proposition 6(c)), and `v_y < v_x` iff `(y, x) ∉ G_t`
(Theorem 14, Step 3).  Step 3, Theorem 17.

**Lemma 19 (Lemma `lem:observer`, Steps 1 and 2).**  `mem_POG_iff`, `uG_lt_uG_iff`.  (a) For every
`G`, `f ∈ PO_G` iff `r({g : (g, f) ∉ G}) < r({g : (g, f) ∉ G} + f)`.  (b) At `G = G_t`, `t ≥ 0`,
for `x`, `y` in one component, `u_G(x) < u_G(y)` iff `x ∈ PO_G ∌ y`, or `x, y ∈ PO_G` lie in
different clusters and `(x, y) ∉ G`.

*Proof.*  (a) `f ∉ cl(X)` gives `r(X + f) = r(X) + 1` (Mathlib, `eRk_insert_eq_add_one`), and
`f ∈ cl(X)` gives `r(X + f) = r(X)` (`rk_union_of_subset_closure`).  (b) Proposition 6(c) and
Theorem 14, Step 3.


## 2. Correspondence table

| paper label | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `def:posl`, `PO_t`, links, clusters, `u_t`, `N(t)` | `PO`, `near`, `Link`, `SameCluster`, `cluster`, `clusterRank`, `u`, `N`, `sameCluster_iff_transGen` | `POSL.lean` | defined |
| `def:posl`, clusters are intervals | `SameCluster.of_le_of_le` | `POSL.lean` | proved |
| `def:posl`, consecutive values differ by at most `t` | `SameCluster.sub_le`, `SameCluster.exists_link` | `POSL.lean` | proved |
| `def:posl`, two clusters differ by more than `t`, ordered | `lt_abs_sub`, `lt_sub_of_not_sameCluster` | `POSL.lean` | proved |
| `def:posl`, `u_t(e)` the rank of the cluster | `u_eq_card_add_one`, `u_le_u_iff`, `u_eq_u_iff`, `u_lt_u_iff`, `u_le_iff_mem`, `u_of_notMem` | `POSL.lean` | proved |
| `prop:posl`, Step 1, `PO_0` = elements of minimum bases | `mem_PO_zero_iff` | `POSL.lean` | proved |
| `prop:posl`, (F1) | `N_zero` | `POSL.lean` | proved |
| `prop:posl`, (F2) | `isBase_N_mono` | `POSL.lean` | proved |
| `prop:posl`, (F3) | `isBase_N_of_mem_Pos` | `POSL.lean` | proved |
| `prop:posl`, (F4) | `N_eq_self` | `POSL.lean` | proved |
| `prop:posl`, (F5) with levels `{0} ∪ {|v_e - v_f|}` | `levels`, `N_eq_N_of_levels` | `POSL.lean` | proved |
| `prop:posl`, admissible | `isAdmissible`, `prop_posl` | `POSL.lean` | proved |
| `prop:posl`, Step 5, determined by `G_t` | `Gt`, `POG`, `linkG`, `uG`, `NG`, `u_eq_uG`, `N_eq_NG`, `N_eq_of_Gt_eq` | `POSL.lean` | proved |
| `lem:observer`, Step 1 (`PO` by rank queries) | `mem_POG_iff` | `POSLRank.lean` | proved |
| `lem:observer`, Step 2 (order read from `G`) | `uG_lt_uG_iff`, `clusterG`, `repsG` | `POSLRank.lean` | proved |
| `lem:observer`, Step 3 (`eq:rank-mu` within components) | `rk_minBases_eq_sum_comp`, `rk_N`, `rk_NG`, `belowG` | `POSLRank.lean` | proved |
| `lem:observer`, Step 5 (`N_{E × E} = M`) | `NG_univ` | `POSL.lean` | proved |


## 3. Differences from the paper

1. **Hypotheses of Proposition `prop:posl`.**  The paper states it "for every `v` with
   `ν₀ < k`".  The structure `IsAdmissible` of `Rainbow/Defs.lean` carries no hypothesis on
   `ν₀`, and the proof never uses it, so `prop_posl` holds for every `v`.  The standing
   hypothesis of Section 4 that `M` has a rainbow base is the hypothesis `hM`; it is needed
   for (F4).  Proposed wording: "For every $v$, the family $N(t)$ of
   Definition~\ref{def:posl} satisfies (F1)--(F5) with levels ..." (the hypothesis
   $\nu_0<k$ only places the proposition in the setting of Definition~\ref{def:admissible}).
2. **Minimum bases of `u_t` lie in `PO_t`.**  Steps 1 and 3 of the proof use that the elements
   of a minimum base `B` of `u_t` lie in `PO_t` (in Step 3, "`x*` and `f` share a cluster"
   needs `f ∈ PO_t`), without saying why.  The reason is Lemma 8(e).  Proposed sentence, at the
   start of Step 3: "A minimum base $B$ of $u_t$ lies in $\PO_t$: by
   Lemma~\ref{lem:minbases}(2), $B\cap\PO_t=B\cap\{u_t\le m\}$ spans $\PO_t$, which contains a
   minimum base of $v$ and so spans $E$."
3. **Step 2, the case `0 < v_f - v_e ≤ t`.**  The paper argues through consecutive gaps; the
   two elements are linked directly.  Proposed wording: "if $0<v_f-v_e\le t$, both lie in
   $\PO_t$ and in one component, so they are linked and share a cluster."
4. **Step 3, the element `x*` and the insertion of `e`.**  The Lean proof uses the set
   `Z = {h ∈ B : u_t(h) ≤ u_t(x)` for some `x ∈ PO_t ∩ K` with `v_x < v_e - t}`, which is the
   set `{h ∈ B ∩ K : u_t(h) ≤ u_t(x*)}` of the paper up to elements outside `K`, and then
   uses Proposition 3 at scale `t'` instead of the gap argument.  Proposed wording for the end
   of Step 3: "Hence $x^{*}$ and $f$ share a cluster at scale $t$, so also at scale $t'$, and
   $e\in\PO_{t'}\cap K$, with $v_{x^{*}}<v_e<v_f$, lies in it, since clusters are intervals."
5. **Step 1, the direction "minimum for `v` implies minimum for `u_0`".**  The Lean proof reads
   it from Step 2 at `t = 0`, since $\Pos_0=\Bases(M^v)$; the paper's argument through
   `PO_0` and the clusters at scale `0` is also correct, and `mem_PO_zero_iff` formalizes its
   first assertion.  No change needed.
6. **Clusters.**  The Lean relation `SameCluster` is the reflexive transitive closure of the
   links on `PO_t`; for `t ≥ 0` it is their transitive closure (`sameCluster_iff_transGen`),
   as in the paper.  The rank of a cluster is defined by counting the clusters of the
   component that contain an element of smaller value outside the cluster;
   `u_eq_card_add_one` shows that these are the clusters below it.  No change needed.
7. **The rank formula of Lemma `lem:observer`, Step 3** holds at `G = G_t`, `t ≥ 0`
   (`rk_NG`), which is the case the lemma needs ("correct whenever $G=G_t$").  For an arbitrary
   `G` it can fail: at `G = ∅`, `PO_G = ∅` and `N_G = M`, while the formula gives `0`.  No change
   needed.
8. **The remark after Definition `def:posl`** (with either inequality changed, (F1) fails for
   `U_{1,3}` and `v = (0, 0, 1)`) is not formalized.  With `≤` in `PO_t`, `PO_0 = ∅`,
   `u_0 ≡ 4` and `N(0) = M ≠ M^v`, as stated.  With `< t` in the linkage, the clusters `{e_1}` and
   `{e_2}` at value `0` are not separated by more than `t = 0`, so "the order" of the clusters is
   not defined; ranking them `1` and `2` breaks (F1), while the counting rank used here gives
   both the rank `1` and (F1) holds.  Proposed wording: "With $\le$ in $\PO_t$, (F1) fails
   already for $U_{1,3}$ and $v=(0,0,1)$; with $<t$ in the linkage, the two clusters of value
   $0$ there are not ordered, and ranking them $1$ and $2$ breaks (F1)."


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/POSL.lean` | 907 |
| `SignedTropical/Rainbow/POSLRank.lean` | 319 |


## 5. Not done

* The counterexample in the remark after Definition `def:posl` (Section 3, item 8).
* The Boolean circuit of Lemma `lem:observer` and its size belong to the observer module
  (agent P6c); this module supplies its mathematical content (Theorems 14, 16 to 18,
  Lemma 19).


## 6. API for later agents (P5, P6c)

Definitions (namespace `SignedTropical.Rainbow.POSL`): `PO M v t : Set (Fin m)`,
`near v t : Fin m → Fin m → Prop`, `SameCluster M P J x y`, `cluster M P J x : Finset`,
`u M v t : Fin m → ℕ`, `N M v t : Matroid (Fin m)` (`= minBases M (fun e => (u M v t e : ℝ))`),
`clusters M v t e`, `levels v : Finset ℝ`, `Gt v t`, `POG M G`, `linkG G`, `uG M G`, `NG M G`;
`compLevel`, `compBelow`, `compReps`, `reps M v t`, `below M v t x`, `clusterG M G x`,
`repsG M G`, `belowG M G x`.  The clusters at scale `t` are
`SameCluster M (PO M v t) (near v t)`; its symmetry is `h.symm near_comm`.

For P5 (Theorem `thm:potential`): `isBase_N_iff`, `subset_PO_of_isBase_N`,
`subset_PO_of_isBase_minBases`, `u_le_iff_mem` (`u_t(e) ≤ m ↔ e ∈ PO_t`),
`u_eq_u_iff` (for `x, y ∈ PO_t` in one component, `u_t x = u_t y ↔` one cluster),
`u_le_u_iff`, `u_lt_u_iff`, `SameCluster.conn`, `SameCluster.sub_le` (consecutive values within
`t`), `SameCluster.of_le_of_le`, `lt_sub_of_not_sameCluster`, `N_eq_N_of_levels`,
`isAdmissible`.

For P6c (Lemma `lem:observer`): `N_eq_NG`, `NG_univ`, `rk_NG`, `mem_POG_iff`, `uG_lt_uG_iff`,
`mem_repsG`, `mem_belowG`, `mem_cluster`, `linkG_comm`, `mem_Gt`.
