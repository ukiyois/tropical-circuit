# P1g: rainbow spanning trees and the NP-hardness reduction

Natural-language companion of `SignedTropical/Rainbow/Star.lean` and
`SignedTropical/Rainbow/NPHard.lean`, namespace `SignedTropical.Rainbow.Graphs`.  Source:
`daishu/paper/greedy_intersection.tex`, Propositions `prop:star` and `prop:nphard` with their
proofs; research note `docs/phase2a-rainbow-2026-10-11.md`, Sections 1.2 and 3.3.  The modules
build on the multigraphs and cycle matroids of `Classes/Graphic.lean` (notes/Graphic.md) and on
`theta_le_iff` of `Rainbow/PossiblyOptimal.lean`.

The paper's statements:

> **Proposition `prop:star`** (Rainbow spanning trees contain assignment).  For every bipartite
> graph `H = (L, R, E)` with `|L| = |R| = n` there is a multigraph with colored edges whose
> rainbow spanning trees are the perfect matchings of `H`, with the same weights.  Its rainbow
> spanning tree polynomial is the permanent of the biadjacency matrix of `H` with variable
> entries.

> **Proposition `prop:nphard`** (Querying `P_t` is NP-complete).  Given a graph with colored and
> weighted edges and `t ≥ 0`, deciding whether `P_t` contains a rainbow spanning tree is
> NP-complete.

Build status: `lake build SignedTropical.Rainbow.Star` and `lake build
SignedTropical.Rainbow.NPHard` succeed with no error and no warning.  No `sorry`, `admit`,
`axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.  `#print axioms`
of the 15 theorems checked (`isSpanningTree_iff_isBase`, `isCycle_star_iff`,
`isRainbowSpanningTree_star_iff`, `rank_star`, `isRainbowBase_star_iff`,
`sum_rainbowSpanningTree_star`, `rainbowTreePolynomial_eq_permanent`, `HasRainbowPath.symm`,
`exists_path_of_isCycle`, `isSpanningTree_image`, `rank_reduction`,
`hasRainbowPath_of_theta_le`, `exists_rainbowBase_of_hasRainbowPath`,
`exists_rainbowBase_theta_le_iff`, `exists_rainbowSpanningTree_theta_le_iff`) gives only
`propext`, `Classical.choice` and `Quot.sound` (`HasRainbowPath.symm`: only `propext`).

Notation.  A multigraph `G : Multigraph n m` has vertices `Fin n` and edges `Fin m`, edge `e`
joining `src e` and `tgt e`; loops and parallel edges are allowed.  `G.Joins e x y`: `e` joins `x`
and `y` in either orientation.  `G.IsCycle C`: `C` is the edge set of a cycle (a loop and a pair
of parallel edges are cycles).  `inc v e` is the number of ends of `e` at `v` and `deg S v` the
degree of `v` in the edge set `S`.  `G.cycleMatroid` is the cycle matroid; its independent sets
are the edge sets containing no cycle (`Multigraph.indep_iff`), equivalently those whose every
nonempty subset has a vertex of odd degree (`Multigraph.indep_iff_odd`), and its circuits are the
cycles (`Multigraph.isCircuit_iff`).  From `Rainbow/Defs.lean`: `IsRainbow col T` (`col` is
injective on `T`), `IsRainbowBase M col T` (a base of `M` that is rainbow), and
`theta M v T`, the paper's `θ(T) = max({0} ∪ {v_f - v_e : e ∉ T, f ∈ C(T, e)})`.  By
`theta_le_iff`, `θ(T) ≤ t` iff `0 ≤ t` and `v_f - v_e ≤ t` for every `e ∉ T` and
`f ∈ C(T, e)`.

## 1. Results

### 1.1 Spanning trees (`Star.lean`)

Definition (`IsSpanningTree G T`).  `T` contains no cycle of `G` and `#T + 1 = n`.  This is the
standard characterization of a spanning tree: a forest with `c` components on `n` vertices has
`n - c` edges, so a forest with `n - 1` edges is connected.

Statements.
* `isSpanningTree_iff_indep`: `T` is a spanning tree iff `T` is independent in the cycle matroid
  and `#T + 1 = n`.
* `IsSpanningTree.isBase`: a spanning tree is a base of the cycle matroid.
* `IsSpanningTree.rank_eq`: if `G` has a spanning tree, then `rank + 1 = n`.
* `isSpanningTree_iff_isBase`: if `rank + 1 = n` (`G` is connected), the spanning trees are
  exactly the bases.
* `joins_comm`: `Joins e x y ↔ Joins e y x`.

Proofs.  Step 1.  `isSpanningTree_iff_indep` is `Multigraph.indep_iff`.  Step 2.  For a spanning
tree `T`, `n ≥ 1`, so `rank ≤ n - 1 = #T` (`Multigraph.rank_le`), and an independent set with at
least `rank` elements is a base.  Step 3.  A base has `rank` elements (Phase 1 `card_base`),
which gives `rank_eq`.  Step 4.  Conversely, if `rank + 1 = n`, a base is independent with
`rank = n - 1` elements.

### 1.2 The star and its cycles (`star`, `indep_star_iff`, `isCycle_star_iff`)

Setting.  A bipartite multigraph `H` on `L = R = Fin n` with edges `Fin m` is given by
`lft rgt : Fin m → Fin n`: edge `e` joins `ℓ_{lft e}` and `ρ_{rgt e}`.  A bipartite graph is the
case where `e ↦ (lft e, rgt e)` is injective.

Definition (`star rgt : Multigraph (n + 1) m`).  The vertices are `R ∪ {z}`, with `ρ_j = j` and
`z = n`; edge `e` joins `z` and `ρ_{rgt e}`.  The color of `e` is `lft e`, and its weight is the
weight of `e` in `H`: the edges of the star are the edges of `H`, under the same names.

Statements.  (a) `indep_star_iff`: an edge set `T` of the star contains no cycle iff `rgt` is
injective on `T` (no two parallel edges).  (b) `isCycle_star_iff`: the cycles of the star are the
sets `{e, e'}` with `e ≠ e'` and `rgt e = rgt e'`.

Proof of (a).  Step 1.  If `e ≠ e'` in `T` have `rgt e = rgt e'`, they have the same ends, so
every vertex `v` has degree `2 inc v e` in `{e, e'}`, which is even; by `indep_iff_odd`, `T` is
dependent.  Step 2.  If `rgt` is injective on `T` and `S ⊆ T` contains `e`, the vertex
`ρ_{rgt e}` meets `e` once (it differs from `z`) and no other edge of `S`, so its degree in `S`
is `1`, odd; by `indep_iff_odd`, `T` is independent.

Proof of (b).  Cycles are circuits.  Step 1.  A circuit `C` is dependent, so by (a) it contains
`e ≠ e'` with `rgt e = rgt e'`; `{e, e'}` is dependent by (a), and by minimality `C = {e, e'}`.
Step 2.  Conversely `{e, e'}` is dependent by (a), and each proper subset has at most one
element, so it is independent by (a).

### 1.3 Proposition `prop:star`, the trees (`isRainbowSpanningTree_star_iff`)

Definition (`IsPerfectMatching lft rgt T`).  Every `i ∈ L` is an end of exactly one edge of `T`,
and every `j ∈ R` is an end of exactly one edge of `T`.

Statement.  For every bipartite multigraph `H` given by `lft, rgt` and every edge set `T`:
`T` is a rainbow spanning tree of the star, colored by `lft`, iff `T` is a perfect matching of
`H`.  The correspondence is the identity on sets of edges of `H`, so it keeps every weight.

Auxiliary statements.  `forall_existsUnique_iff`: for `f : Fin m → Fin n`, `T` meets every
fibre of `f` exactly once iff `f` is injective on `T` and `#T = n`.  `isSpanningTree_star_iff`:
`T` is a spanning tree of the star iff `rgt` is injective on `T` and `#T = n`.

Proof.  Step 1 (`forall_existsUnique_iff`).  If `T` meets every fibre once, `f` is injective on
`T` by uniqueness and `f(T)` is all of `Fin n` by existence, so `#T = #f(T) = n`.  Conversely,
if `f` is injective on `T` and `#T = n`, then `#f(T) = n`, so `f(T)` is all of `Fin n`;
existence follows, and uniqueness follows from injectivity.  Step 2 (`isSpanningTree_star_iff`).
By 1.1 and 1.2(a), `T` is a spanning tree iff `rgt` is injective on `T` and `#T + 1 = n + 1`.
Step 3.  `T` is a rainbow spanning tree iff `rgt` and `lft` are injective on `T` and `#T = n`,
which by Step 1, applied to `lft` and to `rgt`, says that `T` is a perfect matching.

### 1.4 Rainbow bases of the star (`rank_star`, `isRainbowBase_star_iff`)

Statements.  If every `j ∈ R` is an end of some edge of `H`: (a) `rank_star`: the cycle matroid
of the star has rank `n`; (b) `isRainbowBase_star_iff`: the rainbow bases of the cycle matroid,
with the `n` colors as blocks, are exactly the perfect matchings of `H`.

Proof.  Step 1.  Choose an edge `g j` at every `ρ_j`.  Then `rgt ∘ g` is the identity, so `g` is
injective, `rgt` is injective on `{g j}`, and `{g j}` has `n` elements; by 1.3 Step 2 it is a
spanning tree, and 1.1 gives `rank + 1 = n + 1`.  Step 2.  By 1.1, the bases are the spanning
trees, and 1.3 applies.

### 1.5 Proposition `prop:star`, the polynomial (`sum_rainbowSpanningTree_star`, `rainbowTreePolynomial_eq_permanent`)

Statement (`sum_rainbowSpanningTree_star`).  For a bipartite multigraph `H` given by `lft, rgt`
and values `x_e` in a commutative semiring,
`Σ_{T rainbow spanning tree of the star} Π_{e ∈ T} x_e = perm A`, where
`A_{ij} = Σ_{e : lft e = i, rgt e = j} x_e`.

Statement (`rainbowTreePolynomial_eq_permanent`).  For a bipartite graph `E ⊆ L × R`, its edges
numbered by `Fin #E` (`bipEdge`), and any commutative semiring `R`: in the polynomial ring
`R[x_{ij} : i, j ∈ Fin n]`, the rainbow spanning tree polynomial of the star,
`Σ_T Π_{ij ∈ T} x_{ij}`, equals the permanent of the matrix with entry `x_{ij}` if `ij ∈ E` and
`0` otherwise, the biadjacency matrix of `E` with variable entries.

Proof of the first.  Step 1.  By 1.3 the sum runs over the perfect matchings.  Step 2.  Expand
`perm A = Σ_σ Π_j A_{σ j, j}` and each product of sums as a sum over choice functions: the right
side is the sum, over pairs `(σ, g)` of a permutation `σ` and a choice `g j` of an edge with
`lft (g j) = σ j` and `rgt (g j) = j`, of `Π_j x_{g j}`.  Step 3.  The map `(σ, g) ↦ {g j}` is a
bijection onto the perfect matchings.  It lands in them: the edge at `ρ_j` is `g j`, the edge at
`ℓ_i` is `g (σ⁻¹ i)`, and both are unique since `rgt ∘ g` is the identity and `σ` is a
permutation.  It is injective: `g j` is the unique edge of the image at `ρ_j`, and
`σ j = lft (g j)`.  It is onto: for a perfect matching `T`, let `g j` be its edge at `ρ_j`; then
`lft ∘ g` is injective, hence a permutation `σ`, and the image of `g` is `T`.  Step 4.  `g` is
injective, so `Π_{e ∈ {g j}} x_e = Π_j x_{g j}`.

Proof of the second.  Step 1.  Apply the first with `x_e = x_{bipEdge e}`.  Step 2.  The entry
`(i, j)` is the sum of `x_{bipEdge e}` over the edges `e` with `bipEdge e = (i, j)`: there is
exactly one such edge if `ij ∈ E`, which gives `x_{ij}`, and none otherwise, which gives `0`.

### 1.6 Rainbow paths and cycles (`HasRainbowPath`, `exists_path_of_isCycle`)

Definition (`HasRainbowPath G col s t`).  There are `d ≥ 0`, pairwise distinct vertices
`x 0 = s, x 1, …, x d = t`, and edges `e 0, …, e (d - 1)` of pairwise distinct colors, `e i`
joining `x i` and `x (i + 1)`.  `HasRainbowPath.symm`: reversing gives a rainbow path from `t`
to `s`.

Statement (`exists_path_of_isCycle`).  If `g` lies on a cycle `C`, there are pairwise distinct
vertices `x 0, …, x d` and pairwise distinct edges `e 0, …, e (d - 1)` of `C`, all different from
`g`, `e i` joining `x i` and `x (i + 1)`, and `g` joins `x d` and `x 0`.

Proof.  Step 1.  Write `C` as the walk `x'_0 e'_0 ⋯ x'_{l-1} e'_{l-1} x'_0` and `g = e'_j`; put
`l = d + 1`.  Step 2.  Walk around the cycle starting after `g`: `r(i) = (j + 1 + i) mod l`, and
`x i = x'_{r(i)}`, `e i = e'_{r(i)}`.  The map `r` is injective on `{0, …, d}` and `r(d) = j`, so
the vertices and edges are distinct and `e i ≠ g` for `i < d`.  Step 3.  `r(i + 1) = r(i) + 1 mod
l`, so `e i` joins `x i` and `x (i + 1)`; `g = e'_j` joins `x'_j = x d` and
`x'_{(j+1) mod l} = x 0`.

### 1.7 Spanning trees from parent edges (`isSpanningTree_image`)

Statement.  Let `r` be a vertex, `ρ` a height on the vertices, and `p v`, for every vertex
`v ≠ r`, an edge joining `v` to a vertex `u` with `ρ u < ρ v`.  Then `p` is injective on the
vertices other than `r`, and `{p v : v ≠ r}` is a spanning tree.

Proof.  Step 1, injectivity.  Let `p v = p w` with `v ≠ w`.  The edge joins `v` to some `u` and
`w` to some `u'`, both of smaller height.  Since `w ≠ v` is an end, `w = u`; since `v ≠ w` is an
end, `v = u'`.  Then `ρ w < ρ v < ρ w`.  Step 2, no cycle.  By `indep_iff_odd` it suffices that
every nonempty `S ⊆ T` has a vertex of odd degree.  Take `v ≠ r` of largest height with
`p v ∈ S`.  The edge `p v` meets `v` once (its other end has smaller height).  Another edge
`p w ∈ S`, `w ≠ v`, meeting `v` would have `v` as its lower end, so `ρ w > ρ v`, against the
choice of `v`.  So `v` has degree `1` in `S`.  Step 3, count.  By Step 1, `#T = n - 1`.

### 1.8 The instance of Step 2 (`reduction`, `redColor`, `redWeight`, `rank_reduction`)

Data.  A multigraph `H : Multigraph n mH`, edge colors `col : Fin mH → Fin q` (the colors
`C = Fin q`), vertices `s, t` of `H`, and `h` with `n ≤ h` (`hn`) and `q ≤ h` (`hq`).

Definition.  The instance `reduction H hn s t : Multigraph (h + 2) (mH + 2 + h * h)`:
* vertices: `vP a` for `a ∈ Fin h` (the vertices of `H`, `vH a = vP a` for `a ∈ Fin n`, padded
  by `h - n` isolated vertices), `z = vZ` and `y = vY`;
* edges, numbered through `(Fin mH ⊕ Fin 2) ⊕ Fin h × Fin h` (`edgeEquiv`): the edges `eH a` of
  `H`, with the same ends; `e* = eS` joining `s` and `t`; `f = eF` joining `y` and `s`; and
  `eZ x c` joining `z` and `vP x`, for every `x ∈ Fin h` and `c ∈ Fin h`;
* colors `redColor hq col : Fin (mH + 2 + h * h) → Fin (h + 1)`: `eH a` keeps its color
  `col a ∈ C = Fin q ⊆ Fin h`; `e*` and `f` get the new color `c* = h`; `eZ x c` gets `c`, which
  ranges over `C ∪ X = Fin h`, `X = Fin h \ Fin q` being the `h - q` new colors;
* weights `redWeight`: `5` on the edges of `H`, `0` on `e*` and `f`, `10` on the edges `zx`.

So the instance has `h + 2` vertices, `mH + 2 + h²` edges and `h + 1` colors, all recorded in its
type, and weights in `{0, 5, 10}`.  For `h = max(n, q)` its size is polynomial in that of `H`.

Statement (`rank_reduction`).  The cycle matroid of the instance has rank `h + 1`, the number of
colors.  Hence its bases are its spanning trees (1.1).

Proof.  Step 1.  `h ≥ n ≥ 1`, since `s` exists.  Step 2.  Apply 1.7 with root `z`, heights `0` at
`z`, `1` at every `vP b`, `2` at `y`, and parent edges `eZ b 0` at `vP b` and `f` at `y` (which
joins `y` to `s`, of height `1`).  The resulting spanning tree gives `rank + 1 = h + 2` (1.1).

### 1.9 Step 3, forward (`hasRainbowPath_of_theta_le`)

Statement.  If the instance has a rainbow base `T` (a rainbow spanning tree, by 1.8) with
`θ(T) ≤ 5`, then `H` has a rainbow `s`–`t` path.

Proof.  Step 1.  The edge `f` lies on no cycle: `y` is an end of `f` only (`inc_vY`), so in a
cycle through `f` the vertex `y` would have degree `1`, while cycles have even degrees.  So
`f ∈ T` (`Multigraph.mem_of_isBase`), and since `T` is rainbow and `e*` has the color of `f`,
`e* ∉ T`.  Step 2.  Let `C = C(T, e*)`, a circuit, hence a cycle; its edges other than `e*` lie
in `T`.  By `θ(T) ≤ 5` and `theta_le_iff`, every `g ∈ C` has weight at most `0 + 5 = 5`.
Step 3.  Delete `e*` from `C` (1.6): distinct vertices `X 0, …, X d` and distinct edges
`E i ∈ C - e*`, `E i` joining `X i` and `X (i + 1)`, with `e*` joining `X d` and `X 0`.  Each `E i`
is an edge of `H`: it is not `e*`, not `f` (Step 1), and not an edge `zx` (weight `10 > 5`).
Step 4.  Each `X i` is a vertex of `H`: for `i < d` it is an end of the edge `E i` of `H`, and
`X d` is an end of `e*`, that is `s` or `t`.  Step 5.  The corresponding edges of `H` form a
rainbow path of `H` from `X 0` to `X d`: the vertices are distinct, the edges `E i` are distinct
edges of the rainbow `T`, and an edge of `H` keeps its color in the instance (through the
injective inclusion `C ⊆ Fin (h + 1)`).  Step 6.  Since `e*` joins `X d` and `X 0`,
`{X 0, X d} = {s, t}`; if `X 0 = t`, reverse the path (`HasRainbowPath.symm`).

### 1.10 Step 4, backward (`exists_rainbowBase_of_hasRainbowPath`)

Statement.  If `H` has a rainbow `s`–`t` path, the instance has a rainbow base `T` with
`θ(T) ≤ 5`.

Proof.  Step 1, colors.  Let `x 0 = s, …, x d = t` and `e 0, …, e (d - 1)` be the path.  The maps
`j ↦ x (j + 1)` and `j ↦ col (e j)`, from `Fin d` to `Fin h`, are injective; extend the bijection
between their images to a permutation `κ` of `Fin h` (`Equiv.extendSubtype`), so that
`κ (x (j + 1)) = col (e j)`.  Step 2, the tree.  At `vP b` take the edge `e j` if `b = x (j + 1)`,
and otherwise the edge `zb` of color `κ b`; at `y` take `f`.  With heights `i + 1` at `x i`, `1`
at the other `vP b`, `0` at `z` and `2` at `y`, every chosen edge goes down: `e j` from
`x (j + 1)` to `x j`, `zb` to `z`, `f` from `y` to `s = x 0`.  By 1.7 the chosen edges form a
spanning tree `T`, hence a base.  This is the tree of the paper: `P`, `f`, and an edge `zx` at
every vertex of `V(H) \ V(P)` and at the vertex `s` of `P`.  Step 3, rainbow.  The edge chosen at
`vP b` has color `κ b` (for `b = x (j + 1)` by Step 1), and the edge at `y` has the color `c*`,
different from all of these; `κ` is injective, so `T` is rainbow.  Step 4, the cycle of `e*`.
The path followed by `e*` (from `t = x d` back to `s = x 0`) is a cycle contained in `T + e*`, so
it is `C(T, e*)` (`Multigraph.fundCircuit_eq`).  Step 5, `θ(T) ≤ 5` (by `theta_le_iff`).  Let
`g ∉ T` and `g' ∈ C(T, g)`; every weight is at most `10` (`redWeight_le`).  If `g` is an edge of
`H`, `v_{g'} - v_g ≤ 10 - 5 = 5`.  If `g = e*`, `g'` is `e*` or an edge of `P`, so
`v_{g'} - v_g ≤ 5 - 0`.  The case `g = f` is impossible since `f ∈ T`.  If `g` is an edge `zx`,
`v_{g'} - v_g ≤ 10 - 10 = 0`.

### 1.11 Proposition `prop:nphard`, the reduction (`exists_rainbowBase_theta_le_iff`, `exists_rainbowSpanningTree_theta_le_iff`)

Statement (`exists_rainbowSpanningTree_theta_le_iff`).  For every multigraph `H` on `n` vertices
with edge colors in `C = Fin q`, all vertices `s, t` of `H`, and every `h ≥ n, q`: the instance
of 1.8 has a rainbow spanning tree `T` with `θ(T) ≤ 5`, that is, `P_5` contains a rainbow
spanning tree, iff `H` has a rainbow `s`–`t` path.  `exists_rainbowBase_theta_le_iff` is the same
statement for rainbow bases of the cycle matroid with the colors as blocks.

Proof.  Step 1.  For rainbow bases, combine 1.9 and 1.10.  Step 2.  By `rank_reduction` and 1.1,
the bases of the instance are its spanning trees, so the rainbow bases are the rainbow spanning
trees.

## 2. Correspondence table

| Paper | Lean names | Module | Status |
| :-- | :-- | :-- | :-- |
| spanning trees as bases | `IsSpanningTree`, `isSpanningTree_iff_indep`, `IsSpanningTree.isBase`, `IsSpanningTree.rank_eq`, `isSpanningTree_iff_isBase` | Star | proved |
| `prop:star`, Step 1 (construction) | `star`, `indep_star_iff`, `isCycle_star_iff` | Star | proved |
| `prop:star`, Step 2 (trees are perfect matchings, same weights) | `IsPerfectMatching`, `forall_existsUnique_iff`, `isSpanningTree_star_iff`, `isRainbowSpanningTree_star_iff` | Star | proved |
| `prop:star`, as rainbow bases | `rank_star`, `isRainbowBase_star_iff` | Star | proved |
| `prop:star`, the polynomial is the permanent | `sum_rainbowSpanningTree_star`, `bipEdge`, `rainbowTreePolynomial_eq_permanent` | Star | proved |
| rainbow `s`–`t` path | `HasRainbowPath`, `HasRainbowPath.symm` | NPHard | defined, proved |
| tree paths and trees from parent edges | `exists_path_of_isCycle`, `isSpanningTree_image` | NPHard | proved |
| `prop:nphard`, Step 1 (membership in NP) | none | none | not formalized (complexity classes) |
| `prop:nphard`, Step 2 (construction, sizes) | `reduction`, `vP`, `vZ`, `vY`, `vH`, `edgeEquiv`, `eH`, `eS`, `eF`, `eZ`, `redColor`, `redWeight`, `rank_reduction` | NPHard | defined, proved |
| `prop:nphard`, Step 3 | `hasRainbowPath_of_theta_le` | NPHard | proved |
| `prop:nphard`, Step 4 | `exists_rainbowBase_of_hasRainbowPath` | NPHard | proved |
| `prop:nphard`, Steps 2 to 4 | `exists_rainbowBase_theta_le_iff`, `exists_rainbowSpanningTree_theta_le_iff` | NPHard | proved |
| NP-completeness of rainbow `s`–`t` path (`cfmy09`) | none | none | cited, not formalized |

## 3. Differences from the paper

1. Spanning trees.  `IsSpanningTree G T` is "no cycle and `|V| - 1` edges", the standard
   characterization; the modules use it only through the cycle matroid, and in both
   constructions the graph is connected, so the spanning trees are the bases
   (`isSpanningTree_iff_isBase`).

2. `prop:star`, generality.  The tree correspondence and `sum_rainbowSpanningTree_star` are proved
   for bipartite multigraphs (parallel edges allowed) and values in any commutative semiring.
   The permanent statement `rainbowTreePolynomial_eq_permanent` is for a bipartite graph
   `E ⊆ L × R`, as in the paper.  The edges of the star are the edges of `H` under the same names,
   so "with the same weights" holds for every weight function; there is no separate weight
   statement.  For the matroid reading (rainbow bases, the colors as blocks, `k = n` the rank),
   every right vertex must have an edge (`isRainbowBase_star_iff`); otherwise the star is
   disconnected, and its rainbow bases are not spanning trees.  No change to the paper is needed.

3. `prop:nphard`, scope.  Complexity classes are not formalized.  Step 1 (membership) and the
   NP-completeness of rainbow `s`–`t` path, cited from `cfmy09`, are not formalized.  The
   formalization proves Steps 2 to 4: the instance, its sizes (recorded in its type), and the
   equivalence.  It holds for every multigraph `H` (loops and parallel edges allowed) and every
   `s, t`, including `s = t` (then `e*` is a loop and both sides hold).

4. `prop:nphard`, "graph".  The instance has `h` parallel edges `zx` at every `x` (and `e*` may be
   parallel to an edge of `H`), so it is a multigraph, not a graph.  The statement should say
   "multigraph".

5. `prop:nphard`, weights.  `θ` is defined from `v = w - p_blk`; in the decision problem the given
   weights play the role of `v`.  The proposed statement names them `v`.

6. `prop:nphard`, Step 4.  `h - |P|` counts the edges of `P` (there are `h - |V(P)| + 1` edges
   `zx`), so `|P|` should read `|E(P)|`.  The formalization joins `z` to the vertex `s` of `P`; any
   vertex of `P` works.

Proposed replacement wording.

Statement of `prop:nphard`:

> Given a multigraph with colored edges, edge weights $v$ and $t\ge0$, deciding whether $\Pos_t$
> contains a rainbow spanning tree is NP-complete.

Step 4 of its proof, first sentence:

> For a rainbow path $P$ from $s$ to $t$, take $P$, $f$, one edge $zx$ for each
> $x\in V(H)\setminus V(P)$ and one edge $zx$ for a vertex $x$ of $P$, colored by the
> $h-|E(P)|$ colors of $C\cup X$ not on $P$.

Sentence on the scope of the formalization (for a formalization remark, if the paper has one):

> In the Lean formalization, Steps 2 to 4 are proved for every multigraph $H$ with colors $C$,
> vertices $s,t$ and $h\ge|V(H)|,|C|$: the instance of Step 2 has a rainbow spanning tree $T$ with
> $\theta(T)\le5$ if and only if $H$ has a rainbow $s$--$t$ path.  Step 1 and the NP-completeness
> of rainbow $s$--$t$ path~\cite{cfmy09} concern complexity classes, which are not formalized;
> they are cited.

## 4. Line counts

| Module | Lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Star.lean` | 286 |
| `SignedTropical/Rainbow/NPHard.lean` | 601 |

## 5. Not done

* Membership in NP (Step 1 of `prop:nphard`), polynomial-time computability of the instance, and
  the NP-completeness of rainbow `s`–`t` path: complexity classes are not formalized, as the
  assignment states.  The instance's sizes are exact and recorded in its type.
* The equivalence of `IsSpanningTree` with "connected and acyclic" is not proved; the modules do
  not use it.
