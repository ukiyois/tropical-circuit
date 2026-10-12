# Graphic matroids

Module: `SignedTropical/Classes/Graphic.lean` (namespace
`SignedTropical.Classes.Graphic.Multigraph`), written by the coordinator.  Paper:
`greedy_intersection.tex`, Corollary `cor:classes`; also the API used by Propositions `prop:star`
and `prop:nphard`.

## 1. Definitions

* A multigraph `G : Multigraph n m` has vertices `Fin n` and edges `Fin m`; edge `e` joins
  `src e` and `tgt e`.  Loops and parallel edges are allowed.  `Joins e x y` says that `e` joins
  `x` and `y` in either orientation.
* A cycle (`IsCycle C`) is the edge set of a closed walk `x₀ e₀ x₁ e₁ ⋯ x_{l-1} e_{l-1} x₀` with
  `l ≥ 1` pairwise distinct vertices and `l` pairwise distinct edges, edge `e_i` joining `x_i` and
  `x_{i+1}` (indices modulo `l`).  A loop is a cycle with one edge, and two parallel edges form a
  cycle with two edges.
* `inc v e = [src e = v] + [tgt e = v]` and `deg T v = Σ_{e ∈ T} inc v e`, the degree of `v` in the
  edge set `T`, a loop counting twice.
* `incidence G` is the vertex-edge incidence matrix over `ZMod 2`, and `cycleMatroid G` is the
  binary matroid of this matrix (Phase 1's `binaryMatroid`).  Theorem 2.3 shows that its
  independent sets are the edge sets containing no cycle, so it is the cycle matroid of `G`.
* `IsPathIn T d x e`: a path in `T` with `d` edges, pairwise distinct vertices `x 0, …, x d`.

## 2. Results

### 2.1 Even degrees (`sum_colZ_eq_zero_iff`, `IsCycle.deg_eq`, `IsCycle.even_deg`)

Statement.  The columns of an edge set `T` sum to zero over `ZMod 2` iff every vertex has even
degree in `T`.  In a cycle, the degree of `v` is twice the number of visits of the walk to `v`;
in particular every degree is even.

Proof.  Step 1.  Entry `v` of the sum of the columns of `T` is `deg T v` modulo 2.  Step 2.  For a
cycle, `inc v e_i = [x_i = v] + [x_{i+1} = v]`, and summing over `i` counts each visit twice,
since `i ↦ i + 1 mod l` permutes `{0, …, l-1}`.

### 2.2 Even degrees force a cycle (`exists_isCycle_subset`)

Statement.  A nonempty edge set `T` in which every vertex has even degree contains a cycle.

Proof.  Step 1.  A loop in `T` is a cycle.  Step 2.  Otherwise every edge has two distinct ends,
so `T` contains a path with one edge, and a path has at most `n - 1` edges
(`IsPathIn.succ_le`); take a path `x_0, …, x_D` in `T` with `D` largest.  Step 3.  The last edge
`e_{D-1}` meets `x_D` once, and the degree of `x_D` is even, so another edge `f ∈ T` meets
`x_D`; let `w` be its other end, `w ≠ x_D`.  Step 4.  If `w` is not on the path, the path extends
by `f` (`IsPathIn.extend`), against the choice of `D`.  So `w = x_j` with `j < D`.  Step 5.  The
vertices `x_j, …, x_D` and the edges `e_j, …, e_{D-1}, f` form a cycle (`IsPathIn.exists_isCycle`):
the vertices are distinct, the edges of a path are distinct (`IsPathIn.edge_ne`), and `f` differs
from them, since `f ≠ e_{D-1}` and the earlier edges do not meet `x_D` (`IsPathIn.ne_of_inc_last`).

### 2.3 The cycle matroid (`linearIndepOn_iff_sum`, `indep_iff_odd`, `indep_iff`)

Statement.  An edge set `S` is independent in `cycleMatroid G` iff it contains no cycle, iff every
nonempty `T ⊆ S` has a vertex of odd degree.

Proof.  Step 1.  Over `ZMod 2`, a finite family is linearly independent iff no nonempty subfamily
sums to zero, since a coefficient is `0` or `1`.  Step 2.  By 2.1 a subfamily sums to zero iff all
its degrees are even.  Step 3.  A cycle has even degrees (2.1), and a nonempty set with even
degrees contains a cycle (2.2).

### 2.4 Circuits are cycles (`IsCycle.eq_of_subset`, `isCircuit_iff`)

Statement.  A cycle `C` contains no nonempty edge set with even degrees other than `C`; the
circuits of `cycleMatroid G` are exactly the cycles.

Proof.  Step 1.  Let `T ⊆ C` be nonempty with even degrees and `e_j ∈ T`.  The vertex `x_{j+1}`
meets the edges of `C` only in `e_j` and `e_{j+1}` (the vertices of `C` are distinct), so its
degree in `T` is `1 + [e_{j+1} ∈ T]`, and parity gives `e_{j+1} ∈ T`.  Going around the cycle,
`C ⊆ T`.  Step 2.  A circuit is dependent, so it contains a cycle (2.3), which is dependent, so by
minimality it is the circuit.  Step 3.  A cycle is dependent, and a cycle inside a proper subset
of it would contradict Step 1, so every proper subset is independent.

### 2.5 API for spanning trees (`mem_of_isBase`, `fundCircuit_eq`, `rank_le`)

Statements.  (a) An edge on no cycle lies in every base.  (b) For a base `B`, `e ∉ B` and a cycle
`C ⊆ B + e`, the fundamental circuit `C(B, e)` is `C`.  (c) For `n ≥ 1`, the rank of
`cycleMatroid G` is at most `n - 1`.

Proofs.  (a) Otherwise the fundamental circuit of the edge is a cycle through it (2.4).  (b) A
circuit inside `B + e` is the fundamental circuit (Mathlib's `IsCircuit.eq_fundCircuit_of_subset`).
(c) Every column has coordinate sum `[src] + [tgt] = 2 = 0`, so the columns lie in the kernel of
the coordinate-sum functional, a hyperplane of dimension `n - 1`.

### 2.6 Corollary `cor:classes` for graphic matroids (`rankCircuit`, `corollaryC_graphic`)

Statement.  The Boolean rank circuit of Phase 1 for the incidence matrix has
`m(9n² + 5n) + 11n⌈log₂(n+1)⌉` gates and outputs the binary digits of the rank of the cycle matroid;
maximum-weight spanning forests have a signed tropical circuit with at most `100(m+1)²(n+1)²`
gates.

Proof.  Phase 1's `binaryRankCircuit_size`, `binaryRankCircuit_rank` and `corollaryC_binary_poly`
for the `n × m` incidence matrix.

## 3. Correspondence

| Paper | Lean | Status |
|---|---|---|
| graphic matroids in `cor:classes` | `cycleMatroid`, `indep_iff`, `isCircuit_iff`, `rankCircuit`, `corollaryC_graphic` | proved |
| (API) even degrees, longest path | `sum_colZ_eq_zero_iff`, `IsCycle.even_deg`, `exists_isCycle_subset` | proved |
| (API) spanning trees | `mem_of_isBase`, `fundCircuit_eq`, `rank_le` | proved |
| cographic matroids in `cor:classes` | pending E4's `Classes/Dual.lean` | not yet |

## 4. Differences from the paper

The paper lists graphic matroids under the general simulation argument of `cor:classes` item 2;
here they get the explicit sizes above.

## 5. Module size

`Graphic.lean`: 482 lines.
