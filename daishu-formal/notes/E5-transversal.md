# E5: transversal matroids and gammoids (Corollary `cor:classes`)

Natural-language companion of `SignedTropical/Classes/Transversal.lean` and
`SignedTropical/Classes/TransversalGammoid.lean`, namespace `SignedTropical.Classes.Transversal`.
Sources: `daishu/paper/greedy_intersection.tex`, Corollary `cor:classes` (item 6 mentions
transversal matroids and gammoids), Lemma `lem:avoidable` and Lemma `lem:observer`, Step 4; the
finished modules `Rainbow/Exchange.lean` (P2: `card_add_nu_le`, `card_av_add_nu`, `mem_av`,
`card_le_nu`, `exists_card_eq_nu`), `Rainbow/MICircuit.lean` (P6b: `nuCircuit`,
`nuCircuit_spec`, `indepOfRankB_impl`, `indepOfRank_correct`, `roundCost`), `BoolAlg/*.lean`
(P6a: `Impl`, `Impl.foldCtx`, `Impl.tabSum`, `emitOr_impl`, `emitAnd_impl`, `vecPopcountB_impl`,
`popCost`, `runB_num`, `circuitOf_num`), `Rainbow/Partition.lean` (`colMatroid`, `rk_eq`),
`Classes/Dual.lean` (E4: `dualRankCircuit`, `dualRankCircuit_rank`) and Phase 1 (`theoremA`, `rk`,
`rank`, `card_le_rk`, `card_eq_rk`, `card_base`).  For gammoids: the theorem of Ingleton and Piff
(1973; Oxley, *Matroid Theory*, Section 2.4), proved here.

Build status: `lake build SignedTropical.Classes.Transversal` and
`lake build SignedTropical.Classes.TransversalGammoid` succeed with no error and no warning.  No
`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
`#print axioms` of all 50 theorems of the two modules (checked in a scratch file, since
deleted): `propext`, `Classical.choice`, `Quot.sound` only (four of them on fewer).  No external
result enters as a hypothesis.

Conventions, as in Phase 1 and E4.  `E = Fin m`; a family of sets `A₀, …, A_{n-1} ⊆ E` is
`A : Fin n → Finset (Fin m)` (repeated and empty sets allowed).  A matroid on `E` is
`M : Matroid (Fin m)` with `M.E = Set.univ`; `r(S)` is `rk M S` (in `ℕ`) or `M.eRk S` (in `ℕ∞`).
A Boolean circuit `B : Circuit BoolOp m` outputs `r(S)` in binary when
`bitsVal (B.eval boolInterp 1_S) = r(S)` for every `S`, the hypothesis of `theoremA`.  The size
of a circuit is its number of gates; `⌈log₂(k+1)⌉` is `Nat.size k`; `popCost r =
11(2r - 1 - ⌈log₂(r+1)⌉) ≤ 22r` is the size of a population count of `r` bits (P6a);
`roundCost p c = p²c + 8p³ + 12p² + 12p + 4` is the size of one round of the augmenting path
algorithm on `p` elements with `c` gates per independence test (P6b).  `h_M(w) = max_B w(B)` is
`maxBasisWeight M w`.  `ν(N)` and `Av(N)` are `nu N blk` and `Av N blk` of `Rainbow/Defs.lean`.


## 1. Results and proofs

### 1.1 The transversal matroid (`Classes/Transversal.lean`)

**Definition 1 (partial transversals), `IsPartialTransversal`.**  A set `X ⊆ E` is a partial
transversal of `A` if there is an injection `φ : X → {0, …, n-1}` with `x ∈ A_{φ(x)}` for every
`x ∈ X`.

**Definition 2 (bipartite graphs), `Presents`, `incidence`, `incCol`, `incBlk`.**  A bipartite
graph with edges `{0, …, p-1}` is a pair of maps `col : Fin p → Fin m` (edge `j` is at the
element `col j`) and `blk : Fin p → Fin n` (edge `j` is at the set `blk j`); parallel edges are
allowed.  It presents `A` if `e ∈ A_i` exactly when some edge `j` has `col j = e` and
`blk j = i`.  The incidences `(i, e)` with `e ∈ A_i`, numbered by `Fin (|A₀| + ⋯ + |A_{n-1}|)`,
form a presentation (`presents_incidence`).

*Proof of `presents_incidence`.*  Step 1, `incidence A` is a bijection from
`Fin (|A₀| + ⋯ + |A_{n-1}|)` onto the set of pairs `⟨i, e⟩` with `e ∈ A_i` (Mathlib's
`Finset.equivFin` and `Finset.card_sigma`).  Step 2, for `e ∈ A_i` the pair `⟨i, e⟩` is the
image of some `j`, and then `col j = e`, `blk j = i`.  Step 3, conversely the pair of every `j`
lies in that set, so `col j ∈ A_{blk j}`.  ∎

**Definition 3 (the matroid `N_S`), `edgeMatroid`, `edgeMatroid_indep`.**  For `S ⊆ E`, `N_S`
is the matroid on the edges in which a set `J` is independent when it meets every element at
most once (`col` is injective on `J`) and only elements of `S` (`col(J) ⊆ S`): the partition
matroid of the elements (`colMatroid col` of `Rainbow/Partition.lean`) restricted to the edges
at `S`.  The blocks are `blk⁻¹(i)`, one for each set `A_i`; a rainbow independent set of `N_S`
is a matching of a part of `S` into the family.

**Lemma 4 (rank of `N_S`), `rk_edgeMatroid`.**  For every set `F` of edges, `r_{N_S}(F)` is the
number of elements of `S` that `F` meets.

*Proof.*  Step 1, the rank of `F` in a restriction `M ↾ R` is the rank of `F ∩ R` in `M`
(Mathlib's `restrict_eRk_eq'`).  Step 2, the rank of a set of edges in `colMatroid col` is the
number of elements it meets (`Partition.rk_eq`), and `F ∩ col⁻¹(S)` meets exactly the elements of
`S` that `F` meets.  ∎

**Lemma 5 (matchings and partial transversals).**  Let `(col, blk)` present `A`.
1. `image_subset_card_image`: a set `J` independent in `N_S` meets `|J|` elements, all in `S`.
2. `isRainbowIndep_mono`: a rainbow independent set of `N_S` is one of `N_T` for `S ⊆ T`.
3. `isPartialTransversal_image`: if `J` is rainbow independent in `N_S`, the set `col(J)` of the
   elements it meets is a partial transversal.
4. `exists_isRainbowIndep`: a partial transversal `X` is `col(J)` for a rainbow independent set
   `J` of `N_X`.
5. `nu_edgeMatroid`: `ν(N_X) = |X|` for a partial transversal `X`.

*Proof.*  Step 1, items 1 and 2 unfold the definition.  Step 2, item 3: for every `x ∈ col(J)`
choose `j_x ∈ J` with `col j_x = x` and put `φ(x) = blk j_x`.  The edge `j_x` joins `x` and
`φ(x)`, so `x ∈ A_{φ(x)}`.  If `φ(x) = φ(y)`, then `j_x = j_y` since `blk` is injective on `J`,
and `x = col j_x = col j_y = y`.  Step 3, item 4: let `φ` witness that `X` is a partial
transversal.  For `x ∈ X` the presentation gives an edge `g(x)` with `col g(x) = x` and
`blk g(x) = φ(x)`; put `J = g(X)`.  Then `col` is injective on `J` with `col(J) = X`, and `blk`
is injective on `J` since `φ` is.  Step 4, item 5: the set `J` of item 4 is rainbow independent
in `N_X` with `|J| = |col(J)| = |X|` (item 1), so `ν(N_X) ≥ |X|` (`card_le_nu`); a rainbow
independent `J'` with `|J'| = ν(N_X)` (`exists_card_eq_nu`) has `|J'| = |col(J')| ≤ |X|` by
item 1.  ∎

**Theorem 6 (augmentation), `exists_insert`.**  Let `(col, blk)` present `A`, and let `X`, `Y`
be partial transversals with `|X| < |Y|`.  Then `X + y` is a partial transversal for some
`y ∈ Y \ X`.

*Proof.*  Suppose not, and put `Q = Av(N_X)`.  Step 1, every edge `j` with `blk j ∈ Q` and
`col j ∈ Y` has `col j ∈ X`.  Indeed `blk j ∈ Av(N_X)` gives a rainbow independent set `J` of
`N_X` with `|J| = ν(N_X) = |X|` (Lemma 5(5)) that misses the block `blk j` (`mem_av`).  By Lemma
5(1), `col(J) ⊆ X` has `|J| = |X|` elements, so `col(J) = X`, and `j ∉ J`.  If `col j ∉ X`,
then `J + j` is rainbow (the block of `j` is missed by `J`) and independent in `N_{X + col j}`
(`col j ∉ col(J)`), so `col(J + j) = X + col j` is a partial transversal by Lemma 5(3), against
the assumption.  Step 2, Lemma `lem:avoidable`(2) for `N_X` (`card_av_add_nu`) and Lemma 4:
`|Q| + |X| = n + r_{N_X}(E_Q) = n + |col(E_Q) ∩ X|`.  Step 3, Lemma `lem:avoidable`(1) for `N_Y`
at `Q` (`card_add_nu_le`) and Lemma 4: `|Q| + |Y| ≤ n + |col(E_Q) ∩ Y|`.  Step 4, by Step 1,
`col(E_Q) ∩ Y ⊆ col(E_Q) ∩ X`, so Steps 2 and 3 give `|Y| ≤ |X|`, a contradiction.  ∎

**Theorem 7 (the transversal matroid), `transversal`, `transversal_indep`,
`transversal_ground`.**  The partial transversals of `A` are the independent sets of a matroid
`transversal A` on `E` with ground set `E`.

*Proof.*  Mathlib's `IndepMatroid.ofFinite` on the finite ground set `E`.  Step 1, the empty set
is a partial transversal (the empty map, `isPartialTransversal_empty`).  Step 2, a subset of a
partial transversal is one (restrict `φ`, `IsPartialTransversal.subset`).  Step 3,
augmentation: Theorem 6 for the presentation by the incidences (`presents_incidence`), the sets
read as `Finset`s (`exists_finset`).  ∎

**Theorem 8 (the rank is `ν`), `rk_eq_nu`.**  Let `(col, blk)` present `A`.  For every
`S ⊆ E`, `r(S) = ν(N_S)`: the rank of `S` in the transversal matroid is the largest number of
edges that meet every element at most once, only elements of `S`, and every set at most once.

*Proof.*  Step 1, `≤`: a basis `I` of `S` has `|I| = r(S)` (`card_eq_rk`) and is a partial
transversal inside `S`; Lemma 5(4) and 5(2) give a rainbow independent set `J` of `N_S` with
`|J| = |col(J)| = |I|`, so `r(S) ≤ ν(N_S)`.  Step 2, `≥`: a rainbow independent set `J` of `N_S`
with `|J| = ν(N_S)` meets `|J|` elements of `S` (Lemma 5(1)), which form a partial transversal
(Lemma 5(3)), an independent subset of `S`; so `ν(N_S) ≤ r(S)` (`card_le_rk`).  ∎

### 1.2 The rank circuit

The circuit reads the indicator vector `x = 1_S` and runs the circuit for `ν` of P6b
(`nuCircuit`) with the input as its context: the matroid `N_x = N_S` depends on the input.

**Lemma 9 (the rank query and the independence oracle).**  Let `edgesAt col e` be the list of
the edges at `e` in increasing order (`mem_edgesAt`); every edge is at one element, so
`Σ_e |edgesAt col e| = p` (`sum_length_edgesAt`).
1. `anyListB_impl`: from a vector `A` of `p` bits and a bit `a`, the bit
   `a ∨ (A_j for some j in a list l)` costs `|l|` gates.
2. `elemB_impl`: from `(x, A)`, the bit `x_e ∧ (A_j for some edge j at e)` costs
   `|edgesAt col e| + 1` gates.
3. `rkQueryB_impl`: from `(x, A)`, the number `rkQueryV col (x, A)` of elements `e` with `x_e`
   that `A` meets costs `p + m + popCost m` gates, on `⌈log₂(m+1)⌉` bits.
4. `rkQueryV_eq`: at `x = 1_S` and the indicator vector of a set `F` of edges, this number is
   `r_{N_S}(F)`.
5. The oracle `indepOfRankB (rkQueryB col)` (`indepOfRankB_impl` of `BoolAlg/Count.lean` on
   `rkQueryB_impl`) computes `indepOfRankV (rkQueryV col)` with `oracleCost m p = p + m +
   popCost m + popCost p + 5⌈log₂(p+1)⌉ + 1` gates.

*Proof.*  Step 1, item 1: one `∨` gate per entry of the list with the context `A` kept
(`Impl.foldCtx`), and the left fold of `∨` is `a ∨ (some entry)` (`foldl_or`, induction on the
list).  Step 2, item 2: item 1 on the edges at `e` from the constant `false`, then one `∧` with
`x_e`; `j` lies in `edgesAt col e` exactly when `col j = e`.  Step 3, item 3: item 2 for every
element (`Impl.tabSum`, `Σ_e (|edgesAt col e| + 1) = p + m`), then a population count of the `m`
bits (`vecPopcountB_impl`, `popCost m` gates).  Step 4, item 4: the elements counted are those
`e ∈ S` met by `F`, which is `r_{N_S}(F)` by Lemma 4.  Step 5, item 5: `indepOfRankB_impl`
(P6b), whose cost is the cost of the query plus `popCost p + 5⌈log₂(p+1)⌉ + 1`.  ∎

**Theorem 10 (the rank circuit), `rankCircuit`, `rankCircuit_spec`, `rankCircuit_eRk`,
`rankCost_le`.**  Let `(col, blk)` present `A` with `p` edges.  The Boolean circuit
`rankCircuit col blk = nuCircuit (fun _ => indepOfRankB (rkQueryB col)) blk`, the same
independence oracle as the exchange test of every `y`, has exactly
`n · roundCost p (oracleCost m p) + popCost p` gates, at most `36 (n+1)(p+1)²(p+m+1)`, and
outputs `r(S)` in binary for every `S ⊆ E`.

*Proof.*  Step 1, `nuCircuit_spec` (P6b) with the oracle of Lemma 9(5): the size is
`n · roundCost p (oracleCost m p) + popCost p` (`n` rounds, one for each block), and at every
input `x` at which the tests answer the exchange questions of a matroid `N` (`ExchOracle`), the
output is `ν(N)` in binary.  Step 2, at `x = 1_S` the oracle answers independence in `N_S`
(`indepOfRank_correct` with Lemma 9(4)), hence every exchange question
(`ExchOracle.of_indep`).  Step 3, `ν(N_S) = r(S)` by Theorem 8; in `ℕ∞` by `coe_rk`.  Step 4, the
bound: `oracleCost m p ≤ 28p + 23m + 1` (`popCost r ≤ 22r`, `⌈log₂(p+1)⌉ ≤ p`), so
`roundCost p (oracleCost m p) ≤ 36p³ + 23mp² + 13p² + 12p + 4`, and `36 (n+1)(p+1)²(p+m+1)`
equals `n(36p³ + 23mp² + 13p² + 12p + 4) + 22p` plus an explicit polynomial in `m, n, p` with
nonnegative coefficients (written out in the Lean proof and checked by `ring`); finally
`popCost p ≤ 22p`.  ∎

### 1.3 Signed tropical circuits

**Theorem 11 (Theorem A for transversal matroids), `theoremA_rankCircuit`,
`theoremA_cost_le`, `rank_le_card`.**  Let `(col, blk)` present `A` with `p` edges and let `M`
be the transversal matroid, of rank `k`.  Then `h_M` is computed at every `w ∈ ℝ^m` by a signed
tropical circuit of size at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`, where
`s = n · roundCost p (oracleCost m p) + popCost p` and `L = ⌈log₂(k+1)⌉`; this is at most
`120 (m+1)(n+1)(p+1)²(p+m+1)`.

*Proof.*  Step 1, `theoremA` with the rank circuit of Theorem 10 (`rankCircuit_eRk`) and the
ground set `E` (`transversal_ground`).  Step 2, `L ≤ k ≤ m` (`Nat.size k ≤ k`; a base has `k`
elements, `rank_le_card`).  Step 3, with `T = (n+1)(p+1)²(p+m+1) ≥ m + 1`, `s ≤ 36T` and
`L ≤ m`: `3ms + mL + 9m² + 4m + 4L + 1 ≤ 108mT + 10m² + 8m + 1 ≤ 120(m+1)T`, since
`mT ≥ m(m+1)` (`nlinarith`).  ∎

**Theorem 12 (Corollary `cor:classes`, transversal matroids), `transversal_rankCircuit`,
`theoremA_transversal`, `sum_card_add_le`.**  Let `A₀, …, A_{n-1} ⊆ E` with
`p = |A₀| + ⋯ + |A_{n-1}|`, and let `M` be the transversal matroid.
1. A Boolean circuit of size exactly `n · roundCost p (oracleCost m p) + popCost p`, which is at
   most `36 (n+1)(p+1)²(p+m+1) ≤ 36 (m+1)³(n+1)⁴`, outputs `r(S)` in binary for every `S ⊆ E`.
2. `h_M` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size at most
   `120 (m+1)(n+1)(p+1)²(p+m+1) ≤ 120 (m+1)⁴(n+1)⁴`.

*Proof.*  Step 1, the presentation by the incidences has `p` edges (`presents_incidence`);
Theorems 10 and 11 give the first bounds.  Step 2, `p ≤ nm` since `|A_i| ≤ m`, so
`p + 1 ≤ p + m + 1 ≤ (m+1)(n+1)` (`sum_card_add_le`); monotonicity (`gcongr`) and `ring` give
`36 (n+1)(p+1)²(p+m+1) ≤ 36 (m+1)³(n+1)⁴` and the same with `120 (m+1)` in front.  ∎


### 1.4 Gammoids (`Classes/TransversalGammoid.lean`)

Notation.  A digraph on the vertices `V = Fin v` is a set `arcs ⊆ V × V` of arcs `u → w`, with
`a = |arcs|`; `S ⊆ V` is a set of sources; the elements `E = Fin m` are placed at distinct
vertices by an injection `ι : Fin m ↪ Fin v`.

**Definition 13 (linkage), `IsLinked`.**  `X ⊆ V` is linked from `S` if there are pairwise
vertex-disjoint directed paths, one for each `x ∈ X`, each from a vertex of `S` to `x`; a path
may be the single vertex `x ∈ S`.  In Lean, path `x` is `path x 0 → ⋯ → path x (len x)` with
`path x 0 ∈ S`, `path x (len x) = x` and arcs between consecutive vertices, and
`path x i = path y j` (`x, y ∈ X`, `i ≤ len x`, `j ≤ len y`) only for `x = y` and `i = j` (the
paths are vertex-disjoint and their vertices are distinct).

**Lemma 14 (paths that leave `S` at once), `IsLinked.exists_avoid`.**  If `X` is linked from
`S`, there are such paths that meet `S` only at their first vertices.

*Proof.*  Step 1, for each `x` let `t(x)` be the last index `i ≤ len x` with `path x i ∈ S`
(`Nat.findGreatest`; `path x 0 ∈ S`).  Step 2, the paths `path x (t(x) + i)`,
`i ≤ len x - t(x)`, start in `S`, end at `x`, use arcs of the old paths, meet `S` only at
`i = 0`, and two of them meet only where the old ones did.  ∎

**Definition 15 (the family of Ingleton and Piff), `ipFamily`, `mem_ipFamily`.**
`A_w = {w} ∪ {u : u → w}` for `w ∉ S` and `A_w = ∅` for `w ∈ S`, a family of `v` sets of
vertices; `T` is its transversal matroid on `V`.

**Lemma 16 (the bases of `T`).**
1. `isPartialTransversal_iff`: for a family indexed by `V`, a set `B ⊆ V` is a partial
   transversal iff some map `f : V → V`, injective on `B`, has `b ∈ A_{f(b)}` for `b ∈ B`.
2. `card_le_of_isPartialTransversal`: a partial transversal of `(A_w)` has at most `|V \ S|`
   elements; `isPartialTransversal_compl`: `V \ S` is one.
3. `card_of_isBase`, `isBase_of_card`: the bases of `T` are the partial transversals with
   `|V \ S|` elements.

*Proof.*  Step 1, item 1: extend `φ` by the identity outside `B`, and conversely restrict `f`.
Step 2, item 2: `f` maps `B` injectively into `V \ S`, since `A_w = ∅` for `w ∈ S`; the identity
is a transversal map of `V \ S`, since `w ∈ A_w` for `w ∉ S`.  Step 3, item 3: a base has
`r_T(V)` elements (`card_base`) and `V \ S` is independent, so it has at least `|V \ S|`
elements, and at most by item 2.  A partial transversal with `|V \ S|` elements has no
independent extension `B + e` (it would have more elements), so it is a base
(`Matroid.Indep.isBase_of_forall_insert`).  ∎

**Theorem 17 (Ingleton and Piff), `isLinked_of_isBase`, `exists_isBase_of_isLinked`,
`dual_indep_iff_isLinked`.**  A set `X ⊆ V` is independent in the dual `T✶` if and only if it
is linked from `S`.

*Proof.*  Step 1, `X` is independent in `T✶` iff it misses some base of `T` (Mathlib's
`dual_indep_iff_exists'`).

Step 2, from a base to paths.  Let `B` be a base of `T` missing `X`, with transversal map `f`.
By Lemma 16, `f` maps `B` onto `V \ S`; choose `g(w) ∈ B` with `f(g(w)) = w` for `w ∉ S`.  Then
`g` is injective on `V \ S`, `g(w) ∈ A_w` (so `g(w) = w` or `g(w) → w`), and `g(w) ∈ B`.
Cancellation: if `g^i(x) = g^j(y)` for `x, y ∈ X`, all earlier iterates lying outside `S`, then
`i = j` and `x = y`, by induction on `i`: for `i = 0 < j` (or `j = 0 < i`) a vertex of `X` would
lie in `g(V \ S) ⊆ B`, and otherwise injectivity of `g` removes one step.  So the iterates
`g^i(x)` are distinct while they stay outside `S`, and since `V` is finite some iterate lies in
`S` (`not_injective_infinite_finite`); let `l(x)` be the least such index (`Nat.sInf`).  The
path of `x` is `g^{l(x)}(x) → ⋯ → g(x) → x`.  Each step `g(w) → w` is an arc: `g(w) = w` would be
a repetition.  Two paths meet only at equal `x` and equal positions, by cancellation.

Step 3, from paths to a base.  Take paths meeting `S` only at their first vertices (Lemma 14).
Let `B` consist of the vertices of the paths other than their last ones and of the vertices
outside `S` on no path, and let `f` send a vertex of a path other than its last one to its
successor and every other vertex to itself.  Then `b ∈ A_{f(b)}` for `b ∈ B` (an arc
`b → f(b)` with `f(b) ∉ S`, a non-first vertex of a path; or `f(b) = b ∉ S`); `f` is injective
on `B` (the paths are vertex-disjoint, and a vertex on no path is no successor); and
`f(B) ⊇ V \ S` (a vertex `w ∉ S` on a path is not its first vertex and is the successor of its
predecessor; a vertex outside `S` on no path is fixed).  So `B` is a partial transversal with at
least `|V \ S|` elements, a base by Lemma 16, and it misses `X`, since every `x ∈ X` is the last
vertex of its path.  ∎

**Theorem 18 (the gammoid), `gammoid`, `gammoid_ground`, `gammoid_indep`.**  `gammoid arcs S ι`
is the matroid `T✶` pulled back along `ι` (Mathlib's `Matroid.comap`).  Its ground set is `E`,
and a set `X ⊆ E` is independent iff `ι(X)` is linked from `S`.

*Proof.*  Step 1, `comap_indep_iff`: `X` is independent iff `ι(X)` is independent in `T✶` and
`ι` is injective on `X`, which holds.  Step 2, Theorem 17.  ∎

**Theorem 19 (the rank circuit of a gammoid), `vertexB`, `strictGammoidCircuit`,
`gammoidCircuit`, `gammoidCircuit_spec`, `sum_card_ipFamily_le`, `gammoidCost_le`, `ipBound_le`,
`gammoid_rankCircuit`.**  The Boolean circuit `gammoidCircuit arcs S ι` runs the dual rank
circuit (`dualRankCircuit` of E4, with `k = r_T(V)`) of the rank circuit of `T` (Theorem 10,
with `n = v` sets and `p = Σ_w |A_w|` incidences) on the vertex bits, vertex `u` reading the
input bit of the element at `u` and the constant `false` if there is none.  It has exactly
`v · roundCost p (oracleCost v p) + popCost p + v + 1 + 11 (v+1)⌈log₂(v+1)⌉` gates, at most
`48 (v+1)(v+a+1)²(2v+a+1) ≤ 48 (v+1)⁷`, and outputs `r(X)` in binary for every `X ⊆ E`.

*Proof.*  Step 1, `runB_num` (P6a) of the dual circuit after the free rearrangement `vertexB`,
and `circuitOf_num`: the size is that of the dual circuit, `dualRankCircuit_size` and
Theorem 10.  Step 2, at the input `1_X` the vertex bits are `1_{ι(X)}`, as `ι` is injective.
Step 3, `dualRankCircuit_rank` (E4) with `rankCircuit_eRk` gives `r_{T✶}(ι(X))`, which is
`r(X)` by Mathlib's `Matroid.eRk_comap`.  Step 4, the bound: `|A_w| ≤ 1 + |{u : u → w}|`, so
`p ≤ v + a` (`sum_card_ipFamily_le`, fibres of the arcs over their heads); `rankCost_le` gives
`36 (v+1)(p+1)²(p+v+1) ≤ 36 (v+1)(v+a+1)²(2v+a+1)`, and
`v + 1 + 11 (v+1)⌈log₂(v+1)⌉ ≤ 12 (v+1)² ≤ 12 (v+1)(v+a+1)²(2v+a+1)`.  Step 5, `a ≤ v²` gives
`v + a + 1 ≤ (v+1)²` and `2v + a + 1 ≤ (v+1)²` (`ipBound_le`).  ∎

**Theorem 20 (Theorem A for gammoids), `theoremA_gammoidCost_le`, `theoremA_gammoid`.**  For
the gammoid `M`, `h_M` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size at
most `160 (m+1)(v+1)(v+a+1)²(2v+a+1) ≤ 160 (v+1)⁸`.

*Proof.*  Step 1, `theoremA` with the circuit of Theorem 19 and `gammoid_ground`.  Step 2,
`L = ⌈log₂(k+1)⌉ ≤ k ≤ m ≤ v` (`rank_le_card`, and `m ≤ v` from the injection `ι`).  Step 3,
with `U = (v+1)(v+a+1)²(2v+a+1) ≥ m + 1` and `s ≤ 48 U`:
`3ms + mL + 9m² + 4m + 4L + 1 ≤ 144mU + 10m² + 8m + 1 ≤ 160(m+1)U`.  Step 4, `m + 1 ≤ v + 1` and
`U ≤ (v+1)⁷`.  ∎


## 2. Correspondence table

| Paper | Lean names | Module | Status |
|:--|:--|:--|:--|
| `cor:classes` item 6, transversal matroids: the matroid of partial transversals | `IsPartialTransversal`, `transversal`, `transversal_indep`, `transversal_ground`, `isPartialTransversal_empty`, `IsPartialTransversal.subset` | `Classes/Transversal.lean` | proved |
| augmentation (Edmonds and Fulkerson), here through `lem:avoidable` | `exists_insert` | same | proved |
| bipartite graph of a family; `N_S` and its rank | `Presents`, `incidence`, `incCol`, `incBlk`, `presents_incidence`, `edgeMatroid`, `edgeMatroid_indep`, `rk_edgeMatroid` | same | proved |
| matchings are rainbow independent sets | `image_subset_card_image`, `isRainbowIndep_mono`, `isPartialTransversal_image`, `exists_isRainbowIndep`, `nu_edgeMatroid` | same | proved |
| the rank as `ν` of a matroid with blocks | `rk_eq_nu` | same | proved |
| rank query and independence oracle of `N_S` | `edgesAt`, `mem_edgesAt`, `sum_length_edgesAt`, `foldl_or`, `anyListB`, `anyListB_impl`, `elemB`, `elemB_impl`, `rkQueryV`, `rkQueryB`, `rkQueryB_impl`, `rkQueryV_eq`, `oracleB`, `oracleCost`, `oracleB_impl` | same | proved |
| Boolean rank circuit, from `lem:observer` Step 4 | `rankCircuit`, `rankCircuit_spec`, `rankCircuit_eRk`, `rankCost_le` | same | proved |
| signed tropical circuit (Theorem A) | `rank_le_card`, `theoremA_cost_le`, `theoremA_rankCircuit` | same | proved |
| `cor:classes`, transversal matroids with `p = Σ|A_i|`: sizes `36 (n+1)(p+1)²(p+m+1)` and `120 (m+1)(n+1)(p+1)²(p+m+1)` | `sum_card_add_le`, `transversal_rankCircuit`, `theoremA_transversal` | same | proved |
| `cor:classes` item 6, gammoids: linkage | `IsLinked`, `IsLinked.exists_avoid` | `Classes/TransversalGammoid.lean` | proved |
| theorem of Ingleton and Piff | `ipFamily`, `mem_ipFamily`, `isPartialTransversal_iff`, `card_le_of_isPartialTransversal`, `isPartialTransversal_compl`, `card_of_isBase`, `isBase_of_card`, `isLinked_of_isBase`, `exists_isBase_of_isLinked`, `dual_indep_iff_isLinked` | same | proved |
| the gammoid | `gammoid`, `gammoid_ground`, `gammoid_indep` | same | proved |
| `cor:classes`, gammoids: sizes `48 (v+1)(v+a+1)²(2v+a+1)` and `160 (m+1)(v+1)(v+a+1)²(2v+a+1)` | `vertexB`, `strictGammoidCircuit`, `gammoidCircuit`, `gammoidCircuit_spec`, `sum_card_ipFamily_le`, `gammoidCost_le`, `ipBound_le`, `gammoid_rankCircuit`, `theoremA_gammoidCost_le`, `theoremA_gammoid` | same | proved |
| `cor:classes` item 6, general polynomial-time rank oracles (Pippenger and Fischer) | | | out of scope |


## 3. Differences from the paper

1. Item 6 of `cor:classes` treats transversal matroids and gammoids through the simulation of
   polynomial-time computation by circuits (Pippenger and Fischer), with no explicit size and no
   fixed description.  The formalization gives explicit circuits: for transversal matroids, the
   matroid intersection circuit of `lem:observer`, Step 4, on the matroid `N_S` of the
   incidences with the input as its context; for gammoids, the theorem of Ingleton and Piff,
   the dual circuit of item 4 and the transversal circuit.  Proposed replacement for item 6 of
   `cor:classes`, two items:

   > \item A transversal matroid, whose independent sets are the partial transversals of sets
   > $A_1,\ldots,A_n\subseteq E$, with $p=|A_1|+\cdots+|A_n|\le mn$: it has a Boolean rank
   > circuit of size at most $36(n+1)(p+1)^{2}(m+p+1)$, so $h_M$ has a signed tropical circuit
   > of size at most $120(m+1)(n+1)(p+1)^{2}(m+p+1)\le120(m+1)^{4}(n+1)^{4}$.
   > \item A gammoid, whose independent sets are the sets $X\subseteq E$ linked from $S$ in a
   > directed graph with $v$ vertices and $a$ arcs, where $S$ and $E$ are sets of vertices and
   > $X$ is linked from $S$ when $|X|$ vertex-disjoint directed paths lead from $S$ to $X$: it
   > has a Boolean rank circuit of size at most $48(v+1)(v+a+1)^{2}(2v+a+1)$, so $h_M$ has a
   > signed tropical circuit of size at most
   > $160(m+1)(v+1)(v+a+1)^{2}(2v+a+1)\le160(v+1)^{8}$.

   Proposed proofs, replacing the proof of item 6:

   > \emph{Item 6.}  Let $N_S$ be the matroid on the $p$ incidences $(e,i)$, $e\in A_i$, in
   > which a set is independent when it contains at most one incidence of each element and only
   > incidences of elements of $S$, with the blocks $R_i=\{(e,i):e\in A_i\}$.  A rainbow
   > independent set of $N_S$ is a matching of a part of $S$ into the sets, so $r(S)=\nu(N_S)$.
   > Step~4 of the proof of Lemma~\ref{lem:observer}, with the input as its context, computes
   > $\nu(N_S)$ with $n$ rounds; an independence test compares $|J|$ with
   > $r_{N_S}(J)=|\{e\in S:J\text{ contains an incidence of }e\}|$, which costs one disjunction
   > per incidence, one conjunction per element and two population counts, at most
   > $28p+23m+1$ gates.  The $n$ rounds of $p^{2}$ tests each, the shortest paths, the
   > exchanges and the final population count cost at most $36(n+1)(p+1)^{2}(m+p+1)$ gates,
   > and Theorem~\ref{thm:A} with $k\le m$ gives the second bound.

   > \emph{Item 7.}  By the theorem of Ingleton and Piff~\cite{oxley11}, a set of vertices is
   > linked from $S$ exactly when it is independent in the dual of the transversal matroid $T$
   > of the sets $A_w=\{w\}\cup\{u:u\to w\}$, $w\notin S$.  The bases of $T$ are the sets $B$
   > with a bijection $f$ from $B$ onto $V\setminus S$ such that $b\in A_{f(b)}$.  If such a
   > $B$ misses $X$ and $g=f^{-1}$, then for $x\in X$ the vertices $x,g(x),g(g(x)),\ldots$ are
   > distinct up to the first one in $S$, and the paths $\cdots\to g(x)\to x$ are
   > vertex-disjoint.  Conversely, for vertex-disjoint paths from $S$ to $X$ that meet $S$ only
   > at their first vertices, the vertices of the paths other than their last ones, sent to
   > their successors, and the vertices outside $S$ on no path, sent to themselves, form such a
   > $B$.  Item 6 for $T$, with $v$ sets and at most $v+a$ incidences, the dual circuit of
   > item 4, and the input bits placed at the vertices of $E$ give a rank circuit of size at
   > most $36(v+1)(v+a+1)^{2}(2v+a+1)+12(v+1)^{2}\le48(v+1)(v+a+1)^{2}(2v+a+1)$, and
   > Theorem~\ref{thm:A} with $k\le m\le v$ gives the second bound.

   The general statement can become a remark after the corollary, unformalized: "More
   generally, every matroid whose rank is computed in time polynomial in $m$ and in the length
   of a fixed description has a Boolean rank circuit of size polynomial in these two
   quantities~\cite{pippenger-fischer79}."

   Optional sentence on the matroid property, which the formalization proves this way: "That
   the partial transversals form a matroid~\cite{schrijver03} also follows from
   Lemma~\ref{lem:avoidable}: if $X$ and $Y$ are partial transversals with $|X|<|Y|$ and no
   $X+y$ with $y\in Y\setminus X$ is one, every element of $Y$ in a set of $Q=\Av(N_X)$ lies
   in $X$, and items 1 and 2 of the lemma at $Q$ give
   $|Q|+|Y|\le n+|Y\cap\Gamma(Q)|\le n+|X\cap\Gamma(Q)|=|Q|+|X|$, where $\Gamma(Q)$ is the
   union of the sets in $Q$."

   The introduction sentence "and every class with a polynomial-time rank oracle on a fixed
   description has polynomial-size rank circuits (Corollary~\ref{cor:classes})" can read
   "transversal matroids and gammoids have rank circuits of polynomial size by the matroid
   intersection circuit of Section~\ref{sec:circuit} (Corollary~\ref{cor:classes})".  In
   Section~\ref{sec:checks}, "items 1 to 5 of Corollary~\ref{cor:classes}" becomes "items 1 to
   7".

2. The size counts the matroid intersection circuit with exact gate counts (P6b): `n` rounds,
   each with `p(p-1)` arc tests and `p` sink tests on the `p` incidences, then a population
   count of the final matching; no final exchange graph and no guard are needed for `ν` alone
   (`nuCircuit`).  The rounds number `n`, the number of blocks; `ν(N_S) ≤ min(m, n)`.

3. The statements hold for every bipartite graph presenting the family, parallel edges and empty
   or repeated sets allowed (`Presents`); the size is then in terms of its number of edges.
   `N_S` has ground set the edges at `S`, not all edges; Lemma `lem:avoidable` and the circuit
   of P6b hold for matroids whose ground set is contained in `E` (P2, difference 2).  No change
   to the paper.

4. Gammoids: the definition is the usual one with paths from `S` to `X` (Oxley uses paths from
   `X` to the target set; reversing the arcs exchanges the two).  A path may pass through other
   vertices of `S`; Lemma 14 removes this.  The family of Ingleton and Piff is indexed by all
   `v` vertices, with `A_w = ∅` for `w ∈ S`, so the transversal circuit runs `v` rounds rather
   than `|V \ S|`; this only affects the constant.  The ground set `E ⊆ V` is the image of
   `ι : Fin m ↪ Fin v`.

5. The rank `k` of a transversal matroid is at most `min(m, n)`; the proofs use `k ≤ m` for
   `L = ⌈log₂(k+1)⌉`.  No change to the paper.


## 4. Module line counts

| Module | Lines |
|:--|:--|
| `SignedTropical/Classes/Transversal.lean` | 554 |
| `SignedTropical/Classes/TransversalGammoid.lean` | 490 |


## 5. Not done, and why

* Every item of the assignment is proved, including the optional gammoids.
* The general class "rank computable in polynomial time" (simulation of computations by
  circuits, Pippenger and Fischer) is out of scope, as in E4.
* The exponents are not optimized: the transversal circuit tests independence of all `p²` pairs
  per round (the exchange graph is built in full, P6b), and the gammoid bound uses `p ≤ v + a`.


## 6. API for later agents

Namespace `SignedTropical.Classes.Transversal`; `open SignedTropical SignedTropical.Rainbow
SignedTropical.Rainbow.MI SignedTropical.Classes.Transversal`.  Variables
`A : Fin n → Finset (Fin m)`, `col : Fin p → Fin m`, `blk : Fin p → Fin n`,
`hA : Presents A col blk`; for gammoids `arcs : Finset (Fin v × Fin v)`, `S : Finset (Fin v)`,
`ι : Fin m ↪ Fin v`.

* `IsPartialTransversal A (X : Set (Fin m)) : Prop`; `transversal A : Matroid (Fin m)`;
  `transversal_indep : (transversal A).Indep X ↔ IsPartialTransversal A X` (`Iff.rfl`);
  `transversal_ground : (transversal A).E = Set.univ` (`rfl`).
* `Presents A col blk := ∀ e i, e ∈ A i ↔ ∃ j, col j = e ∧ blk j = i`;
  `incCol A`, `incBlk A : Fin (∑ i, (A i).card) → _`, `presents_incidence A`.
* `edgeMatroid col S := (colMatroid col).restrict {j | col j ∈ S}`;
  `edgeMatroid_indep : Indep J ↔ Set.InjOn col J ∧ ∀ j ∈ J, col j ∈ S`;
  `rk_edgeMatroid col S F : rk (edgeMatroid col S) F = #((F.filter (col · ∈ S)).image col)`.
* `exists_insert hA hX hY hXY : ∃ y ∈ Y, y ∉ X ∧ IsPartialTransversal A ↑(insert y X)`.
* `nu_edgeMatroid hA hX : nu (edgeMatroid col X) blk = X.card`;
  `rk_eq_nu hA S : rk (transversal A) S = nu (edgeMatroid col S) blk`.
* `oracleCost m p`; `indepOfRankB_impl (rkQueryB_impl col) : Impl ((vecR m).prod (vecR p))
  bitR (indepOfRankB (rkQueryB col)) (oracleCost m p) (indepOfRankV (rkQueryV col))` (up to the
  form of the cost);
  `rkQueryV_eq col S F : rkQueryV col (indicator S, indicator F) = rk (edgeMatroid col S) F`.
* `rankCircuit col blk : Circuit BoolOp m`; `rankCircuit_spec hA : size = n * roundCost p
  (oracleCost m p) + popCost p ∧ ∀ S, bitsVal (eval (indicator S)) = rk (transversal A) S`;
  `rankCircuit_eRk hA S` (the hypothesis of `theoremA`); `rankCost_le m n p : n * roundCost p
  (oracleCost m p) + popCost p ≤ 36 * (n + 1) * (p + 1) ^ 2 * (p + m + 1)`.
* `theoremA_rankCircuit hA`, `transversal_rankCircuit A hp`, `theoremA_transversal A hp`
  (`hp : ∑ i, (A i).card = p`).
* Gammoids: `IsLinked arcs S X`; `ipFamily arcs S`; `dual_indep_iff_isLinked :
  (transversal (ipFamily arcs S))✶.Indep ↑X ↔ IsLinked arcs S X`; `gammoid arcs S ι :
  Matroid (Fin m)`, `gammoid_ground`, `gammoid_indep : (gammoid arcs S ι).Indep ↑X ↔
  IsLinked arcs S (X.map ι)`; `gammoidCircuit arcs S ι`, `gammoidCircuit_spec hp` (exact size
  and rank outputs, `hp : ∑ w, (ipFamily arcs S w).card = p`); `gammoid_rankCircuit arcs S ι`
  and `theoremA_gammoid arcs S ι` (the bounds of Theorems 19 and 20).
