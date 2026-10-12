# P2: exchange graphs and avoidable blocks (Lemma `lem:avoidable`)

Natural-language companion of `SignedTropical/Rainbow/Exchange.lean`, namespace
`SignedTropical.Rainbow.Exchange`.  Sources: `daishu/paper/greedy_intersection.tex`, Lemma
`lem:avoidable` and its proof, and Step 4 of the proof of Lemma `lem:observer` (the augmenting
path algorithm); Lawler, *Matroid intersection algorithms* (1975); Schrijver, *Combinatorial
Optimization*, Corollary 39.13a and Theorem 41.2.

Lemma `lem:avoidable` of the paper:

> Let `N` be a matroid on `E` and `ν = ν(N)`.
> 1. `|Q| - r_N(E_Q) ≤ k - ν` for every `Q ⊆ [k]`.
> 2. `|Av(N)| - r_N(E_{Av(N)}) = k - ν`.
> 3. `Av(N) ⊆ Q` for every `Q` attaining equality in item 1.

Build status: `lake build SignedTropical.Rainbow.Exchange` succeeds with no error and no
warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`
or `opaque`.  Every main theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (checked with `#print axioms` for the 26 theorems named in Sections 1.1 to 1.9).
The module imports only `SignedTropical.Rainbow.Defs` and uses its definitions unchanged.

Notation.  `E = {0, ..., m-1}` (Lean `Fin m`), `[k] = {0, ..., k-1}` (Lean `Fin k`), and
`blk : E → [k]`; block `b` is `R_b = blk⁻¹(b)`, possibly empty.  `N` is a matroid whose ground
set `N.E` is contained in `E` (Lean `Matroid (Fin m)`, no hypothesis on `N.E`); the paper's case
is `N.E = E`.  `r_N(S)` is the rank (Phase 1 `rk N S`), equal to `r_N(S ∩ N.E)`, and `cl` is
the closure of `N`.  From `Rainbow/Defs.lean`:

* `blocksMet blk S`: `blk(S)`, the blocks met by `S`; `M_S = [k] \ blk(S)` is the set of
  blocks missed by `S`;
* `IsRainbow blk S`: `blk` is injective on `S`; `blockSet blk Q`: `E_Q = blk⁻¹(Q)`;
* `IsRainbowIndep N blk I`: `I` is independent in `N` and rainbow;
* `nu N blk`: `ν(N)`, the largest size of a rainbow independent set;
* `Av N blk`: `Av(N)`, the blocks missed by some rainbow independent set of size `ν(N)`.

`I - x + y` is `(I \ {x}) ∪ {y}` (Lean `insert y (I \ {x})`) and `I + y` is `I ∪ {y}`.
`I ∆ P = (I \ P) ∪ (P \ I)` is the symmetric difference (Mathlib `symmDiff`,
`Finset.symmDiff_def`): the set obtained from `I` by removing the elements of `P` that lie in
`I` and adding the elements of `P` outside `I`.


## 1. Results

### 1.1 Exchange along a path without shortcuts

**Lemma 1 (Schrijver, Corollary 39.13a).**  `indep_exchange`.  Let `M` be a matroid on any
type, `J` independent, `t ∈ ℕ`, and `x_i ∈ J`, `y_i ∉ J` for `i < t`, such that `J - x_i + y_i`
is independent for every `i < t` and `J - x_i + y_j` is dependent whenever `j < i < t`.  Then
`(J \ {x_i : i < t}) ∪ {y_i : i < t}` is independent.

**Lemma 2.**  `indep_insert_sdiff_iff`.  Let `J` and `J'` be independent, `K ⊆ J`, `K ⊆ J'`,
`y ∈ cl(K)`, `y ∉ J` and `y ∉ J'`.  Then for every `e`, `(J + y) \ {e}` is independent if and
only if `(J' + y) \ {e}` is independent.

*Proof of Lemma 2.*  Step 1, `K` is independent and `y ∈ cl(K) \ K`, so the fundamental
circuit `C = C(y, K)` is a circuit contained in `K + y`.  Step 2, `y ∈ cl(J) \ J`, and for such
`y` the set `(J + y) \ {e}` is independent exactly when `e ∈ C(y, J)`, the unique circuit in
`J + y` (Mathlib's `Indep.mem_fundCircuit_iff`); likewise for `J'`.  Step 3, `C ⊆ K + y ⊆ J + y`,
so `C = C(y, J)` by uniqueness (`IsCircuit.eq_fundCircuit_of_subset`), and likewise
`C = C(y, J')`.  Both conditions say `e ∈ C`.

*Proof of Lemma 1.*  Induction on `t`, for all `J`.

Step 1, `t = 0`: the set is `J`.

Step 2, the last pair is exchanged first.  Let pairs `(x_i, y_i)`, `i ≤ t`, be given and put
`J' = J - x_t + y_t`, independent by hypothesis.  By hypothesis `J - x_t + y_i` is dependent
for every `i < t`.  Hence `x_i ≠ x_t` and `y_i ≠ y_t` for `i < t`: either equality would make
`J - x_t + y_i` equal to the independent set `J - x_i + y_i`, respectively `J - x_t + y_t`.  So
`x_i ∈ J'` and `y_i ∉ J'` for `i < t`.

Step 3, every `y_i` with `i < t` lies in `cl(J - x_t)`.  Otherwise `(J - x_t) + y_i` would be
independent, since `J - x_t` is independent, `y_i ∉ J - x_t`, and `y_i` lies in the ground set
(it lies in the independent set `J - x_i + y_i`); but this set is `J - x_t + y_i`, which is
dependent.

Step 4, the first `t` pairs have the same arcs for `J` and `J'`: for `i, j < t`, `J - x_j + y_i`
is independent if and only if `J' - x_j + y_i` is.  This is Lemma 2 with `K = J - x_t`, which
is contained in `J` and in `J'`, the element `y_i` (Step 3) and `e = x_j`; here `y_i ≠ x_j`, so
`J - x_j + y_i = (J + y_i) \ {x_j}`.

Step 5, the induction hypothesis for `J'` and the pairs `(x_i, y_i)`, `i < t`, whose hypotheses
hold by Steps 2 and 4, gives that `(J' \ {x_i : i < t}) ∪ {y_i : i < t}` is independent.  Since
`y_t ∉ J` is none of the `x_i`, this set is `(J \ {x_i : i ≤ t}) ∪ {y_i : i ≤ t}`.

### 1.2 The exchange graph (Step 2 of the proof of `lem:avoidable`)

**Definition 3.**  For `I ⊆ E`:

* `Arc N blk I u v`, an arc `u → v`: either `u ∉ I`, `v ∈ I` and `I - v + u` is independent in
  `N` (the paper's arc `y → x`), or `u ∈ I`, `v ∉ I` and `blk(v) = blk(u)` (the paper's arc
  `x → y`);
* `IsSource blk I y`: `y` lies in a block missed by `I`, that is `blk(y) ∉ blk(I)`;
  `isSource_iff`: equivalently `y ∉ I` and `blk(y) ∉ blk(I)`;
* `IsSink N I y`: `y ∉ I` and `I + y` is independent;
* `layer N blk I d`, the breadth-first layers: `L_0` is the set of sources, and
  `L_{d+1} = L_d ∪ {v : u → v for some u ∈ L_d}`;
* `distance N blk I y ∈ ℕ ∪ {∞}`: the least `d` with `y ∈ L_d`, and `∞` if there is none;
* `reachSet N blk I`: the set `R` of the elements reachable from a source by a directed path;
* `IsShortestPath N blk I v n`, for `v : ℕ → E`: `v_i → v_{i+1}` for every `i < n`, and
  `v_i` has distance exactly `i` for every `i ≤ n`;
* `avOf N blk I`: `A' = M_I ∪ blk(I ∩ R)`.

Basic facts: `IsSource.notMem` (a source lies outside `I`), `Arc.mem_iff` (an arc joins `I` and
its complement), `Arc.mem_blk_eq` (an arc into the complement of `I` starts in `I`, in the same
block), `arc_iff_indep` (for `u ∉ I` and `v ∈ I`, `u → v` exactly when `I - v + u` is
independent).

### 1.3 Layers, distance and reachability

**Proposition 4.**

1. `mem_layer_zero`, `mem_layer_succ`: the defining equations of the layers; `layer_mono`: the
   layers increase; `exists_arc_of_mem_layer_succ`: an element of `L_{d+1} \ L_d` has an
   in-neighbour in `L_d`.
2. `le_distance_iff`: `d ≤ distance(y)` if and only if `y ∉ L_j` for every `j < d`.
   `distance_le_iff`: `distance(y) ≤ d` if and only if `y ∈ L_d`.  `distance_eq_iff`:
   `distance(y) = d` if and only if `y ∈ L_d` and `y ∉ L_j` for every `j < d`.
3. `mem_reachSet_iff_exists_layer`: `y ∈ R` if and only if `y ∈ L_d` for some `d`;
   `distance_lt_top_iff`: `distance(y) < ∞` if and only if `y ∈ R`.
4. `layer_subset_layer_card`: `L_d ⊆ L_m` for every `d`; `reachSet_eq_layer`: `R = L_m`.

*Proof.*  Step 1, item 1 unfolds the definition; monotonicity holds since `L_d ⊆ L_{d+1}`.
Step 2, item 2 unfolds the infimum; `distance_le_iff` uses that the layers increase.  Step 3,
item 3: along a path from a source `s`, `s ∈ L_0` and an arc from `L_d` ends in `L_{d+1}`;
conversely, by induction on `d`, an element of `L_0` is a source, and an element of `L_{d+1}`
lies in `L_d` or is the head of an arc from `L_d`, whose tail is reachable.  Step 4, some
`j ≤ m` has `L_{j+1} = L_j`: otherwise `L_0 ⊊ L_1 ⊊ ... ⊊ L_{m+1}`, so `|L_{m+1}| ≥ m + 1 > |E|`.
Step 5, `L_{d+1}` depends only on `L_d` (`layer_succ_congr`), so `L_{j+i} = L_j` for every `i`;
hence `L_d ⊆ L_m` both for `d ≤ j` (monotonicity) and for `d ≥ j` (`L_d = L_j`).  Item 4
follows with item 3.

### 1.4 Shortest paths

**Lemma 5.**  `isShortestPath_of_pred`.  If `v_n ∈ L_n`, `v_n ∉ L_j` for every `j < n`, and
`v_i ∈ L_i` with `v_i → v_{i+1}` for every `i < n`, then `v` is a shortest path of length `n`.

*Proof.*  Step 1, if `v_i ∈ L_j` with `j < i ≤ n`, then following the arcs
`v_i → ... → v_n` gives `v_n ∈ L_{j+n-i}` with `j + n - i < n`, a contradiction (induction on
`n - i`).  Step 2, so `v_i` has distance exactly `i`: `v_i ∈ L_i` by hypothesis, and
`v_i ∉ L_j` for `j < i` by Step 1.

**Lemma 6 (a path chosen backwards by a rule is a shortest path).**  `isShortestPath_of_rule`.
Let `pred : ℕ → E → E` satisfy `pred i y ∈ L_i` and `pred i y → y` whenever
`y ∈ L_{i+1} \ L_i`.  If `v_d ∈ L_d`, `v_d ∉ L_j` for every `j < d`, and
`v_i = pred i (v_{i+1})` for every `i < d`, then `v` is a shortest path of length `d`.

*Proof.*  Step 1, downward induction on `l ≤ d`: `v_{d-l}` has distance exactly `d - l`.  For
`l = 0` this is the hypothesis.  If `v_{i+1}` has distance exactly `i + 1`, then
`v_{i+1} ∈ L_{i+1} \ L_i`, so `v_i = pred i (v_{i+1}) ∈ L_i` and `v_i → v_{i+1}`; and
`v_i ∈ L_j` with `j < i` would give `v_{i+1} ∈ L_{j+1}` with `j + 1 < i + 1`.  Step 2, Lemma 5.

**Definition 7.**  `leastPred N blk I i y`: the in-neighbour of `y` in `L_i` of least index,
and `y` if there is none.  `backPath N blk I d y : ℕ → E`, by recursion on `d`:
`backPath 0 y i = y`, and `backPath (d+1) y i` is `backPath d (leastPred d y) i` for `i ≤ d`
and `y` otherwise.

**Lemma 8.**  `leastPred_spec`: if `y ∈ L_{i+1} \ L_i`, then `leastPred i y ∈ L_i` and
`leastPred i y → y`.  `backPath_self`: `backPath d y d = y`.  `backPath_pred`:
`backPath d y i = leastPred i (backPath d y (i + 1))` for `i < d`.

*Proof.*  Step 1, the in-neighbours of `y` in `L_i` form a nonempty set
(`exists_arc_of_mem_layer_succ`), and its least element belongs to it.  Step 2, `backPath_self`
by cases on `d`, and `backPath_pred` by induction on `d`, separating `i < d` and `i = d` in the
step from `d` to `d + 1`.

**Proposition 9.**

1. `exists_isShortestPath`: every `y` of distance exactly `d` is the end of the shortest path
   `backPath d y` of length `d` (Lemma 6 with `pred = leastPred`, Lemma 8).
   `exists_isShortestPath_of_mem_reachSet`: every `y ∈ R` is the end of a shortest path.
2. `isShortestPath_iff`: `v` is a shortest path of length `n` if and only if `v_0` is a
   source, `v_i → v_{i+1}` for every `i < n`, and `distance(v_n) = n`.

*Proof of item 2.*  Step 1, following the path for `l` steps from `v_i ∈ L_j` stays in
`L_{j+l}`.  Step 2, from `v_0 ∈ L_0` this gives `v_i ∈ L_i`.  Step 3, `v_i ∈ L_j` with `j < i`
would give `v_n ∈ L_{j+n-i}` with `j + n - i < n`, against `distance(v_n) = n`.

**Proposition 10 (shape of a shortest path).**  Let `v` be a shortest path of length `n` and
`P = {v_0, ..., v_n}` (Lean `(range (n + 1)).image v`).  Namespace `IsShortestPath`:

1. `isSource`: `v_0` is a source; `mem_layer`, `notMem_layer`: `v_i ∈ L_i` and `v_i ∉ L_j`
   for `j < i ≤ n`;
2. `injOn`: `v_i = v_j` with `i, j ≤ n` implies `i = j`, since the distances differ;
3. `not_arc`, no shortcuts: there is no arc `v_j → v_i` with `j + 1 < i ≤ n`, since it would
   put `v_i` in `L_{j+1}`;
4. `mem_iff`: `v_i ∈ I` if and only if `i` is odd, since `v_0 ∉ I` and every arc joins `I`
   and its complement;
5. `image_inter`, `image_sdiff`, `coe_symmDiff`: `P ∩ I = {v_{2i+1} : i < ⌊(n+1)/2⌋}`,
   `P \ I = {v_{2i} : i ≤ ⌊n/2⌋}`, and so `I ∆ P = (I \ {v_{2i+1}}) ∪ {v_{2i}}` with these
   ranges;
6. `card_symmDiff`: `|I ∆ P| + ⌊(n+1)/2⌋ = |I| + ⌊n/2⌋ + 1`, by items 2 and 5.

### 1.5 Exchange along a shortest path

**Lemma 11 (the rainbow half).**  `IsShortestPath.isRainbow_symmDiff`.  If `I` is rainbow and
`v` is a shortest path, then `I ∆ P` is rainbow.

*Proof.*  Step 1, every element of `P \ I` is `v_0`, whose block is missed by `I`, or `v_{i+1}`
with `v_i ∈ I` and `blk(v_{i+1}) = blk(v_i)` (`Arc.mem_blk_eq`).  Step 2, an element `a` of
`I \ P` and an element `b` of `P \ I` lie in different blocks: if `b = v_0`, the block of `b`
is missed by `I` and the block of `a` is not; if `b = v_{i+1}`, then `blk(a) = blk(v_i)` would
force `a = v_i ∈ P`, as `I` is rainbow.  Step 3, two elements of `P \ I` in one block are
equal: `v_0` and `v_{j+1}` cannot share a block, since the block of `v_{j+1}` is met by `I`;
if `v_{i+1}` and `v_{j+1}` share a block, then so do `v_i, v_j ∈ I`, so `v_i = v_j` and
`i = j` (`injOn`).  Step 4, two elements of `I \ P` in one block are equal, as `I` is rainbow.

**Lemma 12 (the matroid half, ending in `I`).**  `IsShortestPath.indep_symmDiff_of_mem`.  If
`I` is independent, `v` is a shortest path of length `n` and `v_n ∈ I`, then `I ∆ P` is
independent.

*Proof.*  Step 1, `n = 2s + 1` is odd (`mem_iff`), and
`I ∆ P = (I \ {v_{2i+1} : i ≤ s}) ∪ {v_{2i} : i ≤ s}` (`coe_symmDiff`).  Step 2, Lemma 1 with
`J = I`, `x_i = v_{2i+1}` and `y_i = v_{2i}` for `i ≤ s`: `x_i ∈ I` and `y_i ∉ I` by
`mem_iff`; `I - x_i + y_i` is independent by the arc `v_{2i} → v_{2i+1}` (`arc_iff_indep`);
for `j < i`, `I - x_i + y_j` is dependent, since an arc `v_{2j} → v_{2i+1}` would be a
shortcut (`not_arc`, `2j + 1 < 2i + 1`).

**Lemma 13 (the matroid half, ending in a sink).**  `IsShortestPath.indep_symmDiff_of_sink`.  If
`I` is independent, `v` is a shortest path of length `n`, `v_n` is a sink and no `v_i` with
`i < n` is a sink, then `I ∆ P` is independent.

*Proof.*  Step 1, `n = 2s` is even, since `v_n ∉ I`.  The set `J = I + v_n` is independent,
and `v_n` lies in the ground set and not in `cl(I)`.  Put `x_i = v_{2i+1}` and `y_i = v_{2i}`
for `i < s`.  Step 2, every `y_i` lies in `cl(I)`: otherwise `I + y_i` would be independent and
`y_i` would be a sink.  Step 3, `J - x_i + y_i` is independent: `I - x_i + y_i` is independent
(the arc), `v_n` does not lie in it (`v_n ∉ I`, and `v_n ≠ y_i` by `injOn`), and
`v_n ∉ cl(I - x_i + y_i)`, since this closure is contained in `cl(I)` by Step 2.  Step 4, for
`j < i < s`, `J - x_i + y_j` contains `I - x_i + y_j`, which is dependent by `not_arc`.  Step 5,
Lemma 1 for `J` and the pairs `(x_i, y_i)`, `i < s`, shows that
`(J \ {x_i : i < s}) ∪ {y_i : i < s}` is independent.  As `v_n` is none of the `x_i`, this set
is `(I \ {v_{2i+1} : i < s}) ∪ {v_{2i} : i ≤ s} = I ∆ P`.

**Proposition 14 (Step 3 of the proof of `lem:avoidable`).**  `IsShortestPath.exchange`.  Let
`I` be rainbow independent and `v` a shortest path of length `n` with `v_n ∈ I`.  Then `I ∆ P`
is rainbow independent, `|I ∆ P| = |I|`, `I ∆ P` meets the block of the source `v_0`, and
`I ∆ P` misses the block of `v_n`.

*Proof.*  Step 1, `I ∆ P` is rainbow independent by Lemmas 11 and 12.  Step 2, `n` is odd, so
`|I ∆ P| = |I|` (`card_symmDiff`).  Step 3, `v_0 ∈ P \ I ⊆ I ∆ P`.  Step 4, the block of `v_n`
is missed.  An element of `I \ P` in this block would be `v_n` (`I` is rainbow), which lies in
`P`.  An element of `P \ I` is `v_0`, whose block is missed by `I` while the block of `v_n` is
met, or `v_{i+1}` with `v_i ∈ I` and `blk(v_i) = blk(v_{i+1}) = blk(v_n)`; then `v_i = v_n`, so
`i = n` (`injOn`), against `i + 1 ≤ n`.

### 1.6 Augmentation (Lawler; Schrijver, Theorem 41.2)

**Theorem 15 (augmentation along a shortest path).**  `IsShortestPath.augment`.  Let `I` be
rainbow independent and `v_0 → ... → v_n` a path on which `v_i` has distance exactly `i` (so
`v_0` is a source), such that `v_n` is a sink and `n ≤ distance(y)` for every sink `y`.  Then
`I ∆ {v_0, ..., v_n}` is rainbow independent of size `|I| + 1`.

*Proof.*  Step 1, no `v_i` with `i < n` is a sink, since its distance is `i < n`.  Step 2,
`I ∆ P` is independent by Lemma 13 and rainbow by Lemma 11.  Step 3, `n` is even since
`v_n ∉ I`, so `|I ∆ P| = |I| + n/2 + 1 - n/2 = |I| + 1` (`card_symmDiff`).

**Theorem 16 (augmentation, in the form a circuit uses).**  `augment`.  Let `I` be rainbow
independent, `d ∈ ℕ` and `v : ℕ → E` such that `v_d` is a sink in `L_d`, no sink lies in `L_j`
for `j < d`, and, for every `i < d`, `v_i ∈ L_i` and `v_i → v_{i+1}` (any choice of such a
predecessor).  Then `I ∆ {v_0, ..., v_d}` is rainbow independent of size `|I| + 1`.

`augment_of_pred`: the same conclusion when the predecessors are chosen by a rule `pred` as in
Lemma 6, `v_i = pred i (v_{i+1})` for `i < d`, for instance `pred = leastPred`.

*Proof.*  Step 1, `v_d` is a sink, so it lies in no `L_j` with `j < d`, and Lemma 5 (for
`augment`) or Lemma 6 (for `augment_of_pred`) makes `v` a shortest path.  Step 2, every sink
lies in no `L_j` with `j < d`, so its distance is at least `d` (`le_distance_iff`).  Step 3,
Theorem 15.

### 1.7 One round of the augmenting path algorithm

**Definition 17.**  `augStep N blk I`, one round with least-index choices: if some layer
contains a sink, let `d` be the least such layer, `y` the sink of least index in `L_d`, and
`P = {backPath d y i : i ≤ d}`; the round returns `I ∆ P`.  Otherwise it returns `I`.

**Proposition 18.**  `augStep_spec`.  If `I` is rainbow independent, then `augStep I` is
rainbow independent, `|augStep I| ≥ |I|`, and `|augStep I| = |I| + 1` when some sink is
reachable from a source.  `exists_augment`: if a sink is reachable from a source, some rainbow
independent set has `|I| + 1` elements.

*Proof.*  Step 1, if some layer contains a sink, no sink lies in `L_j` for `j < d` by the
choice of `d`, and `y ∈ L_d` is a sink; `augment_of_pred` with `pred = leastPred` and
`v = backPath d y` (Lemma 8) gives a rainbow independent set of size `|I| + 1`.  Step 2,
otherwise the round returns `I`, and no sink is reachable from a source, since a reachable sink
lies in some layer (Proposition 4(3)).  Step 3, `exists_augment` takes `augStep I`.

### 1.8 Maximality and Lemma `lem:avoidable`

Basic facts: `isRainbowIndep_empty`; `card_le_nu` (a rainbow independent set has at most `ν`
elements); `exists_card_eq_nu` (some rainbow independent set has `ν` elements); `mem_av`
(unfolding `Av`).

**Lemma 19 (Steps 1 and 5).**  `card_add_card_le`.  For a rainbow independent `J` and
`Q ⊆ [k]`, `|J| + |Q ∪ M_J| ≤ k + r_N(E_Q)`.

*Proof.*  Step 1, `J ∩ E_Q` is independent and contained in `E_Q`, so
`|J ∩ E_Q| ≤ r_N(E_Q)` (Phase 1 `card_le_rk`).  Step 2, `blk` is injective on `J \ E_Q`, and
`blk(J \ E_Q)` is disjoint from `Q` (an element outside `E_Q` has its block outside `Q`) and
from `M_J` (the blocks of elements of `J` are met by `J`); so
`|J \ E_Q| + |Q ∪ M_J| = |blk(J \ E_Q) ∪ Q ∪ M_J| ≤ k`.  Step 3, add the two inequalities,
using `|J| = |J \ E_Q| + |J ∩ E_Q|`.

**Theorem 20 (Lemma `lem:avoidable`(1)).**  `card_add_nu_le`.  For every `Q ⊆ [k]`,
`|Q| + ν(N) ≤ k + r_N(E_Q)`, that is `|Q| - r_N(E_Q) ≤ k - ν(N)`.

*Proof.*  Lemma 19 for a rainbow independent `J` with `|J| = ν`, and `|Q| ≤ |Q ∪ M_J|`.

**Theorem 21 (Lemma `lem:avoidable`(3)).**  `av_subset`.  If `|Q| + ν(N) = k + r_N(E_Q)`, then
`Av(N) ⊆ Q`.

*Proof.*  Step 1, let `b ∈ Av(N) \ Q`, missed by a rainbow independent `J` with `|J| = ν`.
Step 2, `b ∈ M_J \ Q`, so `|Q ∪ M_J| ≥ |Q| + 1`.  Step 3, Lemma 19 gives
`ν + |Q| + 1 ≤ k + r_N(E_Q) = |Q| + ν`, a contradiction.

**Lemma 22 (the count of Step 2).**  `card_avOf_add`.  For a rainbow `I`,
`|A'| + |I| = k + |I ∩ R|`.

*Proof.*  `M_I` and `blk(I ∩ R)` are disjoint, `|M_I| = k - |blk(I)| = k - |I|` and
`|blk(I ∩ R)| = |I ∩ R|`, as `blk` is injective on `I`.

**Lemma 23 (Step 4).**  `rk_blockSet_avOf_le`.  If `I` is rainbow independent and no sink is
reachable from a source, then `r_N(E_{A'}) ≤ |I ∩ R|`.

*Proof.*  Step 1, `E_{A'} ∩ N.E ⊆ cl(I ∩ R)`.  Let `y ∈ E_{A'} ∩ N.E`; then `y` is a source,
or `blk(y) = blk(x)` for some `x ∈ I ∩ R`.  If `y ∈ I`, it is not a source, so `y = x` (`I` is
rainbow) and `y ∈ I ∩ R`.  If `y ∉ I`, then `y ∈ R`, as a source or as the head of the arc
`x → y`; so `y` is not a sink, and `y ∈ cl(I)`, since otherwise `I + y` would be independent.
Every `x' ≠ y` on the fundamental circuit `C` of `y` in `I + y` lies in `I`, and `I - x' + y`
is independent, so `y → x'` is an arc and `x' ∈ R`.  Hence `y ∈ cl(C \ {y}) ⊆ cl(I ∩ R)`.
Step 2, `r_N(E_{A'}) = r_N(E_{A'} ∩ N.E) ≤ r_N(cl(I ∩ R)) = r_N(I ∩ R) = |I ∩ R|`, as `I ∩ R`
is independent.

**Theorem 24 (maximality).**  `card_eq_nu`.  If `I` is rainbow independent and no sink is
reachable from a source, then `|I| = ν(N)`.  `card_eq_nu_iff`: a rainbow independent `I` has
`|I| = ν(N)` if and only if no sink is reachable from a source.

*Proof.*  Step 1, Theorem 20 for `Q = A'`, Lemma 23 and Lemma 22 give
`|A'| + ν ≤ k + r_N(E_{A'}) ≤ k + |I ∩ R| = |A'| + |I|`, so `ν ≤ |I|`; and `|I| ≤ ν`.  Step 2,
for the equivalence: a reachable sink gives a rainbow independent set of size `|I| + 1`
(Proposition 18), so `|I| < ν`.

**Lemma 25 (Step 6).**  `card_avOf_add_nu`.  If `I` is rainbow independent with `|I| = ν(N)`,
then `|A'| + ν(N) = k + r_N(E_{A'})`.

*Proof.*  No sink is reachable (Theorem 24); Theorem 20 for `Q = A'`, Lemma 23 and Lemma 22.

**Proposition 26 (Step 3).**  `exists_exchange`.  If `I` is rainbow independent with
`|I| = ν(N)` and `x ∈ I ∩ R`, then some rainbow independent `J` with `|J| = ν(N)` misses
`blk(x)`.

*Proof.*  Take a shortest path from a source to `x` (Proposition 9(1)) and apply
Proposition 14.

**Theorem 27 (avoidable blocks from a largest set; Steps 3 to 6).**  `av_eq`.  If `I` is
rainbow independent with `|I| = ν(N)`, then `Av(N) = M_I ∪ blk(I ∩ R)`: the avoidable blocks
are the blocks missed by `I` and the blocks of the elements of `I` reachable from a source.

*Proof.*  Step 1, `Av(N) ⊆ A'` by Theorem 21, since `A'` attains equality (Lemma 25).  Step 2,
`M_I ⊆ Av(N)`, taking `J = I`, and `blk(x) ∈ Av(N)` for `x ∈ I ∩ R` by Proposition 26.

**Theorem 28 (Lemma `lem:avoidable`(2)).**  `card_av_add_nu`.
`|Av(N)| + ν(N) = k + r_N(E_{Av(N)})`, that is `|Av(N)| - r_N(E_{Av(N)}) = k - ν(N)`.

*Proof.*  Take a rainbow independent `I` with `|I| = ν`.  Then `Av(N) = A'` (Theorem 27), and
`A'` attains equality (Lemma 25).

### 1.9 `k` rounds of augmentation (Step 4 of the proof of `lem:observer`)

**Lemma 29.**  `nu_le`.  `ν(N) ≤ k`.

*Proof.*  A rainbow set `J` with `|J| = ν` maps injectively into `[k]` by `blk`.

**Theorem 30 (`k` rounds of augmentation).**  `iterate_step`.  Let `step` send every rainbow
independent `J` to a rainbow independent set with at least `|J|` elements, and with `|J| + 1`
elements when a sink of the exchange graph of `J` is reachable from a source.  Then
`step^k(∅)`, the result of `k` rounds from `∅`, is rainbow independent of size `ν(N)`.
`iterate_augStep`: in particular `augStep^k(∅)` is rainbow independent of size `ν(N)`
(Proposition 18).

*Proof.*  Step 1, by induction on `j`, `step^j(∅)` is rainbow independent with at least
`min(j, ν)` elements: if a sink is reachable from a source, the round adds one element;
otherwise the set already has `ν` elements (Theorem 24), and the round does not decrease its
size.  Step 2, for `j = k`, `min(k, ν) = ν` by Lemma 29, and a rainbow independent set has at
most `ν` elements.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:avoidable`(1) | `card_add_nu_le` | `Rainbow/Exchange.lean` | proved |
| `lem:avoidable`(2) | `card_av_add_nu` | same | proved |
| `lem:avoidable`(3) | `av_subset` | same | proved |
| proof of `lem:avoidable`, Steps 1 and 5 | `card_add_card_le` | same | proved |
| Step 2, the exchange graph | `Arc`, `IsSource`, `IsSink`, `layer`, `distance`, `reachSet`, `avOf`; `card_avOf_add` | same | definitions; proved |
| Step 2, "by maximality of `I` no path joins a source to a sink" | `card_eq_nu_iff` | same | proved |
| Step 3 | `IsShortestPath.exchange`, `exists_exchange` | same | proved |
| Step 3, "the exchange lemma for shortest paths" (Schrijver, Corollary 39.13a) | `indep_exchange`, `IsShortestPath.indep_symmDiff_of_mem` | same | proved |
| Step 4 | `rk_blockSet_avOf_le` | same | proved |
| Step 6 | `card_avOf_add_nu`, `av_eq` | same | proved |
| augmentation along a shortest path (Lawler; Schrijver, Theorem 41.2) | `IsShortestPath.augment`, `augment`, `augment_of_pred`, `exists_augment` | same | proved |
| shortest paths and breadth-first layers | `isShortestPath_of_pred`, `isShortestPath_of_rule`, `exists_isShortestPath`, `isShortestPath_iff`, `reachSet_eq_layer` | same | proved |
| maximality: no reachable sink implies `|I| = ν` | `card_eq_nu`, `card_eq_nu_iff` | same | proved |
| `lem:observer`, Step 4: "`k` rounds of the augmenting path algorithm", "the least-index shortest path", "one more exchange graph and its reachable set give `Av(N_G)`" | `augStep`, `augStep_spec`, `iterate_step`, `iterate_augStep`, `nu_le`, `leastPred`, `backPath`, `reachSet_eq_layer`, `av_eq` | same | proved (the mathematical content; the Boolean circuit and its size belong to the observer module) |


## 3. Differences from the paper

1. Items 1 and 2 are stated without subtraction, as `|Q| + ν ≤ k + r_N(E_Q)` and
   `|Av(N)| + ν = k + r_N(E_{Av(N)})`; over the integers these are the paper's inequalities.
   No change to the paper.
2. The Lean statements hold for every matroid `N` whose ground set lies in `E`, with
   `r_N(S) = r_N(S ∩ N.E)`, and for every map `blk`, empty blocks allowed.  The paper's lemma,
   for a matroid on `E`, is a special case.  No change to the paper.
3. Step 3 is proved for every rainbow independent `I` (the exchanged set has size `|I|`), and
   the count of Step 2 as `|A'| + |I| = k + |I ∩ R|` for every rainbow `I`; the paper uses
   both for `|I| = ν`.  No change to the paper.
4. Step 4 of the paper shows `E_{A'} ⊆ cl_N(I ∩ R)`; Lean shows
   `E_{A'} ∩ N.E ⊆ cl_N(I ∩ R)`, the same set when `N` is a matroid on `E`.  No change.
5. Precise references (optional).  The exchange lemma used in Step 3 is the lemma for paths
   without shortcuts, Schrijver's Corollary 39.13a, and the augmentation behind Step 2 is
   Schrijver's Theorem 41.2.  Proposed wording, Step 2: "By maximality of `I` no path joins a
   source to a sink~\cite{lawler75}, \cite[Theorem~41.2]{schrijver03}."  Step 3: "it is
   independent by the exchange lemma for paths without
   shortcuts~\cite[Corollary~39.13a]{schrijver03}."
6. `lem:observer`, Step 4, "the choice of the least-index shortest path".  The formal round
   `augStep` takes the least layer containing a sink, the sink of least index in it, and then
   predecessors of least index; `augment_of_pred` shows that any rule of predecessors in the
   previous layer works, and `iterate_step` that `k` rounds suffice for any round with the
   specification of Proposition 18.  Proposed wording (optional): "a breadth-first search, the
   choice of a shortest path (the sink of least index in the first layer that contains a sink,
   then predecessors of least index) and the exchange cost `O(m^3)` gates."


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Exchange.lean` | 937 |


## 5. Not done

* The Boolean circuit that implements the augmenting path algorithm, and its size
  `O(km^3(s+m))` in Lemma `lem:observer`, belong to the observer module; this module supplies
  the mathematical specification (`augStep`, `iterate_step`, `reachSet_eq_layer`, `av_eq`,
  `card_eq_nu_iff`).
* The number of independence tests per round is a property of the circuit and is not stated
  here.
* Every item of the assignment (Lemma `lem:avoidable` items 1 to 3, the exchange graph with its
  layers and distance, augmentation along a shortest path in general and in the backward form,
  maximality, and the avoidable blocks of a largest set with the exchange of Step 3) is
  proved.
