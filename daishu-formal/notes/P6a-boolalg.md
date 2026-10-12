# P6a: Boolean algorithm library

Natural-language companion of
`SignedTropical/BoolAlg/{Impl,Bits,Arith,Count,Rel,Path,ExchangeBits}.lean`, namespace
`SignedTropical.BoolAlg`.  Sources: `daishu/paper/greedy_intersection.tex`, Lemma
`lem:observer` (Steps 1 to 4) and the proof of Theorem `thm:D` (Steps 2 and 4); the builders of
Phase 1 (`Circuit.lean`: `Bld`, `emit`, `Den`, `DenL`; `Inline.lean`: `inline`, `inline_spec`);
the Boolean arithmetic of `Converse.lean` (`xorB`, `rcaB`, `notsB`, `selB`, `fit`) and
`Binary.lean` (`orB`, `leadV`, `leadV_eq`); Warshall, *A theorem on Boolean matrices* (1962); the
exchange graph and the round `augStep` of `Rainbow/Exchange.lean` (P2).

Build status: each of the seven modules builds with `lake build SignedTropical.BoolAlg.<Module>`
with no error and no warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
`extern`, `unsafe` or `opaque`.  All 174 theorems of the seven modules (main and auxiliary)
were checked with `#print axioms`: they depend only on `propext`, `Classical.choice` and
`Quot.sound` (seven on none).  Dependencies: `Impl` imports `Inline`;
`Bits` imports `Impl` and `Binary`; `Arith` imports `Bits` and `Counting`; `Count` imports
`Arith`; `Rel` imports `Bits`; `Path` imports `Rel`; `ExchangeBits` imports `Path` and
`Rainbow/Exchange`.

Conventions.  A circuit on `n` inputs is a list of gates (Phase 1); an input is
`x : Fin n → Bool`.  Gates are `∧`, `∨`, `¬` (`BoolOp`); the constant source `false` is an
operand and costs no gate, the constant `true` costs one gate `¬false`.  A number is carried
least significant bit first and read by `bitsVal`.  `⌈log₂(k+1)⌉`, the number of binary digits
of `k`, is `Nat.size k`.  Every gate count below is exact.


## 1. Results

### 1.1 Representations and implementations (`Impl.lean`)

**Definition 1.**  A *representation* `R : Rep Op α n σ τ` is a predicate `R.rep gs s T`, read
"in the gate list `gs`, the object `s` (made of operands) carries the value `T x : τ` at every
input `x`", that persists when gates are appended (`R.mono`).  Instances: one operand
(`Rep.arg I`, which is `Den I`), `L` operands (`Rep.list I L`, which is `DenL I` with length
`L`), pairs (`Rep.prod`, componentwise) and families (`Rep.pi ι`, entrywise).

**Definition 2.**  `Impl R₁ R₂ b c F` (the builder `b` implements `F : τ₁ → τ₂` from `R₁` to
`R₂` with `c` gates): for every gate list `gs`, object `s` and values `T` with `R₁.rep gs s T`,
the gate list `(b s gs).1` extends `gs` by exactly `c` gates and `(b s gs).2` carries
`x ↦ F (T x)` in it.

**Proposition 3 (composition).**  Let `b₁`, `b₂` implement `F₁`, `F₂` with `c₁`, `c₂` gates.

1. `Impl.comp`: `seqB b₁ b₂` (run `b₁`, then `b₂` on its result) implements `F₂ ∘ F₁` with
   `c₁ + c₂` gates.  `Impl.pair`: `pairB b₁ b₂` (both on the same object) implements
   `t ↦ (F₁ t, F₂ t)` with `c₁ + c₂` gates.  `Impl.extend`: keep the object and add `F t`.
2. `Impl.free`, `Impl.self`, `Impl.fst`, `Impl.snd`: rearranging operands costs no gate.
   `Impl.pre`, `Impl.post`: rearranging before or after a builder.  `Impl.cost`, `Impl.congr`:
   rewriting the count or the function.
3. `Impl.tab`: if `b i` implements `F i` with `c` gates for every `i < r`, then
   `tabB (b · s)` implements `t ↦ (F i t)ᵢ` with `r c` gates; `Impl.tabSum`: with `c i` gates,
   `∑ i, c i` gates.  `Impl.map`, `Impl.map₂`: one gadget at every index.
4. `Impl.iterate`: `k` rounds of a gadget from `R` to `R` implement `F^[k]` with `k c` gates.
   `Impl.fold`: one round per element of a list `l` (implemented for the elements of `l`),
   `|l| c` gates, the left fold.  `Impl.scan`: `k` rounds keeping every intermediate object,
   entry `i` carrying `F^[i]`.
5. Rounds with a fixed context: if `b` reads a pair (context, state) and implements
   `t ↦ F t.1 t.2` with `c` gates, then `iterCtxB b k` implements `t ↦ (F t.1)^[k] t.2`
   (`Impl.iterateCtx`), `scanCtxB b k` implements `t ↦ ((F t.1)^[i] t.2)ᵢ` with `i ≤ k`
   (`Impl.scanCtx`), both with `k c` gates, and `foldCtxB b l` implements the left fold over
   `l` of `F e t.1` with `|l| c` gates (`Impl.foldCtx`, rounds implemented for the elements
   of `l`).

*Proof.*  Step 1, `comp`: run `b₁`, then `b₂` on the result; the prefixes compose and the counts
add.  Step 2, `pair`: after `b₁` the original object still carries its value (`Rep.mono`), so
`b₂` applies to it.  Step 3, `tabB_sum_spec`, by induction on `r`: run `b 0`, then the
remaining builders on the extended list; the first result persists (`Rep.mono`) and the counts
add (`Fin.sum_univ_succ`); `tabB_spec` is the case of a constant count.  Step 4, `iterate`,
`fold` and `scan` by induction on `k` or on the list, with `comp`.  Step 5, the context versions
iterate the round `t ↦ (t.1, b t)` (`Impl.fst.pair h`) and keep the state (`post`); the values
follow from `iterate_ctx`: `(t ↦ (t.1, F t.1 t.2))^[k] (a, s) = (a, (F a)^[k] s)`, and from its
list form `foldl_ctx`, both by induction.

**Theorem 4 (running a circuit inside a circuit; `lem:observer`, Steps 1 and 3, "evaluate the
rank circuit on ...").**  `runB_impl`.  For a circuit `C` on `k` inputs over any gate set and any
reading `I`, `runB C v` appends the gates of `C`, input `i` of `C` reading the operand `v i`, and
returns operands for the outputs of `C`.  It implements `C.eval I` from `k` operands to
`C.outs.length` operands with exactly `C.size` gates.

*Proof.*  Step 1, `inline_spec` of `Inline.lean` with the gadget `emit o` for every gate `o`
(correct by `den_emit`) shows that the returned operands carry the outputs of `C` evaluated at
the carried values.  Step 2, `length_inline` with one gate per gate of `C` gives `C.size`.

**Theorem 5 (back to circuits).**  `circuitOf_spec`: if `b` implements `F` from the `n` input
operands to `L` operands with `c` gates, then `circuitOf b` has size `c`, `L` outputs, and
outputs `F x` at every input `x`.  `vecCircuit_spec` (`Bits.lean`): the same for `L` bits
(`vecR L`), outputs `List.ofFn (F x)`; `circuitOf_num` (`Count.lean`): the same for a number on
`w` bits, `bitsVal` of the outputs is `F x`.  `seqCircuit_spec`: `C₂` run on the outputs of `C₁`
has size `C₁.size + C₂.size` and outputs `C₂` at the outputs of `C₁`.  `ofFn_impl`, `getD_impl`:
lists and families of operands convert freely.

*Proof.*  Step 1, apply the implementation to the empty gate list and the input operands
(`den_input`, `input_rep`).  Step 2, `DenL.eval` reads the outputs.  `seqCircuit` is two `runB`
composed with a free rearrangement.

### 1.2 Bits (`Bits.lean`)

Representations: one bit (`bitR`), `r` bits (`vecR r`, a subset of `Fin r`), a relation on
`Fin r` (`relR r`, `r²` bits), an `r × s` matrix (`matR r s`), a list of `L` bits (`bitsR L`).

**Proposition 6 (gates and bitwise gadgets).**  One gate `o` (`emit_impl`, `emitAnd_impl`,
`emitOr_impl`, `emitNot_impl`); exclusive or, 4 gates (`xorB_impl`); `true`, 1 gate
(`true_impl`); `false`, no gate (`false_impl`).  On vectors of `r` bits: `¬`, `∧`, `∨` entrywise,
`r` gates each (`vecNotB_impl`, `vecAndB_impl`, `vecOrB_impl`); `⊕`, `4r` (`vecXorB_impl`); a bit
and every entry, `r` (`vecMaskB_impl`); selection `if s then u else v`, `3r + 1`
(`vecMuxB_impl`); `∃ i, V i`, `r` gates (`vecAnyB_impl`); `∀ i, V i`, `r + 1` (`vecAllB_impl`);
`acc ∨ ∃ i, P i ∧ Q i`, `2r` (`dotAccB_spec`).

*Proof.*  Step 1, each gate by `den_emit`.  Step 2, entrywise gadgets by `Impl.map`, `Impl.map₂`
and `Impl.tab`.  Step 3, the reductions by induction on `r` with an accumulator (`anyAccB_spec`,
`allAccB_spec`, `dotAccB_spec`), one or two gates per entry.  Step 4, selection: one shared
negation `¬s`, then `(s ∧ uᵢ) ∨ (¬s ∧ vᵢ)` per entry.

**Theorem 7 (least-index selection; `lem:observer`, Step 2 "its element of least index" and
Step 4 "the sink of least index ..., then predecessors of least index").**  `vecFirstB_impl`:
`vecFirstB` implements `leadV` with `3r` gates, where `leadV V j = V j ∧ ¬∃ i < j, V i`, the
one-hot vector of the least set entry.  Facts: `leadV_eq_true_iff`; `leadV_unique` (at most one
entry is set); `exists_leadV_iff` (some entry of `leadV V` is set iff some entry of `V` is);
`leadV_eq_min'` (if `V` has a set entry, `leadV V j` holds iff `j` is the `min'` of the set
entries); `leadV_eq_find` (for a decidable predicate `P` on `ℕ` with some `P d` and
`Nat.find < r`, `leadV` of `d ↦ [P d]` over `d < r` marks `Nat.find`); `leadV_of_forall_false`.

*Proof.*  Step 1, `firstAccB_spec`, by induction on `r` with an accumulator `acc` ("an earlier
entry is set"): per entry `¬acc`, `vⱼ ∧ ¬acc` and `acc ∨ vⱼ`, three gates.  Step 2, with `acc`
the constant `false` the value is `leadV`.  Step 3, `leadV_eq_min'` and `leadV_eq_find` are
`leadV_eq` of `Binary.lean` with `q` the `min'` (`min'_mem`, `min'_le`), respectively
`Nat.find` (`Nat.find_spec`, `Nat.find_min`).

### 1.3 Binary numbers (`Arith.lean`)

**Definition 8.**  `numR w`: `w` operands carrying `N`: their bits `A x` (a list of length `w`)
satisfy `bitsVal (A x) = N x`.  `numR_lt`: `N x < 2^w`.

**Theorem 9 (arithmetic; `thm:D`, Steps 2 and 4; `lem:observer`, Steps 1, 3, 4).**  For widths
`w₁`, `w₂` put `W = max w₁ w₂` (the shorter argument is padded with `false`):

| gadget | value | width | gates |
| :-- | :-- | :-- | :-- |
| `numAddB` | `a + b` | `W + 1` | `11W` |
| `numSubB` | `a - b` in `ℕ` (`0` if `b > a`) | `w₁` | `12W + w₁ + 1` |
| `numLeB`, `numLtB` | `[a ≤ b]`, `[a < b]` | bit | `5W + 1`, `5W + 2` |
| `numEqB` | `[a = b]` | bit | `5W + 1` |
| `numMuxB` | `if s then a else b` | `W` | `3W + 1` |
| `numMaskB` | `if s then a else 0` | `w` | `w` |
| `numMinB` | `min a b` | `W` | `8W + 2` |
| `numConstB c w` | `c mod 2^w` | `w` | `1` |

With a constant `c` as second argument on `W = max w ⌈log₂(c+1)⌉` bits, one more gate:
`numLeConstB_impl` (`[a ≤ c]`, `5W + 2`), `numGeConstB_impl` (`[c ≤ a]`, `5W + 2`),
`numEqConstB_impl` (`[a = c]`, `5W + 2`), `numSubConstB_impl` (`a - c`, `12W + w + 2`),
`numMinConstB_impl` (`min a c`, `8W + 3`).  Free: reading bits as a number (`numOfBits_impl`,
`numOfBit_impl`), widening (`numWiden_impl`), truncation and fitting to `W` bits, the value
modulo `2^W` (`numTrunc_impl`, `numFit_impl`).

*Proof.*  Step 1, padding with `false` keeps the value (`bitsVal_append_false`).  Step 2,
addition: the ripple-carry adder `rcaB` of `Converse.lean` (full adders, 11 gates per bit);
`bitsVal_rcaV`: the sum bits and `2^W` times the carry make `a + b + c`, by induction on the bits.
Step 3, subtraction: `a + ¬b + 1` on `W` bits (`W` negations, one gate for `true`, `11W`);
`bitsVal(¬b) + b + 1 = 2^W` (`bitsVal_map_not`) gives carry `[b ≤ a]` and sum `a - b` in that
case (`rcaV_not_carry`); the low `w₁` sum bits, each in conjunction with the carry (`w₁` gates),
carry `a - b` if `b ≤ a` and `0` otherwise.  Step 4, `[a ≤ b]` is the carry of `b + ¬a + 1`,
computed by the carry chain alone (`carryB`, 4 gates per bit); `[a < b] = ¬[b ≤ a]`.  Step 5,
equality: no bit of `a ⊕ b` is set (`any_zipWith_xor`), and bit lists of one length with one
value are equal (`eq_of_bitsVal_eq`).  Step 6, selection by `selB` (3 gates per bit) and one
negation; minimum by comparison and selection.  Step 7, the constant `c` has bits
`c.testBit i`, wired to the constant `false` or to one gate `true`; on `⌈log₂(c+1)⌉` bits its
value is `c` (`const_mod_size`).

### 1.4 Population counts, sums, rank queries and independence tests (`Count.lean`)

**Theorem 10 (population count; `thm:D`, Step 2 "a population count"; `lem:observer`, Step 4
"comparing `|I|` with `r₀`").**  `vecPopcountB_impl`, `popcountB_spec`: the number of set
entries of `r` bits, on `⌈log₂(r+1)⌉` bits, with `popCost r = 11(2r - 1 - ⌈log₂(r+1)⌉)` gates
(`0` for `r ≤ 1`); `popCost_le`: `popCost r ≤ 22r`.

*Proof.*  Strong induction on the number `L` of bits.  Step 1, `L ≤ 1`: no gate.  Step 2, split
after `k = ⌊L/2⌋` bits, count both halves, add on `W = ⌈log₂(L-k+1)⌉` bits (`11W` gates), and
keep the low `⌈log₂(L+1)⌉` bits (free); the count is at most `L < 2^⌈log₂(L+1)⌉`, so the value is
unchanged.  Step 3, the counts: `⌈log₂(⌊L/2⌋+1)⌉ + 1 = ⌈log₂(L+1)⌉` (`size_div_two_add_one`), so
`popCost k + popCost (L-k) + 11W = popCost L`.

**Theorem 11 (sums).**  `numSumB_impl`: the sum of `r` numbers of width `w`, on
`w + ⌈log₂(r+1)⌉` bits, with `11r(w + ⌈log₂(r+1)⌉)` gates.

*Proof.*  Step 1, add the numbers to an accumulator, truncating to `W = w + ⌈log₂(r+1)⌉` bits
after each addition (`numSumAccB_spec`): the value is the sum modulo `2^W`.  Step 2, the sum is
at most `r(2^w - 1) < 2^W`.

**Theorem 12 (rank queries; `lem:observer`, Steps 1 and 3; `thm:D`, Step 2 "on top of the two
rank circuits").**  Let `C` be a Boolean circuit on `k` inputs.  `runB_num`: run on a carried
vector `V` it costs `C.size` gates and carries `bitsVal (C.eval V)` on `C.outs.length` bits.
`runB_set`: if `bitsVal (C.eval (indicator S)) = f S` for every `S`, the carried number is
`f {i : V i}`.  `runB_set_fit`: if moreover `f S < 2^w` for every `S`, then with the outputs
fitted to `w` bits (free) the carried number is `f {i : V i}` on exactly `w` bits.

*Proof.*  Step 1, `runB_impl`.  Step 2, the indicator vector of `{i : V i}` is `V`
(`indicator_filter`).  Step 3, `numFit_impl`, and `f S mod 2^w = f S`.

**Theorem 12a (independence tests; `lem:observer`, Step 4 "independence tests, one rank query
each").**  Let `C` be a Boolean circuit on `k` inputs and `T = {i : V i}` for a carried vector
`V` of `k` bits.

1. `eqCardB_impl`: if `bitsVal (C.eval (indicator S)) = f S < 2^w` for every `S`, then
   `eqCardB C w` computes `[f(T) = |T|]` with `C.size + popCost k + 5 max(w, ⌈log₂(k+1)⌉) + 1`
   gates.
2. `indepB_impl`: if `C` is a rank circuit of a matroid `N` on `Fin k`, that is
   `(bitsVal (C.eval (indicator S)) : ℕ∞) = N.eRk S` for every `S` (the hypothesis of the rank
   circuits of Phase 1), then `eqCardB C ⌈log₂(k+1)⌉` computes `[T is independent in N]` with
   `C.size + popCost k + 5⌈log₂(k+1)⌉ + 1` gates.

*Proof.*  Step 1, item 1: `runB_set_fit` (the number `f(T)` on `w` bits) and
`vecPopcountB_impl` (`|T|` on `⌈log₂(k+1)⌉` bits) on the same vector (`Impl.pair`), then
`numEqB_impl` (`Impl.comp`); the counts add.  Step 2, item 2: the hypothesis gives
`bitsVal (C.eval (indicator S)) = rk N S` (`coe_rk`, injectivity of `ℕ → ℕ∞`), and
`rk N S ≤ |S| ≤ k < 2^⌈log₂(k+1)⌉` (`eRk_le_encard`, `Nat.lt_size_self`), so item 1 applies
with `w = ⌈log₂(k+1)⌉`.  Step 3, a finite set is independent if and only if its rank equals its
size (`Matroid.indep_iff_eRk_eq_encard_of_finite`), that is `rk N T = |T|`.

### 1.5 Relations (`Rel.lean`)

**Theorem 13 (image of a set).**  `relImageAccB_impl`: for an `r × s` matrix `G`, `U ⊆ Fin r` and
`A ⊆ Fin s`, the set `v ↦ A v ∨ ∃ u, U u ∧ G u v` with `2rs` gates; `relImageB_impl`: the image
`v ↦ ∃ u, U u ∧ G u v` with `2rs` gates (for a one-hot `U` marking `u`, row `u` of `G`).
`transpose_impl`: transposition is free.

*Proof.*  For every `v`, `dotAccB` over `u` with column `v` of `G` and accumulator `A v` (`2r`
gates); `Impl.tab` over the `s` columns.

**Definition 14.**  `bfsStep G L v = L v ∨ ∃ u, L u ∧ G u v`; the layers
`layerV G S d = (bfsStep G)^[d] S`, so `layerV G S 0 = S` and
`layerV G S (d+1) = bfsStep G (layerV G S d)` (`layerV_succ`).

**Theorem 15 (breadth-first layers; `lem:observer`, Step 4 "a breadth-first search").**

1. `layersB_impl`: from `(G, S)`, a relation on `Fin r` and a subset, `layersB d` computes the
   layers `0, …, d` with `2dr²` gates, entry `i` carrying `layerV G S i`.
2. `layerV_eq_true_iff`: `v` lies in layer `d` if and only if some path
   `p 0 → p 1 → ⋯ → p l` of `l ≤ d` arcs of `G` leads from `p 0 ∈ S` to `p l = v`.
3. `layerV_le`: the layers increase.  `layerV_le_card`: every layer is contained in layer `r`.
4. `layerV_card_eq_true_iff`: `v` lies in layer `r` if and only if `v` is reachable from `S`
   (`Relation.ReflTransGen` of `G`).

*Proof.*  Step 1, one step `bfsStepB = relImageAccB (G, L, L)`, `2r²` gates; `layersB` is
`scanCtxB` with the context `G` (Proposition 3(5)).  Step 2, item 2 by induction on `d`: a path
of at most `d + 1` arcs has at most `d` arcs, or exactly `d + 1`, and then its first `d` arcs
reach the in-neighbour `p d` of `v` in layer `d`; conversely a path to `u` in layer `d` extends
by an arc `u → v`.  Step 3, monotonicity from item 2.  Step 4, some `j ≤ r` has
`layerV (j+1) = layerV j`: otherwise the sets of marked elements would strictly increase `r + 1`
times inside `Fin r` (`exists_layerV_succ_eq`).  Since each layer is `bfsStep` of the previous
one, the layers are constant from `j` on, and every layer is contained in layer `r`.  Step 5,
item 4: a path gives `ReflTransGen` by induction along it; conversely, by induction on
`ReflTransGen`, `v` lies in some layer, hence in layer `r`.

**Theorem 16 (Warshall's algorithm; `lem:observer`, Step 2 "Warshall's algorithm closes them
transitively with `2m³` gates").**  `warshallB_impl`: `warshallB` implements `warshallV` on
relations on `Fin r` with exactly `2r³` gates, and `warshallV_eq_true_iff`: `warshallV G i j`
holds if and only if `Relation.TransGen G i j`.  `rtcB_impl`, `rtcV_eq_true_iff`: with the
diagonal set, `2r³ + 1` gates, the reflexive transitive closure `Relation.ReflTransGen G`.

*Proof.*  Step 1, the round with pivot `k` replaces `R i j` by `R i j ∨ (R i k ∧ R k j)` for all
`r²` pairs, two gates each (`orAndB_impl`, `warshallStepB_impl`); one round per pivot
`0, …, r - 1` gives `2r³` gates (`Impl.fold`).  Step 2, invariant (`PathVia`,
`foldl_warshallStep_eq_true_iff`, induction on the list of pivots from the right): after the
rounds for the pivots in `l`, entry `(i, j)` is set if and only if a path `i → ⋯ → c → j` of at
least one arc exists whose inner vertices lie in `l`.  With no pivot, this is `G i j`.  Step 3,
the round (`pathVia_or_eq`): a path with inner vertices in `K ∪ {k}` exists if and only if one
with inner vertices in `K` exists, or one from `i` to `k` and one from `k` to `j`.  For the
forward direction, induction along the path from `i`: every vertex reached through `K ∪ {k}` is
reached through `K` from `i`, or (once the path has met `k`) through `K` from `k`; at the vertex
`k` itself the second case holds with the empty path.  The converse concatenates at `k`.
Step 4, after all pivots the inner vertices are unrestricted, and such paths are `TransGen`
(`Relation.TransGen.tail'_iff`).  Step 5, the diagonal: one gate `true`, wired to the entries
`(i, i)` (`reflB_impl`); `ReflTransGen G i j` if and only if `i = j` or `TransGen G i j`.

### 1.6 Least-index shortest paths (`Path.lean`)

Let `G` be a relation on `Fin r`, `S` a set of sources and `Y` a set of targets, with layers
`L_d = layerV G S d`.

**Definition 17.**  `hitV G S Y d = L_d ∩ Y`; `Hits G S Y`: some layer meets `Y`;
`predV G S i y`: the in-neighbour of least index of `y` in `L_i`, and `y` if there is none;
`backV G S d y`: `backV d y d = y` and `backV d y i = predV i (backV d y (i + 1))` for `i < d`
(`backV_self`, `backV_pred`); `firstY`: the least element of `Y` in the first layer `D` meeting
`Y`; `pathSet G S Y = {backV D (firstY) i : i ≤ D}` if `Hits G S Y`, and `∅` otherwise.

**Definition 18 (the values of the circuit).**  `targetV G S Y d` is `leadV` over `e ≤ r` of
`[L_e meets Y]`, at `d`, in conjunction with `leadV (L_d ∩ Y)`; `predHotV G S i y` is
`leadV (L_i ∩ G(·, y))`; `downStep P T i (cur, acc) = (c, acc ∪ c)` with
`c = T_i ∪ P_i(cur)` for `i < r`; `downV P T` runs the rounds `i = r - 1, …, 0` from
`(T_r, T_r)` and returns `acc`; `pathV G S Y = downV (predHotV G S) (targetV G S Y)`.

**Theorem 19 (`lem:observer`, Step 4, "the choice of a shortest path (the sink of least index
in the first layer that contains a sink, then predecessors of least index)").**
`pathV_eq_true_iff`: `pathV G S Y u = true` if and only if `u ∈ pathSet G S Y`.  On the way:
`predV_spec` (if `y ∈ L_{i+1} \ L_i`, then `predV i y ∈ L_i`, `predV i y → y`, and
`predHotV i y` is the one-hot vector of `predV i y`), `backV_layer` (from an element `y` of
distance exactly `d`, `backV d y i` has distance exactly `i`), `firstY_layer`, `find_le`
(`D ≤ r`), `targetV_eq` (`targetV d y` holds iff `d = D` and `y = firstY`),
`targetV_of_not_hits`.

*Proof.*  Step 1, `predV_spec`: the in-neighbours in `L_i` of `y ∈ L_{i+1} \ L_i` form a nonempty
set (`layerV_succ`); `predV i y` is its `min'`, which `leadV` marks (`leadV_eq_min'`).  Step 2,
`backV_layer`, by downward induction as `isShortestPath_of_rule` of P2: the predecessor of a
vertex of distance exactly `i + 1` lies in `L_i`, and in no `L_j` with `j < i`, since then its
successor would lie in `L_{j+1}`.  Step 3, `firstY` has distance exactly `D`: it lies in `L_D`,
and if it lay in `L_j` with `j < D`, then `L_j` would meet `Y` (`Nat.find_min`); and `D ≤ r`
since `L_D ⊆ L_r` (`layerV_le_card`).  Step 4, `targetV_eq` by `leadV_eq_find` and
`leadV_eq_min'`.  Step 5, the downward pass (`foldl_downStep`, `downV_eq`), by induction on
`k ≤ r`: the rounds `k - 1, …, 0` take `(C_k, A_k)` to `(C_0, A_0)` whenever each round takes
`(C_{i+1}, A_{i+1})` to `(C_i, A_i)`.  Step 6, if `Hits G S Y`, take `C_i = {backV D y₀ i}` for
`i ≤ D` and `∅` for `i > D`, and `A_i = {backV D y₀ j : i ≤ j ≤ D}`, with `y₀ = firstY`.  The
round for `i` yields `T_i ∪ Pred_i(C_{i+1})`: `{y₀}` for `i = D`; the one-hot vector of
`predV i (backV D y₀ (i + 1)) = backV D y₀ i` for `i < D` (Steps 1 and 2); `∅` for `i > D`.
Moreover `(T_r, T_r) = (C_r, A_r)` since `D ≤ r`.  So `pathV = A_0 = pathSet`.  Step 7,
otherwise every `T_i` is empty (`targetV_of_not_hits`) and every state is `(∅, ∅)`.

**Theorem 20 (the circuit).**  `pathB_impl`: `pathB` computes `pathV G S Y` from `(G, S, Y)`
with `pathCost r = 8r³ + 7r² + 9r + 3` gates.  `exchangeB_impl`: `exchangeB` computes
`I ⊕ pathV G S Y`, the indicator vector of `I ∆ pathSet G S Y`, from `(I, (G, S, Y))` with
`pathCost r + 4r` gates.

*Proof.*  Step 1, the context (`pathCtxB_impl`, `6r³ + 6r(r+1) + 3(r+1)` gates): the layers
`L_0, …, L_r` (`layersB_impl r`, `2r³`); the predecessor one-hots `leadV (L_i ∩ G(·, y))` for
`i < r` and every `y` (`predsB_impl`, `r + 3r` gates each, `4r³`); the target one-hots
(`targetsB_impl`): `L_d ∩ Y` (`r` gates per layer), whether it is nonempty (`r`), the first such
layer (`3(r+1)`), the least element of each (`3r`), and the mask (`r`).  Step 2, the downward
pass (`downB_impl`, `r(2r² + r)` gates): from `(T_r, T_r)` (free), one round per layer
`i = r - 1, …, 0` (`downRoundB_impl`: `relImageAccB`, `2r²` gates, and `vecOrB`, `r`), by
`Impl.foldCtx`; `foldl_finRange_reverse` converts the list of `Fin r` in decreasing order to
`List.range`.  Step 3, the counts add to `pathCost r`.  Step 4, `exchangeB` adds `vecXorB`,
`4r` gates.

### 1.7 Bits of the exchange graph (`ExchangeBits.lean`)

Let `S`, `G`, `K` be bits with `S y ↔ IsSource blk I y`, `G u v ↔ Arc N blk I u v` and
`K y ↔ IsSink N I y` (Definition 3 of `notes/P2-exchange.md`), for a matroid `N` on `Fin m`.

**Theorem 21 (Step 4 of `lem:observer`, one round of the augmenting path algorithm).**

1. `layerV_iff_mem_layer`: `layerV G S d v ↔ v ∈ layer N blk I d`;
   `layerV_iff_mem_reachSet`: `layerV G S m v ↔ v ∈ reachSet N blk I`.
2. `find_sink_layer_le`: if some layer contains a sink, the least such layer is at most `m`.
3. `leadV_sink_eq`: least-index selection among `layerV G S d y ∧ K y` marks the `min'` of the
   sinks in `layer N blk I d`, the sink chosen by `augStep` (the statement is written with the
   same terms as `augStep`).
4. `leadV_pred_eq`: if `y ∈ layer (i+1)` and `y ∉ layer i`, least-index selection among
   `layerV G S i u ∧ G u y` marks `leastPred N blk I i y`.  `leastPred_le`: `leastPred i y` is at
   most every in-neighbour of `y` in `layer i`.
5. `predV_eq_leastPred`, `backV_eq_backPath`: `predV G S = leastPred N blk I` and
   `backV G S = backPath N blk I`.
6. `augStep_eq_symmDiff`: `augStep N blk I = I ∆ pathSet G S K`.  `augStep_bits`: `u ∈ augStep`
   if and only if `[u ∈ I] ⊕ pathV G S K u`; so `exchangeB` run on `(1_I, (G, S, K))` outputs the
   indicator vector of `augStep N blk I` with `pathCost m + 4m` gates.

*Proof.*  Step 1, item 1 by induction on `d`: both layer 0's are the sources, and both
recursions add the out-neighbours (`mem_layer_succ`); `reachSet_eq_layer`.  Step 2, item 2: a
sink in layer `d` lies in layer `m` (`layer_subset_layer_card`), so `Nat.find_min'`.  Step 3,
items 3 and 4 by `leadV_eq` with `q` the `min'` of the sinks, respectively `leastPred i y`: the
bit at `q` is set (`min'_mem`, `leastPred_spec`), and a set bit at `j < q` would give a smaller
sink, respectively a smaller in-neighbour (`min'_le`, `leastPred_le`).  Step 4, item 5: the
finsets of which `predV` and `leastPred` take the `min'` are equal by item 1, and `backV`,
`backPath` have the same recursion.  Step 5, item 6: a layer meets `K` exactly when it contains
a sink (item 1), so `Hits G S K` holds exactly when `augStep` exchanges, the two first layers
agree (`Nat.find_mono` both ways), the two least elements agree (equal finsets), and the two
paths agree by item 5; without a reachable sink both sides are `I` (`I ∆ ∅ = I`).  The bit form
follows with `pathV_eq_true_iff` and `Finset.mem_symmDiff`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer` Step 1: rank circuit on computed sets, with and without `f`, compare | `runB_impl`, `runB_set`, `runB_set_fit`, `numEqB_impl`, `numLtB_impl` | `Impl`, `Count`, `Arith` | proved |
| `lem:observer` Step 2: Warshall's algorithm, `2m³` gates | `warshallB_impl`, `warshallV_eq_true_iff`, `rtcB_impl`, `rtcV_eq_true_iff` | `Rel` | proved |
| `lem:observer` Step 2: representative of least index | `vecFirstB_impl`, `leadV_eq_min'` | `Bits` | proved |
| `lem:observer` Step 3: rank queries, differences and their sum | `runB_set_fit`, `numSubB_impl`, `numMaskB_impl`, `numSumB_impl` | `Count`, `Arith` | proved |
| `lem:observer` Step 4: `k` rounds | `Impl.iterate`, `Impl.iterateCtx` | `Impl` | proved |
| `lem:observer` Step 4: independence tests, one rank query each | `indepB_impl`, `eqCardB_impl` | `Count` | proved |
| `lem:observer` Step 4: breadth-first search | `layersB_impl`, `layerV_eq_true_iff`, `layerV_card_eq_true_iff`, `layerV_iff_mem_layer`, `layerV_iff_mem_reachSet` | `Rel`, `ExchangeBits` | proved |
| `lem:observer` Step 4: least-index shortest path | `pathB_impl`, `pathV_eq_true_iff`, `predV_spec`, `backV_layer`, `targetV_eq`; `vecFirstB_impl`, `leadV_eq_find`, `leadV_sink_eq`, `leadV_pred_eq`, `find_sink_layer_le` | `Path`, `Bits`, `ExchangeBits` | proved |
| `lem:observer` Step 4: the exchange, one round of the algorithm | `exchangeB_impl`, `augStep_eq_symmDiff`, `augStep_bits`, `predV_eq_leastPred`, `backV_eq_backPath` | `Path`, `ExchangeBits` | proved |
| `lem:observer` Step 4: guard `|I| ≤ r₀` | `vecPopcountB_impl`, `numLeConstB_impl` | `Count`, `Arith` | proved |
| `thm:D` Step 2: population count and two additions on top of two rank circuits | `vecPopcountB_impl`, `popCost_le`, `numAddB_impl`, `numSubConstB_impl`, `vecNotB_impl`, `runB_set_fit` | `Count`, `Arith`, `Bits` | proved |
| `thm:D` Step 4: comparison and selection on `O(log m)` bits | `numMinConstB_impl`, `numLeB_impl`, `numMuxB_impl` | `Arith` | proved |
| a builder from the inputs is a circuit | `circuitOf_spec`, `vecCircuit_spec`, `circuitOf_num`, `seqCircuit_spec` | `Impl`, `Bits`, `Count` | proved |


## 3. Differences from the paper

1. The counts are exact and match the paper where it states them: Warshall's algorithm on `r`
   points costs exactly `2r³` gates (`warshallB_impl`), the breadth-first layers `0, …, m` cost
   `2m³` gates (`layersB_impl`, `O(m³)` in Step 4), least-index selection `3r` gates, and a
   population count at most `22r` gates (`O(m)` in `thm:D`, Step 2).  No change to the paper.
2. Widths of rank outputs.  A circuit that "outputs the binary digits of the rank" may have more
   output bits than `⌈log₂(m+1)⌉`; the extra ones are identically `0`.  The costs
   `O(log m)` per comparison or addition in `lem:observer` (Step 1) and `thm:D` (Steps 2 and 4)
   hold after fitting the outputs to `⌈log₂(m+1)⌉` bits, which is free and keeps the value since
   the rank is at most `m` (`runB_set_fit`).  Proposed wording (optional), after the first
   sentence of `lem:observer`: "We may assume that the circuit has $\lceil\log_2(m+1)\rceil$
   outputs: further outputs are identically zero and are dropped."
3. Clusters (`lem:observer`, Step 2) are the classes of the reflexive transitive closure of the
   linkage relation; setting the diagonal after Warshall's algorithm costs one more gate
   (`rtcB_impl`).  No change to the paper.
4. Subtraction is the subtraction of natural numbers (`0` when the subtrahend is larger); it is
   exact when the difference is nonnegative, as for `r₂(E \ B) + |B| - r₂(E)` in `thm:D`,
   Step 2.  No change to the paper.


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/BoolAlg/Impl.lean` | 445 |
| `SignedTropical/BoolAlg/Bits.lean` | 389 |
| `SignedTropical/BoolAlg/Arith.lean` | 620 |
| `SignedTropical/BoolAlg/Count.lean` | 293 |
| `SignedTropical/BoolAlg/Rel.lean` | 370 |
| `SignedTropical/BoolAlg/Path.lean` | 456 |
| `SignedTropical/BoolAlg/ExchangeBits.lean` | 173 |
| total | 2746 |


## 5. Not done

* Every item of the assignment (numbers, running a circuit on computed wires, Warshall's
  algorithm, breadth-first layers, least-index selection, iteration and sequential composition)
  is proved with exact gate counts.  Added: the least-index shortest path, its exchange, the
  identification of the exchange with one round `augStep` of P2, and independence tests from a
  rank circuit.
* The circuit of the augmenting path algorithm (P6b) and the observer of `lem:observer` are
  assigned to later agents.  What remains for P6b: the bit gadgets for the sources, arcs and
  sinks of the exchange graph of `I` (built from `indepB_impl` and free rearrangements, with the
  hypotheses `hS`, `hG`, `hK` of Section 1.7), the rounds (Section 6.4, whose skeleton is
  compiled), and `Av(N)` and the guard.  What remains for the observer: Steps 1 to 3 of
  `lem:observer` (`PO`, clusters, rank queries of `N_G`), for which the gadgets of Sections 1.3
  to 1.5 are ready.


## 6. API for later agents

All names are in the namespace `SignedTropical.BoolAlg`; `open SignedTropical
SignedTropical.BoolAlg` makes them and the Phase 1 builders available.  Every snippet marked
"compiled" below was checked with `lake env lean` against the final modules.

### 6.1 The judgement and the representations

`Impl R₁ R₂ b c F` (`Impl.lean`): for every gate list `gs`, object `s` and values
`T : (Fin n → Bool) → τ₁` with `R₁.rep gs s T`, the builder call `b s gs` returns a gate list
that extends `gs` (prefix) by exactly `c` gates and an object carrying `x ↦ F (T x)`.  `F` is a
function of the carried value only, so correctness lemmas are statements about `F`.

| representation | object (operands) | value |
| :-- | :-- | :-- |
| `bitR` | `Arg n` | `Bool` |
| `vecR r` | `Fin r → Arg n` | `Fin r → Bool` (a subset of `Fin r`) |
| `relR r` | `Fin r → Fin r → Arg n` | `Fin r → Fin r → Bool` (entry `u v` is the arc `u → v`) |
| `matR r s` | `Fin r → Fin s → Arg n` | `Fin r → Fin s → Bool` |
| `numR w` | `List (Arg n)` of length `w` | `ℕ` below `2^w`, least significant bit first |
| `bitsR L` | `List (Arg n)` of length `L` | `List Bool` |
| `R₁.prod R₂` | `σ₁ × σ₂` | `τ₁ × τ₂` |
| `Rep.pi ι R` | `ι → σ` | `ι → τ` |

The constant source `.const : Arg n` carries `false` in every gate list (`den_const gs`); the
input operands `fun i => .input i` carry the input (`input_rep gs`).

### 6.2 Composition and how sizes add

| combinator | result | gates |
| :-- | :-- | :-- |
| `h₁.comp h₂` | `Impl R₁ R₃ (seqB b₁ b₂) _ (fun t => F₂ (F₁ t))` | `c₁ + c₂` |
| `h₁.pair h₂` (same input `R`) | `Impl R (R₁.prod R₂) (pairB b₁ b₂) _ (fun t => (F₁ t, F₂ t))` | `c₁ + c₂` |
| `h.extend` | `Impl R (R.prod R₁) _ c (fun t => (t, F t))` | `c` |
| `Impl.self`, `Impl.fst`, `Impl.snd`, `Impl.free hg` | rearrangements | `0` |
| `h.pre (R := R₀) (g := g) (G := G) hg` | `Impl R₀ R₂ (fun s => b (g s)) c (fun t => F (G t))` | `c` |
| `h.post (R₃ := R₃) (g := g) (G := G) hg` | output rearranged | `c` |
| `Impl.tab fun i => h i` | `Impl R (Rep.pi (Fin r) R₂) (fun s => tabB fun i => b i s) _ (fun t i => F i t)` | `r * c` |
| `Impl.tabSum fun i => h i` | the same, with costs `c i` | `∑ i, c i` |
| `h.map r`, `h.map₂ r` | the gadget at every index of a family (of pairs) | `r * c` |
| `h.iterate k` | `Impl R R (iterB b k) _ F^[k]` | `k * c` |
| `Impl.fold fun a ha => h a` | one round per element of `l`, value `l.foldl` | `l.length * c` |
| `h.scan k` | entry `i` carries `F^[i]` | `k * c` |
| `h.iterateCtx k`, from `h : Impl (R₁.prod R₂) R₂ b c (fun t => F t.1 t.2)` | `Impl (R₁.prod R₂) R₂ (iterCtxB b k) _ (fun t => (F t.1)^[k] t.2)` | `k * c` |
| `h.scanCtx k`, `Impl.foldCtx` | every intermediate state; one round per list element | `k * c`, `l.length * c` |
| `h.cost hc`, `h.congr hF` | rewrite the count (`c = c'`) or the value (`∀ t, F t = G t`) | |

Practical points: give `R` to `pre` (and `R₃` to `post`) when the expected type is not known;
write `.cost (c' := …) (by ring)` to put a sum in normal form; in a rearrangement proof
`fun gs s T hs => …` with `if` on static indices, `dsimp only` and then `split_ifs` leave goals
closed by `hs.…` and `den_const gs`; the composed value is the composed function up to
β-reduction, so `exact` accepts it, and `Impl.congr` restates it.

### 6.3 Running a given circuit on computed wires

* `runB C v` (any gate set) appends the gates of `C : Circuit Op k`, input `i` of `C` reading
  the operand `v i`, and returns the output operands.  `runB_impl I C : Impl (Rep.pi (Fin k)
  (Rep.arg I)) (Rep.list I C.outs.length) (runB C) C.size (C.eval I)`.  For `BoolOp`, the input
  representation is `vecR k` and the output `bitsR C.outs.length` (abbreviations).
* `runB_num C : Impl (vecR k) (numR C.outs.length) (runB C) C.size (fun V => bitsVal (C.eval
  boolInterp V))`.
* `runB_set C hC`, with `hC : ∀ S, bitsVal (C.eval boolInterp (indicator S)) = f S`: value
  `fun V => f (univ.filter fun i => V i = true)`, `C.size` gates.
* `runB_set_fit C hC hw`, with `hw : ∀ S, f S < 2 ^ w`: the same on exactly `w` bits, builder
  `seqB (runB C) (pureB (fit w))`, `C.size` gates.
* `eqCardB_impl C hC hw`: `[f(T) = |T|]`, `C.size + popCost k + (5 * max w (Nat.size k) + 1)`
  gates.
* `indepB_impl N C hC`, with the Phase 1 rank hypothesis `hC : ∀ S, (bitsVal (C.eval boolInterp
  (indicator S)) : ℕ∞) = N.eRk (S : Set (Fin k))`: `Impl (vecR k) bitR (eqCardB C (Nat.size k))
  (C.size + popCost k + (5 * Nat.size k + 1)) (fun V => decide (N.Indep ↑(univ.filter fun i =>
  V i = true)))`.  The `decide` uses classical decidability; compare with another instance by
  `decide_eq_decide`.
* The vector fed to a query is any carried vector.  Compiled: the bits of `T + u - v` for static
  `u, v` are the free rearrangement `fun i => if i = u then t else if i = v then .const else
  V i` of the bits of `T`, with `t` one gate `true` (`true_impl`); with
  `(indepB_impl N C hC).pre` this costs `1 + (C.size + popCost m + (5 * Nat.size m + 1))` gates.
  A single `true` operand computed once can be shared by all queries (`Impl.extend`).
* If the matroid depends on the input of the whole circuit (as `N_G` in `lem:observer`), its
  rank query is a gadget from `(context, vector)`; feed it with `pre` and run the rounds with
  `Impl.iterateCtx`.

### 6.4 The augmenting path algorithm (for P6b)

Compiled skeleton.  Let `hG : Impl (vecR m) (relR m) bG cG FG`,
`hS : Impl (vecR m) (vecR m) bS cS FS` and `hK : Impl (vecR m) (vecR m) bK cK FK` with, for every
`I : Finset (Fin m)`, `hG' I : ∀ u v, FG (indicator I) u v = true ↔ Arc N blk I u v`,
`hS' I : ∀ y, FS (indicator I) y = true ↔ IsSource blk I y` and
`hK' I : ∀ y, FK (indicator I) y = true ↔ IsSink N I y`.  Then

```lean
have hround := ((Impl.self.pair (hG.pair (hS.pair hK))).comp exchangeB_impl).cost
  (c' := cG + cS + cK + pathCost m + 4 * m) (by ring)
have hsemi : Function.Semiconj indicator (augStep N blk)
    (fun V u => V u ^^ pathV (FG V) (FS V) (FK V) u) := fun I =>
  funext fun u => augStep_bits (hS' I) (hG' I) (hK' I) u
-- hround.iterate j : j * (cG + cS + cK + pathCost m + 4 * m) gates
-- (hsemi.iterate_right j I).symm : F^[j] (indicator I) = indicator ((augStep N blk)^[j] I)
```

The input of `exchangeB` is `(I, (G, S, Y))`, represented by `(vecR r).prod (pathInR r)` with
`pathInR r = (relR r).prod ((vecR r).prod (vecR r))`; `pathCost r = 8r³ + 7r² + 9r + 3`.  The
empty set is free (compiled: `Impl.free fun gs _ _ _ _ => (den_const gs).congr …`, value
`fun _ => indicator ∅`).  After `k` rounds from `∅`, `iterate_augStep N blk` (P2) gives a
rainbow independent set of size `ν(N)`.  For `Av(N)`: `av_eq hI hmax`; the reachable set is
`layerV G S m` (`layerV_iff_mem_reachSet`), computed by `layersB_impl m` (entry `Fin.last m`,
`2m³` gates) or by `bfsStepB_impl.iterateCtx m` (`2m³` gates; `layerV G S d` is by definition
`(bfsStep G)^[d] S`).  The guard `[|I| ≤ r₀]` is
`vecPopcountB_impl.comp (numLeConstB_impl r₀ (Nat.size m))`, with
`popCost m + 5 max(⌈log₂(m+1)⌉, ⌈log₂(r₀+1)⌉) + 2` gates (compiled).

Facts for the gadgets of the exchange graph (P2, `Rainbow/Exchange.lean`):
`Arc N blk I u v` is by definition
`(u ∉ I ∧ v ∈ I ∧ N.Indep (insert u (↑I \ {v}))) ∨ (u ∈ I ∧ v ∉ I ∧ blk v = blk u)` (no arc
`u → u`); `IsSource blk I y ↔ y ∉ I ∧ blk y ∉ blocksMet blk I` (`isSource_iff`, with
`blocksMet blk I = I.image blk`); `IsSink N I y` is by definition
`y ∉ I ∧ N.Indep (insert y ↑I)`.  The block tests `blk v = blk u` are static: they choose
operands and cost no gate.

Other names of the path layer: `pathB_impl`, `pathV_eq_true_iff`
(`pathV G S Y u = true ↔ u ∈ pathSet G S Y`), `exchangeB_impl`, `layerV_iff_mem_layer`,
`augStep_eq_symmDiff`, `predV_eq_leastPred`, `backV_eq_backPath`, `leadV_sink_eq`,
`leadV_pred_eq`, `find_sink_layer_le`.

### 6.5 From an implementation to a circuit

`vecCircuit_spec h` (`h : Impl (vecR n) (vecR L) b c F`): `(vecCircuit b).size = c`,
`(vecCircuit b).outs.length = L`, `(vecCircuit b).eval boolInterp x = List.ofFn (F x)`.
`circuitOf_num h` (`h : Impl (vecR n) (numR w) b c F`): size `c`, `w` outputs,
`bitsVal (eval x) = F x`.  `circuitOf_spec` for a list of outputs (any gate set),
`seqCircuit_spec` for two circuits in sequence (sizes add).

### 6.6 Other verified compositions

`((runB_set_fit C hC hw).pair vecPopcountB_impl).comp (numEqB_impl w (Nat.size m))` is
`eqCardB_impl`; `warshallB_impl.comp (vecFirstB_impl.map m)` is the closure followed by
least-index selection in every row, `2m³ + 3m²` gates (`lem:observer`, Step 2).
