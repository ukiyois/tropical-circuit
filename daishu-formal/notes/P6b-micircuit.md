# P6b: the matroid intersection circuit

Natural-language companion of `SignedTropical/Rainbow/MICircuit.lean`, namespace
`SignedTropical.Rainbow.MI`.  Sources: `daishu/paper/greedy_intersection.tex`, Lemma
`lem:observer`, Step 4, and Lemma `lem:avoidable` (for `Av`); the augmenting path algorithm of
`Rainbow/Exchange.lean` (P2: `Arc`, `IsSource`, `IsSink`, `reachSet`, `augStep`,
`iterate_augStep`, `nu_le`, `av_eq`); the Boolean library of `BoolAlg/*.lean` (P6a: `Impl` and its
combinators, `exchangeB_impl`, `augStep_bits`, `layerV_iff_mem_reachSet`, `bfsStepB_impl`,
`vecPopcountB_impl`, `numLeConstB_impl`, `numEqB_impl`, `runB_num`, `circuitOf_spec`,
`vecCircuit_spec`, `circuitOf_num`).

Build status: `lake build SignedTropical.Rainbow.MICircuit` succeeds with no error and no
warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or
`opaque`.  `#print axioms` of all 44 theorems of the module: `propext`, `Classical.choice`,
`Quot.sound` only (three of them on fewer).  The module imports `BoolAlg/ExchangeBits.lean` and
`BoolAlg/Count.lean`.

Conventions.  `E = Fin m`; `blk : Fin m → Fin k`, block `b` is `blk⁻¹(b)`; `N` is a matroid on
`Fin m` (no hypothesis on its ground set).  A set is carried by its bits `A : Fin m → Bool`, the
set being `{i : A i}` (Lean `univ.filter fun i => A i = true`); `1_J` is the indicator vector
`indicator J`.  `I - v + u = (I \ {v}) ∪ {u}` and `I + y = I ∪ {y}`.  `W = ⌈log₂(m+1)⌉` is
`Nat.size m`.  Gate counts are exact: `Impl R₁ R₂ b c F` (P6a) says that the builder `b`
appends exactly `c` gates and that its result carries `F` of what its argument carries, at every
input.

Context and oracle.  The circuit reads a *context*, an object carried by a representation
`Rc : Rep BoolOp Bool n σ τ` whose value `a : τ` depends on the input of the whole circuit: the
input bits themselves (`Rc = vecR n`), or data computed from them once, such as the context of
the observer (P6c).  Independence is answered by an *oracle*, a gadget
`hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo` that computes the bit `Fo (a, A)` from the context
and the bits of a set `A` with `cO` gates.  `Fo` is arbitrary.  `Fo` *answers independence in `N`
at `a`* when `Fo (a, A) = [{i : A i} is independent in N]` for every `A`, in Lean
`∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))` (classical `decide`).
The circuit is built and counted for every `Fo`; the statements about its outputs hold at every
context where the oracle answers independence in some matroid `N`, which may depend on the
context.  The circuit queries the oracle only at its own context.


## 1. Results

### 1.1 The values

**Definition 1.**  For an oracle `Fo`, blocks `blk`, a context `a` and bits `I`, `R`:

* `exchV I u v`, the bits of `I - v + u`; `addV I y`, the bits of `I + y`;
* `arcV Fo blk a I u v`: `false` if `u = v`, and otherwise
  `(¬I u ∧ I v ∧ Fo(a, I - v + u)) ∨ (β ∧ ¬I v)` with `β = I u` if `blk v = blk u` and
  `β = false` otherwise;
* `srcV blk I y = ¬∃ x, blk x = blk y ∧ I x`;
* `sinkV Fo a I y = ¬I y ∧ Fo(a, I + y)`;
* `roundV Fo blk a I = I ⊕ pathV (arcV Fo blk a I) (srcV blk I) (sinkV Fo a I)`, where `pathV`
  (P6a, `BoolAlg/Path.lean`) marks the least-index shortest path from the sources to the sinks;
* `stateV Fo blk a = (roundV Fo blk a)^k(∅)`, `k` the number of blocks;
* `reachV Fo blk a I = layerV (arcV Fo blk a I) (srcV blk I) m`, layer `m` of the breadth-first
  search;
* `avV blk I R b = (¬∃ x, blk x = b ∧ I x) ∨ (∃ x, blk x = b ∧ I x ∧ R x)`;
* `miV Fo blk r₀ a = (I, |I|, [|I| ≤ r₀], avV blk I (reachV Fo blk a I))` with
  `I = stateV Fo blk a`.

### 1.2 Correctness

**Theorem 2 (`lem:observer`, Step 4, correctness).**  Let `Fo` answer independence in `N` at
`a`, and let `J ⊆ E`.

1. `arcV_iff`: `arcV Fo blk a 1_J u v` holds iff `u → v` is an arc of the exchange graph of `J`
   (`Arc N blk J u v`); `srcV_iff`: `srcV blk 1_J y` holds iff `y` is a source
   (`IsSource blk J y`); `sinkV_iff`: `sinkV Fo a 1_J y` holds iff `y` is a sink
   (`IsSink N J y`).
2. `roundV_indicator`: `roundV Fo blk a 1_J = 1_{augStep N blk J}`; a round of the circuit is one
   round of the augmenting path algorithm of P2.
3. `stateV_eq`: `stateV Fo blk a = 1_{augStep^k(∅)}`.
4. `reachV_iff`: `reachV Fo blk a 1_J v` holds iff `v` is reachable from a source
   (`v ∈ reachSet N blk J`).
5. `avV_eq`: if `J` is rainbow independent with `|J| = ν(N)`, then
   `avV blk 1_J (reachV Fo blk a 1_J) b = [b ∈ Av(N)]` for every block `b`.
6. `miV_spec`: put `J₀ = augStep^k(∅)`.  The first output of `miV Fo blk r₀ a` is `1_{J₀}`, and
   `J₀` is rainbow independent with `|J₀| = ν(N)`; the second output is `ν(N)`, the third is
   `[ν(N) ≤ r₀]`, and the fourth is `b ↦ [b ∈ Av(N)]`.

*Proof.*  Step 1, the arcs.  For `u = v` both sides are false, since an arc joins `J` and its
complement.  For `u ≠ v` the set entries of `exchV 1_J u v` form `J - v + u`, so by the hypothesis
on `Fo` the first term is `u ∉ J ∧ v ∈ J ∧ (J - v + u independent)`, and the second term is
`u ∈ J ∧ v ∉ J ∧ blk v = blk u`; the two sides agree in each case of `blk v = blk u`, `u ∈ J`,
`v ∈ J`.

Step 2, the sources and sinks.  `blk y ∉ blk(J)` iff no `x ∈ J` has `blk x = blk y`.  The set
entries of `addV 1_J y` form `J + y`.

Step 3, a round.  With the three bit families of Steps 1 and 2, `augStep_bits` (P6a) gives
`[u ∈ augStep N blk J] = [u ∈ J] ⊕ pathV G S K u`, which is `roundV Fo blk a 1_J` at `u`.

Step 4, `k` rounds.  By Step 3, `indicator` semiconjugates `augStep N blk` to `roundV Fo blk a`,
hence their `k`-th iterates (`Function.Semiconj.iterate_right`); and `1_∅` is the zero vector.

Step 5, the reachable set: `layerV_iff_mem_reachSet` (P6a) with Step 1.

Step 6, the avoidable blocks.  `av_eq` (P2) gives `Av(N) = M_J ∪ blk(J ∩ R)`: `b ∈ M_J` iff no
`x ∈ J` has `blk x = b`, and `b ∈ blk(J ∩ R)` iff some `x ∈ J ∩ R` has `blk x = b`; Step 5
identifies `R`.

Step 7, `miV_spec`.  `iterate_augStep` (P2) shows that `J₀` is rainbow independent of size
`ν(N)`; `k` rounds suffice since `ν(N) ≤ k` (`nu_le`).  The set entries of `1_{J₀}` form `J₀`
(`filter_indicator`), so the count and the guard are `ν(N)` and `[ν(N) ≤ r₀]` (Step 4); Step 6
with `J = J₀` gives the last output.

### 1.3 The gadgets and their gate counts

**Theorem 3 (`lem:observer`, Step 4, the circuit).**  Let `hO` be an oracle gadget with `cO`
gates.  Each builder below implements the stated value with exactly the stated number of gates.

| builder | reads | value | gates | Lean |
| :-- | :-- | :-- | :-- | :-- |
| `prepB` | `(a, I)` | `(a, I, ¬I, true)` | `m + 1` | `prepB_impl` |
| `arcB bO blk u v` | `(a, I, ¬I, true)` | the arc test `u → v` | `cO + 4` | `arcB_impl` |
| `arcsB bO blk` | `(a, I, ¬I, true)` | `arcV` at every pair | `m(m-1)(cO + 4)` | `arcsB_impl` |
| `srcsB blk` | `(a, I, ¬I, true)` | `srcV blk I` | `m(m + 1)` | `srcsB_impl` |
| `sinksB bO` | `(a, I, ¬I, true)` | `sinkV Fo a I` | `m(cO + 1)` | `sinksB_impl` |
| `roundB bO blk` | `(a, I)` | `roundV Fo blk a I` | `roundCost m cO` | `roundB_impl` |
| `roundsB bO blk` | `a` | `(a, stateV Fo blk a)` | `k · roundCost m cO` | `roundsB_impl` |
| `reachB bO blk` | `(a, I)` | `reachV Fo blk a I` | `m(m-1)(cO + 4) + 2m³ + m² + 2m + 1` | `reachB_impl` |
| `avB blk` | `(I, R)` | `avV blk I R` | `m + k(2m + 2)` | `avB_impl` |
| `nuGuardB r₀` | `I` | `(|I|, [|I| ≤ r₀])`, `|I|` on `W` bits | `popCost m + 5 max(W, ⌈log₂(r₀+1)⌉) + 2` | `nuGuardB_impl` |
| `miB bO blk r₀` | `a` | `miV Fo blk r₀ a` | `miCost m k cO r₀` | `miB_impl` |

The values of `arcB`, `arcsB` and `sinksB` are stated in Lean as functions of the four
components; at a prepared tuple `(a, I, ¬I, true)` they are the arc bit, `arcV Fo blk a I` and
`sinkV Fo a I`.  Here `roundCost m cO = m²cO + 8m³ + 12m² + 12m + 4` and
`miCost m k cO r₀ = k · roundCost m cO + m(m-1)(cO + 4) + 2m³ + m² + 3m + 2k(m + 1) + popCost m +
5 max(W, ⌈log₂(r₀+1)⌉) + 3`, with `popCost m ≤ 22m` (P6a).  Per round the oracle is queried
`m(m-1)` times for the arcs and `m` times for the sinks, `m²` times in all; the final exchange
graph queries it `m(m-1)` times.

*Proof.*  Step 1, preparation: `m` negations (`vecNotB_impl`) and one gate `true`
(`true_impl`); rearranging operands costs no gate.

Step 2, one arc test, for `u ≠ v`.  The operands of `I - v + u` are a free rearrangement: entry
`u` reads the shared `true`, entry `v` the constant `false`, the others the operands of `I`.  The
oracle on them gives `q` (`cO` gates); then `(¬I u ∧ (I v ∧ q)) ∨ (β ∧ ¬I v)` costs four gates
(`arcGateB_impl`), where `β` is the operand of `I u` if `blk v = blk u` and the constant `false`
otherwise, a static choice that costs no gate.

Step 3, all arcs.  The diagonal gets the constant `false` with no gate (`impl_ite`, `false_impl`),
every ordered pair of distinct elements one arc test (`Impl.tabSum`), and
`Σ_u Σ_v [u ≠ v](cO + 4) = m(m-1)(cO + 4)` (`sum_offDiag`).

Step 4, the sources: for each `y`, `vecAnyB` (`m` gates) on the vector whose entry `x` is the
operand of `I x` if `blk x = blk y` and the constant `false` otherwise (static), then a negation;
`exists_ite_eq_true` turns the masked vector into the condition `blk x = blk y`.  The sinks: for
each `y`, the oracle on the operands of `I + y` and one `∧` with `¬I y`.

Step 5, a round: preparation, the exchange graph `(G, S, K)`, and `exchangeB_impl` (P6a,
`pathCost m + 4m = 8m³ + 7m² + 13m + 3` gates) on `(I, (G, S, K))`.  Since the prepared values are
`¬I` and `true`, the value is `I ⊕ pathV G S K = roundV Fo blk a I` by definition.  The counts
add to `roundCost m cO` (`roundCost_eq`, with `m(m-1) + m = m²`).

Step 6, `k` rounds with the context threaded through: the empty set is the constant operands
(free), and `Impl.iterateCtx` gives `k · roundCost m cO` gates and the value
`(roundV Fo blk a)^k(∅) = stateV Fo blk a`; `Impl.extend` keeps the context.

Step 7, one more exchange graph: preparation, arcs and sources (no sinks), and `m` breadth-first
steps (`bfsStepB_impl.iterateCtx m`, `2m³` gates), whose value is `layerV G S m` by definition.

Step 8, the avoidable blocks: `I ∧ R` (`m` gates); for each block `b`, `vecAnyB` on `I` masked by
block `b`, a negation, `vecAnyB` on `I ∧ R` masked by block `b`, and an `∨`, `2m + 2` gates.

Step 9, the population count of `I` on `W` bits (`vecPopcountB_impl`) and the comparison with the
constant `r₀` (`numLeConstB_impl`).

Step 10, `miB`: the `k` rounds; then, from `(a, I)`, the state `I`, Step 9, and Step 8 on
`(I, reachV Fo blk a I)`, rearranged into `(I, |I|, guard, Av bits)` (free).  The counts add to
`miCost m k cO r₀`, and the value is `miV Fo blk r₀ a`.

### 1.4 The size

**Theorem 4.**  `miCost_add_le`:
`miCost m k cO r₀ + k ≤ (k + 1)(m + 1)²(cO + 10(m + 1)) + 5⌈log₂(r₀+1)⌉`; `miCost_le`: the same
bound for `miCost m k cO r₀`.  `miCost_rank_le`: for the oracle from a rank query of `cR` gates
(Theorem 7, `cO = cR + popCost m + 5W + 1`),
`miCost m k cO r₀ + k ≤ (k + 1)(m + 1)²(cR + 37(m + 1)) + 5⌈log₂(r₀+1)⌉`.

*Proof.*  Step 1, `m(m-1)(cO + 4) ≤ m²(cO + 4)`, `popCost m ≤ 22m` (`popCost_le`) and
`max(W, ⌈log₂(r₀+1)⌉) ≤ m + ⌈log₂(r₀+1)⌉` (`size_le_self`).  Step 2, the left side is then at most
`(k + 1)m²cO + k(8m³ + 12m² + 14m + 7) + 2m³ + 5m² + 30m + 3 + 5⌈log₂(r₀+1)⌉`, while the right side
is `(k + 1)(m² + 2m + 1)cO + (k + 1)(10m³ + 30m² + 30m + 10) + 5⌈log₂(r₀+1)⌉`; compare the
coefficients (`nlinarith`).  Step 3, `miCost_rank_le`: `popCost m + 5W + 1 + 10(m + 1) ≤ 37(m + 1)`
since `W ≤ m`.

**Theorem 5 (Lemma `lem:observer`, Step 4, packaged).**  `lem_observer_step4`: for an oracle
gadget `hO` of `cO` gates, (1) `miB bO blk r₀` computes `miV Fo blk r₀` from the context with
`miCost m k cO r₀` gates; (2) `miCost m k cO r₀ + k ≤ (k + 1)(m + 1)²(cO + 10(m + 1)) +
5⌈log₂(r₀+1)⌉`; (3) at every context `a` at which `Fo` answers independence in a matroid `N`,
the conclusion of `miV_spec` holds.

*Proof.*  Theorems 3, 4 and 2(6).

### 1.5 Outputs for the observer and for rank circuits; circuits on the input

**Theorem 6.**

1. `avGuardB_impl`, `avGuardV_eq`: from the context, `avGuardB bO blk r₀` computes the `k` bits
   `[|I| ≤ r₀] ∧ avV …` with `miCost m k cO r₀ + k` gates; at a context where `Fo` answers
   independence in `N`, bit `b` is `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`, the bit `F_b` of
   `lem:observer`.
2. `nuB_impl`, `card_stateV`: from the context, `nuB bO blk` computes `|stateV Fo blk a|` on `W`
   bits with `k · roundCost m cO + popCost m` gates (no final exchange graph); at a context where
   `Fo` answers independence in `N`, the value is `ν(N)`.
3. When the context is the input (`Rc = vecR n`): `miCircuit_spec`: `miCircuit bO blk r₀` has
   `miCost m k cO r₀` gates and `m + W + k + 1` outputs, and at every input `x` at which `Fo`
   answers independence in a matroid `N` its outputs are `1_{J₀}` (`J₀ = augStep^k(∅)`), the `W`
   binary digits of `ν(N)` (least significant first), `[ν(N) ≤ r₀]`, and the bits
   `[b ∈ Av(N)]`; `avGuardCircuit_spec`: `miCost m k cO r₀ + k` gates, `k` outputs
   `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`; `nuCircuit_spec`: `k · roundCost m cO + popCost m` gates, `W`
   outputs whose value (`bitsVal`) is `ν(N)`.

*Proof.*  Step 1, item 1 composes `miB_impl` with `vecMaskB_impl` (`k` gates); the values come
from `miV_spec`.  Step 2, item 2 composes `roundsB_impl` with `vecPopcountB_impl`; the value is
`ν(N)` by `stateV_eq`, `filter_indicator` and `iterate_augStep`.  Step 3, item 3: `circuitOf_spec`,
`vecCircuit_spec`, `circuitOf_num` (P6a) on the implementations from the input operands.  For
`miCircuit` the outputs are flattened into one list (`flatB_impl`, free); a number carried on `W`
bits is carried by its binary digits `ν.testBit i`, `i < W` (`numR_bitsR`: the carried bits have
length `W` and value `ν mod 2^W = ν`, and bit lists of one length with one value are equal,
`eq_of_bitsVal_eq`, `bitsVal_testBit`).

### 1.6 Oracles from rank queries and from one rank circuit

**Theorem 7.**

1. `indepOfRankB_impl`: if `hR : Impl (Rc.prod (vecR m)) (numR w) bR cR Fr` computes a number
   `Fr (a, A)` from the context and a set with `cR` gates, then `indepOfRankB bR` computes
   `indepOfRankV Fr (a, A) = [Fr (a, A) mod 2^W = |A|]` with `cR + popCost m + 5W + 1 ≤
   cR + 27m + 1` gates.
2. `indepOfRank_correct`: if `Fr (a, 1_S) = r_N(S)` for every `S ⊆ E`, then `indepOfRankV Fr`
   answers independence in `N` at `a`.
3. `rankQueryB_impl`, `circuitOracleB_impl`, `circuitOracle_correct`: for a circuit `C` on
   `p + m` inputs and of size `s`, reading the context bits `a : Fin p → Bool` followed by the set
   bits (`Fin.append a A`), the rank query `rankQueryV C` costs `s` gates and the oracle
   `indepOfRankV (rankQueryV C)` costs `s + popCost m + 5W + 1` gates; at every `a` with
   `bitsVal (C(a, 1_S)) = r_N(S)` for all `S` (the rank hypothesis of Phase 1 read at `a`, in
   `ℕ∞` with `N.eRk`), this oracle answers independence in `N` at `a`.
4. `rankMICircuit_spec`: for such a `C` on `n + m` inputs, `rankMICircuit C blk r₀` (on `n`
   inputs, the context being the input) has
   `miCost m k (s + popCost m + 5W + 1) r₀ ≤ (k + 1)(m + 1)²(s + 37(m + 1)) + 5⌈log₂(r₀+1)⌉`
   gates and `m + W + k + 1` outputs, and at every input `x` at which `C(x, ·)` outputs the rank
   of a matroid `N`, its outputs are those of Theorem 6(3).

*Proof.*  Step 1, item 1: the number fitted to `W` bits (`numFit_impl`, free, value
`Fr mod 2^W`), the population count (`vecPopcountB_impl`) and `numEqB_impl` on `W` bits.  Step 2,
item 2: with `S = {i : A i}`, `A = 1_S` (`indicator_filter`) and `r_N(S) ≤ |S| ≤ m < 2^W`, so the
fitted value is `r_N(S)`; a finite set is independent iff its rank is its size
(`Matroid.indep_iff_eRk_eq_encard_of_finite`).  Step 3, item 3: `runB_num` (P6a) on the operands
`Fin.append` of the context and the set (`Fin.addCases`, free); then items 1 and 2, the
hypothesis in `ℕ∞` giving the one in `ℕ` (`coe_rk`).  Step 4, item 4: `miCircuit_spec` with this
oracle, and `miCost_rank_le`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer` Step 4: "Run `k` rounds of the augmenting path algorithm on `N_G` and the blocks" | `roundV`, `stateV`, `roundB_impl`, `roundsB_impl`, `roundV_indicator`, `stateV_eq` | `Rainbow/MICircuit` | proved |
| Step 4: "the exchange graph needs `O(m²)` independence tests, one rank query each" | `arcV`, `srcV`, `sinkV`, `arcB_impl`, `arcsB_impl`, `srcsB_impl`, `sinksB_impl`, `arcV_iff`, `srcV_iff`, `sinkV_iff`; `indepOfRankV`, `indepOfRankB_impl`, `indepOfRank_correct` | same | proved |
| Step 4: "a breadth-first search, the choice of a shortest path ... and the exchange cost `O(m³)` gates" | `roundB_impl` (with `exchangeB_impl`, `augStep_bits` of P6a), `roundCost`, `roundCost_eq` | same | proved |
| Step 4: "One more exchange graph and its reachable set give `Av(N_G)` as in Lemma `lem:avoidable`" | `reachV`, `avV`, `reachB_impl`, `avB_impl`, `reachV_iff`, `avV_eq` | same | proved |
| Step 4: "comparing `|I|` with `r₀` gives the guard" | `nuGuardB_impl`, `miV_spec` | same | proved |
| Step 4: "The total is `(k+1)(O(m²)(2ms+O(m²))+O(m³)) = O(km³(s+m))`" | `miCost`, `miCost_add_le`, `miCost_le`, `miCost_rank_le` | same | proved |
| Step 4, packaged; outputs `F_b = [ν ≤ r₀] ∧ [b ∈ Av]` at good contexts | `miB_impl`, `miV_spec`, `lem_observer_step4`, `avGuardB_impl`, `avGuardV_eq` | same | proved |
| the circuits on the input | `miCircuit_spec`, `avGuardCircuit_spec`, `nuCircuit_spec`, `nuB_impl`, `card_stateV` | same | proved |
| a rank circuit reading (context bits, set bits) as the oracle | `rankQueryV`, `rankQueryB_impl`, `circuitOracleB_impl`, `circuitOracle_correct`, `rankMICircuit_spec` | same | proved |


## 3. Differences from the paper

1. Correctness pointwise in the context.  The circuit is a fixed circuit; its outputs are
   `1_{J₀}`, `ν(N)`, the guard and the bits `[b ∈ Av(N)]` at every input at which the oracle
   answers independence in the intended matroid `N` (`miV_spec`, `lem_observer_step4`).  This is the form the paper uses ("the outputs are correct
   whenever `G = G_t` for some `v` and `t ≥ 0`").  No change to the paper.
2. The rounds.  The circuit runs `k` rounds of augmentation and then builds one more exchange
   graph (arcs and sources only) for `Av`, the `k + 1` exchange graphs of the paper's total;
   `k` rounds suffice since `ν(N) ≤ k` (`nu_le`, `iterate_augStep`).  No change to the paper.
3. The tests per round.  Which pairs `(u, v)` have `u ∉ I`, `v ∈ I` depends on `I`, which is
   computed inside the circuit, so every ordered pair `u ≠ v` gets a query of `I - v + u` (masked
   when `u ∈ I` or `v ∉ I`): `m(m-1)` arc tests and `m` sink tests, `m²` independence tests per
   round, and `m(m-1)` for the final exchange graph.  An independence test from a rank query is
   the query compared with `|A|`: a population count and a comparison, `O(m)` gates more
   (`indepOfRankB_impl`), absorbed in the cost of the query.  The paper's accounting
   `(k+1)(O(m²)(2ms+O(m²))+O(m³))` is confirmed with explicit constants
   (`miCost_add_le`): with `q` gates per independence test, at most
   `(k+1)(m+1)²(q + 10(m+1)) + 5⌈log₂(r₀+1)⌉` gates, including the `k` gates of the bits `F_b`.
   Proposed wording (optional, makes the constants explicit), for Step 4:
   "\emph{Step 4, matroid intersection.}  Run $k$ rounds of the augmenting path
   algorithm~\cite{lawler75,schrijver03} on $N_G$ and the blocks; $k$ rounds suffice since
   $\nu(N_G)\le k$.  In each round the exchange graph needs $m^{2}$ independence tests,
   $m(m-1)$ for the arcs ($I-x+y$) and $m$ for the sinks ($I+y$), one rank query each; a
   breadth-first search, the choice of a shortest path (the sink of least index in the first
   layer that contains a sink, then predecessors of least index) and the exchange cost
   $8m^{3}+O(m^{2})$ gates.  One more exchange graph and its reachable set ($2m^{3}$ gates)
   give $\Av(N_G)$ as in Lemma~\ref{lem:avoidable}, and comparing $|I|$ with $r_0$ gives the
   guard.  With $q$ gates per independence test the total is at most
   $(k+1)(m+1)^{2}(q+10(m+1))+5\lceil\log_2(r_0+1)\rceil$, which is $O(km^{3}(s+m))$ for
   $q=2ms+O(m^{2})$."
4. The ground set of `N` is unrestricted: the statements hold for every matroid on `Fin m`, and
   `N_G` of the paper has ground set `E`.  No change to the paper.
5. The guard compares `|I|` on `⌈log₂(m+1)⌉` bits with the constant `r₀`; its cost depends on
   `⌈log₂(r₀+1)⌉`, which is at most `⌈log₂ k⌉` for the paper's `r₀ ∈ {1, …, k-1}`.  No change to
   the paper.


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/MICircuit.lean` | 856 |


## 5. Not done

* Every item of the assignment is proved: the implementation for any context and any oracle
  (`miB_impl`), the circuit when the context is the input (`miCircuit_spec`), the exact and the
  explicit size bounds (`roundCost`, `miCost`, `miCost_add_le`), correctness from the lemmas of
  P2 at every context where the oracle answers independence (`miV_spec`), and the special case of
  a rank circuit reading (context bits, set bits) (`rankMICircuit_spec`).
* Outside the assignment: the composition with the observer's context and oracle, the circuit
  of Lemma `lem:observer` as a whole, and `F_b(E × E) = 0` (Step 5) belong to the observer
  (P6c, phase 2); the snippet of Section 6.3, compiled against `Rainbow/ObserverOracle.lean` as
  built at 10:14 on 2026-10-12 (where the bits of a relation are `relBits`), shows the
  composition.  Rank circuits of transversal matroids belong to a
  later agent (Section 6.4).


## 6. API for later agents

Namespace `SignedTropical.Rainbow.MI`; `open SignedTropical SignedTropical.BoolAlg
SignedTropical.Rainbow SignedTropical.Rainbow.MI`.  Variables: `Rc : Rep BoolOp Bool n σ τ` (the
context), `bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)`, `Fo : τ × (Fin m → Bool) → Bool`,
`hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo` (the oracle), `blk : Fin m → Fin k`, `r₀ : ℕ`.
"`Fo` good at `a` for `N`" abbreviates the hypothesis
`hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))` (classical `decide`,
as in `indepB_impl` of P6a).

### 6.1 Values and correctness

* `stateV Fo blk a : Fin m → Bool`, the state after `k` rounds; `miV Fo blk r₀ a :
  (Fin m → Bool) × ℕ × Bool × (Fin k → Bool)` = `(I, |I|, [|I| ≤ r₀], Av bits)`; `roundV`,
  `reachV`, `avV`, `arcV`, `srcV`, `sinkV` as in Definition 1.
* `miV_spec hFo r₀ : (miV Fo blk r₀ a).1 = indicator ((augStep N blk)^[k] ∅) ∧
  IsRainbowIndep N blk ((augStep N blk)^[k] ∅) ∧ ((augStep N blk)^[k] ∅).card = nu N blk ∧
  (miV Fo blk r₀ a).2.1 = nu N blk ∧ (miV Fo blk r₀ a).2.2.1 = decide (nu N blk ≤ r₀) ∧
  ∀ b, (miV Fo blk r₀ a).2.2.2 b = decide (b ∈ Av N blk)`.
* `avGuardV_eq hFo r₀ b : ((miV Fo blk r₀ a).2.2.1 && (miV Fo blk r₀ a).2.2.2 b) =
  (decide (nu N blk ≤ r₀) && decide (b ∈ Av N blk))`.
* `card_stateV hFo : (univ.filter fun i => stateV Fo blk a i = true).card = nu N blk`.
* `stateV_eq hFo : stateV Fo blk a = indicator ((augStep N blk)^[k] ∅)`;
  `roundV_indicator hFo J`, `reachV_iff hFo J v`, `avV_eq hFo hJ hmax b`, `arcV_iff`,
  `srcV_iff`, `sinkV_iff` (Theorem 2).

### 6.2 Implementations and sizes

* `miB_impl hO blk r₀ : Impl Rc (outR m k) (miB bO blk r₀) (miCost m k cO r₀) (miV Fo blk r₀)`,
  with `outR m k = (vecR m).prod ((numR (Nat.size m)).prod (bitR.prod (vecR k)))`.
* `lem_observer_step4 hO blk r₀`: `miB_impl`, `miCost_add_le` and `∀ a N, hFo → (miV_spec)`.
* `avGuardB_impl hO blk r₀ : Impl Rc (vecR k) (avGuardB bO blk r₀) (miCost m k cO r₀ + k)
  (fun a b => (miV Fo blk r₀ a).2.2.1 && (miV Fo blk r₀ a).2.2.2 b)` (the observer's bits).
* `nuB_impl hO blk : Impl Rc (numR (Nat.size m)) (nuB bO blk) (k * roundCost m cO + popCost m)
  (fun a => (univ.filter fun i => stateV Fo blk a i = true).card)` (`ν` alone).
* `roundsB_impl hO blk : Impl Rc (Rc.prod (vecR m)) (roundsB bO blk) (k * roundCost m cO)
  (fun a => (a, stateV Fo blk a))`; `roundB_impl hO blk : Impl (Rc.prod (vecR m)) (vecR m)
  (roundB bO blk) (roundCost m cO) (fun t => roundV Fo blk t.1 t.2)`;
  `reachB_impl hO blk : Impl (Rc.prod (vecR m)) (vecR m) (reachB bO blk)
  (m * (m - 1) * (cO + 4) + 2 * m ^ 3 + m ^ 2 + 2 * m + 1) (fun t => reachV Fo blk t.1 t.2)`;
  `avB_impl blk : Impl ((vecR m).prod (vecR m)) (vecR k) (avB blk) (m + k * (2 * m + 2))
  (fun P => avV blk P.1 P.2)`; `nuGuardB_impl r₀`.
* `roundCost m cO = m ^ 2 * cO + 8 * m ^ 3 + 12 * m ^ 2 + 12 * m + 4`;
  `miCost m k cO r₀ = k * roundCost m cO + m * (m - 1) * (cO + 4) + 2 * m ^ 3 + m ^ 2 + 3 * m +
  2 * k * (m + 1) + popCost m + 5 * max (Nat.size m) (Nat.size r₀) + 3`.
* `miCost_add_le m k cO r₀ : miCost m k cO r₀ + k ≤ (k + 1) * (m + 1) ^ 2 * (cO + 10 * (m + 1)) +
  5 * Nat.size r₀`; `miCost_le` (without `+ k`); `miCost_rank_le m k cR r₀ :
  miCost m k (cR + popCost m + (5 * Nat.size m + 1)) r₀ + k ≤
  (k + 1) * (m + 1) ^ 2 * (cR + 37 * (m + 1)) + 5 * Nat.size r₀`.
* Oracles: `indepOfRankB_impl hR : Impl (Rc.prod (vecR m)) bitR (indepOfRankB bR)
  (cR + popCost m + (5 * Nat.size m + 1)) (indepOfRankV Fr)` for
  `hR : Impl (Rc.prod (vecR m)) (numR w) bR cR Fr`; `indepOfRank_correct
  (hFr : ∀ S, Fr (a, indicator S) = rk N S) A : indepOfRankV Fr (a, A) =
  decide (N.Indep ↑(univ.filter fun i => A i = true))`, so `indepOfRank_correct hFr` is a
  hypothesis `hFo` for `Fo = indepOfRankV Fr`.  `circuitOracleB_impl C`, `circuitOracle_correct hC`
  (`C : Circuit BoolOp (p + m)`, value `indepOfRankV (rankQueryV C)`).
* Circuits (context = input): `miCircuit_spec hO blk r₀`, `avGuardCircuit_spec hO blk r₀`,
  `nuCircuit_spec hO blk` (sizes, numbers of outputs, outputs at every good input `x`);
  `rankMICircuit_spec C blk r₀`.
* Helpers: `impl_ite` (a static choice between two implementations, cost `if p then c₁ else c₂`),
  `exists_ite_eq_true`, `sum_offDiag`, `numR_bitsR`, `filter_indicator`.

### 6.3 For the observer (P6c, phase 2)

The observer's context `ctxR m`, its builder `ctxB M C` and its oracle `oracleB C` plug in
directly; `oracle_correct hE ht` is a hypothesis `hFo` at the context `ctxV M (relBits (Gt v t))`.
Compiled (against the built `Rainbow/ObserverOracle.lean`, with `open Finset SignedTropical
SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.MI
SignedTropical.Rainbow.Observer SignedTropical.Rainbow.POSL`):

```lean
example (hB : ∀ S : Finset (Fin m),
    (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    Impl (relR m) (vecR (n := n) k) (seqB (ctxB M C) (avGuardB (oracleB C) blk r₀))
      (ctxCost m C.size + (miCost m k (oracleCost m C.size) r₀ + k))
      (fun R b => (miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M R)).2.2.1 &&
        (miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M R)).2.2.2 b) :=
  (ctxB_impl hB).comp (avGuardB_impl (oracleB_impl hB) blk r₀)

open Classical in
example (hE : M.E = Set.univ) {v : Fin m → ℝ} {t : ℝ} (ht : 0 ≤ t) (b : Fin k) :
    ((miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M (relBits (Gt v t)))).2.2.1 &&
      (miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M (relBits (Gt v t)))).2.2.2 b) =
      (decide (nu (NG M (Gt v t)) blk ≤ r₀) && decide (b ∈ Av (NG M (Gt v t)) blk)) :=
  avGuardV_eq (fun A => oracle_correct hE ht A) r₀ b
```

The size is then `ctxCost m s + miCost m k (oracleCost m s) r₀ + k`, bounded with
`miCost_add_le` and `oracleCost_le`: `(k + 1)(m + 1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 +
5⌈log₂(r₀+1)⌉ = O(km³(s + m))`.  For `F_b(E × E) = 0`: `avGuardV_eq` with `oracle_univ` gives
`[ν(M) ≤ r₀] ∧ …`, and `ν(M) = k > r₀` when `M` has a rainbow base.  `vecCircuit_spec` (P6a)
turns the composite into a circuit.

### 6.4 For rank circuits by matroid intersection (transversal matroids)

Take the input bits as the context (`Rc = vecR n`), a matroid `N x` on `Fin m` for every input
`x` (for a transversal matroid: the edges of the bipartite graph as `Fin m`, the blocks `blk` the
sets of the family, `N x` the partition matroid that allows one edge per element of the input set
`x` and none at other elements), and an oracle gadget `hO` for it.  Then `nuCircuit_spec hO blk`
gives a circuit of `k · roundCost m cO + popCost m` gates whose outputs are the binary digits of
`ν(N x)` at every input `x` where the oracle is correct.  Compiled:

```lean
open Classical in
example {n m k cO : ℕ} {bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : (Fin n → Bool) × (Fin m → Bool) → Bool}
    (hO : Impl ((vecR n).prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k)
    (N : (Fin n → Bool) → Matroid (Fin m)) (good : (Fin n → Bool) → Prop)
    (hFo : ∀ x, good x → ∀ A, Fo (x, A) = decide ((N x).Indep ↑(univ.filter fun i => A i = true))) :
    (nuCircuit bO blk).size = k * roundCost m cO + popCost m ∧
      ∀ x, good x → bitsVal ((nuCircuit bO blk).eval boolInterp x) = nu (N x) blk :=
  ⟨(nuCircuit_spec hO blk).1, fun x hx => (nuCircuit_spec hO blk).2.2 x (N x) (hFo x hx)⟩
```

With an oracle from a rank query (`indepOfRankB_impl hR`), compiled:
`⟨avGuardB_impl (indepOfRankB_impl hR) blk r₀, avGuardV_eq (indepOfRank_correct hFr) r₀ b,
miCost_rank_le m k cR r₀⟩` proves the implementation, the values
`[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]` at `a`, and the bound `(k + 1)(m + 1)²(cR + 37(m + 1)) +
5⌈log₂(r₀+1)⌉`.
