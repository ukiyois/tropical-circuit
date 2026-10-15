# P6b: the matroid intersection circuit

Natural-language companion of `SignedTropical/Rainbow/MICircuit.lean`, namespace
`SignedTropical.Rainbow.MI`.  Source: `paper/greedy_intersection.tex`, Lemma `lem:augment`, used
in Lemma `lem:observer`, Step 4, and in Corollary `cor:transversal`; Lemma `lem:avoidable` for
`Av`.  The module uses the augmenting path algorithm of `Rainbow/Exchange.lean` (`Arc`,
`IsSource`, `IsSink`, `reachSet`, `augStep`, `iterate_augStep`, `card_iterate_augStep`, `nu_le`,
`av_eq`) and the Boolean library of `BoolAlg/*.lean` (`Impl` and its combinators,
`exchangeB_impl`, `augStep_bits`, `layerV_iff_mem_reachSet`, `bfsStepB_impl`,
`vecPopcountB_impl`, `numLeConstB_impl`, `vecCircuit_spec`, `circuitOf_num`).

Build: no error, no warning, no `sorry`; the theorems depend on `propext`, `Classical.choice`
and `Quot.sound` only.

Conventions.  `E = Fin m`; `blk : Fin m → Fin k`, block `b` is `blk⁻¹(b)`; `N` is a matroid on
`Fin m`.  A set is carried by its bits `A : Fin m → Bool`; `1_J` is `indicator J`.
`I - v + u = (I \ {v}) ∪ {u}`, `I + y = I ∪ {y}`, `W = ⌈log₂(m+1)⌉ = Nat.size m`.  Gate counts
are exact: `Impl R₁ R₂ b c F` says that the builder `b` appends exactly `c` gates and that its
result carries `F` of what its argument carries.

**Context and exchange tests.**  The circuit reads a *context* carried by a representation
`Rc : Rep BoolOp Bool n σ τ`, whose value `a : τ` depends on the input of the whole circuit (the
input bits, or data computed from them once, as in the observer).  For each `y` an *exchange
test* `hO y : Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y)` computes a bit `Fo y (a, A)` from
the context and the bits of a set, with `cO` gates.  The circuit uses the test of `y` only on
`I - v + y` (the arc `y → v`, masked unless `y ∉ I` and `v ∈ I`) and on `I + y` (the sink `y`,
masked unless `y ∉ I`), at independent `I`.  `ExchOracle Fo N a` says that the tests answer
these questions in `N` at `a`:

  for every `y` and `A ∋ y` with `A - y` independent in `N`, `Fo y (a, 1_A) = [A independent in N]`.

An independence oracle answers all of them (`ExchOracle.of_indep`).


## 1. Results

### 1.1 The values

**Definition 1.**  For tests `Fo`, blocks `blk`, a context `a` and bits `I`, `R`:

* `exchV I u v`, the bits of `I - v + u`; `addV I y`, the bits of `I + y`;
  `exchV_indicator`: `exchV 1_J u v = 1_{J - v + u}` for `u ≠ v`; `addV_indicator`;
* `arcV Fo blk a I u v`: `false` if `u = v`, and otherwise
  `(¬I u ∧ I v ∧ Fo u (a, I - v + u)) ∨ (β ∧ ¬I v)` with `β = I u` if `blk v = blk u` and
  `β = false` otherwise;
* `srcV blk I y = ¬∃ x, blk x = blk y ∧ I x`; `sinkV Fo a I y = ¬I y ∧ Fo y (a, I + y)`;
* `roundV Fo blk a I = I ⊕ pathV (arcV …) (srcV …) (sinkV …)`, `pathV` the least-index shortest
  path from the sources to the sinks (`BoolAlg/Path.lean`);
* `stateV Fo blk j a = (roundV Fo blk a)^j(∅)`;
* `reachV Fo blk a I = layerV (arcV Fo blk a I) (srcV blk I) m`;
* `avV blk I R b = (¬∃ x, blk x = b ∧ I x) ∨ (∃ x, blk x = b ∧ I x ∧ R x)`;
* `miV Fo blk j r₀ a = (I, |I|, [|I| ≤ r₀], avV blk I (reachV Fo blk a I))`, `I = stateV Fo blk j a`.

### 1.2 Correctness

**Theorem 2 (`lem:augment`, Steps 1 to 3).**  Let `ExchOracle Fo N a`.

1. For `J` independent in `N`: `arcV_iff`, `arcV Fo blk a 1_J u v ↔ Arc N blk J u v`;
   `srcV_iff`, `srcV blk 1_J y ↔ IsSource blk J y`; `sinkV_iff`,
   `sinkV Fo a 1_J y ↔ IsSink N J y`; `roundV_indicator`,
   `roundV Fo blk a 1_J = 1_{augStep N blk J}`; `reachV_iff`, `reachV Fo blk a 1_J v ↔
   v ∈ reachSet N blk J`.
2. `stateV_eq`: `stateV Fo blk j a = 1_{augStep^j(∅)}` for every `j`.
3. `avV_eq`: for `J` rainbow independent with `|J| = ν(N)`, the bits computed from `J` and its
   reachable set are `[b ∈ Av(N)]`.
4. `miV_spec`: for `r₀ < j`, the guard is `[ν(N) ≤ r₀]`, and when `ν(N) ≤ r₀` the last output is
   `b ↦ [b ∈ Av(N)]`.

*Proof.*  Step 1, the arcs.  For `u = v` both sides are false.  For `u ≠ v`, `u ∈ J`, the first
term is masked and the second is `v ∉ J ∧ blk v = blk u`.  For `u ∉ J`, `v ∈ J`, the bits of
`exchV 1_J u v` are those of `J - v + u`, which contains `u`, and `(J - v + u) - u = J - v ⊆ J` is
independent, so `ExchOracle` gives `Fo u (a, ·) = [J - v + u independent]`.  For `u ∉ J`,
`v ∉ J`, both sides are false.

Step 2, the sinks.  For `y ∉ J`, the bits of `addV 1_J y` are those of `J + y`, and
`(J + y) - y = J` is independent; for `y ∈ J` both sides are false.

Step 3, a round: `augStep_bits` with Steps 1 and 2.

Step 4, `j` rounds, by induction: the state after `i` rounds is `1_{augStep^i(∅)}`, which is
rainbow independent (`iterate_augStep`), so Step 3 applies to the next round.

Step 5, the reachable set: `layerV_iff_mem_reachSet` with Step 1.  The avoidable blocks:
`av_eq`, `Av(N) = {b missed by J} ∪ blk(J ∩ R)`.

Step 6, `miV_spec`.  By `iterate_augStep` the state `I` after `j` rounds has
`min(j, ν(N)) ≤ |I| ≤ ν(N)`.  If `ν(N) ≤ r₀ < j`, then `|I| = ν(N) ≤ r₀`, and Step 5 gives the
bits.  If `ν(N) > r₀`, then `|I| ≥ min(j, ν(N)) ≥ r₀ + 1`.  So `[|I| ≤ r₀] = [ν(N) ≤ r₀]`.

### 1.3 The gadgets and their gate counts

**Theorem 3.**  With exchange tests of `cO` gates, each builder implements the stated value with
exactly the stated number of gates.

| builder | reads | value | gates | Lean |
| :-- | :-- | :-- | :-- | :-- |
| `prepB` | `(a, I)` | `(a, I, ¬I, true)` | `m + 1` | `prepB_impl` |
| `arcB bO blk u v` | `(a, I, ¬I, true)` | the arc test `u → v`, by the test of `u` | `cO + 4` | `arcB_impl` |
| `arcsB bO blk` | `(a, I, ¬I, true)` | `arcV` at every pair | `m(m-1)(cO + 4)` | `arcsB_impl` |
| `srcsB blk` | `(a, I, ¬I, true)` | `srcV blk I` | `m(m + 1)` | `srcsB_impl` |
| `sinksB bO` | `(a, I, ¬I, true)` | `sinkV Fo a I`, by the test of `y` | `m(cO + 1)` | `sinksB_impl` |
| `roundB bO blk` | `(a, I)` | `roundV Fo blk a I` | `roundCost m cO` | `roundB_impl` |
| `roundsB bO blk j` | `a` | `(a, stateV Fo blk j a)` | `j · roundCost m cO` | `roundsB_impl` |
| `reachB bO blk` | `(a, I)` | `reachV Fo blk a I` | `m(m-1)(cO + 4) + 2m³ + m² + 2m + 1` | `reachB_impl` |
| `avB blk` | `(I, R)` | `avV blk I R` | `m + k(2m + 2)` | `avB_impl` |
| `nuGuardB r₀` | `I` | `(|I|, [|I| ≤ r₀])` | `popCost m + 5 max(W, ⌈log₂(r₀+1)⌉) + 2` | `nuGuardB_impl` |
| `miB bO blk j r₀` | `a` | `miV Fo blk j r₀ a` | `miCost m k j cO r₀` | `miB_impl` |

Here `roundCost m cO = m²cO + 8m³ + 12m² + 12m + 4` (`roundCost_eq`: `m(m-1) + m = m²` tests) and
`miCost m k j cO r₀ = j · roundCost m cO + m(m-1)(cO + 4) + 2m³ + m² + 3m + 2k(m + 1) + popCost m +
5 max(W, ⌈log₂(r₀+1)⌉) + 3`.  The test of `I - v + u` reads the operands of `I` with entry `u`
set to the shared `true` and entry `v` to the constant `false`, a free rearrangement; the masks
and the diagonal are static choices (`impl_ite`, `exists_ite_eq_true`, `sum_offDiag`).

**Theorem 4 (the size).**  `miCost_add_le`:
`miCost m k j cO r₀ + k ≤ (j + 1)(m + 1)²(cO + 10(m + 1)) + 3k(m + 1) + 5⌈log₂(r₀+1)⌉`.

*Proof.*  `m(m-1)(cO + 4) ≤ m²(cO + 4)`, `popCost m ≤ 22m`, `max(W, ⌈log₂(r₀+1)⌉) ≤ m +
⌈log₂(r₀+1)⌉`, `2k(m + 1) + k ≤ 3k(m + 1)`, and a comparison of coefficients (`nlinarith`).

### 1.4 The observer's bits and `ν` alone

**Theorem 5.**

1. `avGuardB_impl`: `avGuardB bO blk j r₀` computes the `k` bits `[|I| ≤ r₀] ∧ avV …` from the
   context with `miCost m k j cO r₀ + k` gates; `avGuardV_eq`: for `r₀ < j`, at a context where
   `ExchOracle Fo N a`, bit `b` is `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`.
2. `avGuardCircuit_spec` (**Lemma `lem:augment`, the bits**): with the context the input,
   `avGuardCircuit bO blk r₀` runs `r₀ + 1` rounds, has `miCost m k (r₀ + 1) cO r₀ + k` gates and
   `k` outputs, and at every input `x` with `ExchOracle Fo N x` outputs
   `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`, `b < k`.
3. `nuB_impl`, `card_stateV`, `nuCircuit_spec` (**Lemma `lem:augment`, `ν`**): `k` rounds and a
   population count, `k · roundCost m cO + popCost m` gates and `W` outputs; at every input with
   `ExchOracle Fo N x` the outputs are the binary digits of `ν(N)` (`card_iterate_augStep`,
   `ν(N) ≤ k`).

*Proof.*  Item 1 composes `miB_impl` with `vecMaskB_impl` (`k` gates); the values come from
`miV_spec`.  Items 2 and 3: `vecCircuit_spec`, `circuitOf_num` on the implementations from the
input operands.


## 2. Correspondence table

| paper | Lean | status |
| :-- | :-- | :-- |
| `lem:augment`, hypothesis: a test for each `y`, deciding independence of `J ∋ y` with `J - y` independent | `ExchOracle`, `ExchOracle.of_indep` | proved |
| Step 1, one round: `m²` tests, used answers only at `y ∉ I` (and `x' ∈ I`), each on a set whose part without `y` is independent | `arcV`, `sinkV`, `arcV_iff`, `sinkV_iff`, `srcV_iff`, `roundV_indicator`, `roundB_impl`, `roundCost` | proved |
| Step 2, `j` rounds give at least `min(j, ν)` elements; `k` rounds give `ν` | `stateV`, `stateV_eq`, `roundsB_impl`, `iterate_augStep`, `card_iterate_augStep` | proved |
| Step 3, `r₀ + 1` rounds, one more exchange graph, `Av`, the guard | `reachV_iff`, `avV_eq`, `miV_spec`, `miB_impl`, `avGuardB_impl`, `avGuardV_eq` | proved |
| the size `(r₀+2)(m+1)²(q+10(m+1)) + 3k(m+1) + 5⌈log₂(r₀+1)⌉` | `miCost`, `miCost_add_le` | proved |
| the two circuits of the lemma | `avGuardCircuit_spec`, `nuCircuit_spec` | proved |


## 3. Differences from the paper

1. Correctness is pointwise in the context: the outputs are correct at every input at which the
   tests answer the exchange questions of the intended matroid.  This is the form the paper
   uses.
2. Every ordered pair `u ≠ v` gets a test of `I - v + u` and every `y` a test of `I + y`, since
   which of them are used depends on `I`; the unused answers are masked.  The paper counts the
   same `m²` tests per round.
3. The ground set of `N` is unrestricted.


## 4. Line count

`MICircuit.lean`: 677 lines.
