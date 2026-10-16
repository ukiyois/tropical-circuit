# Phase 1, formalized: greedy without branching

Natural-language companion of the Lean package `SignedTropical`
(`D:\Dsektop\daishu\daishu-formal`, tracked in the git repository `daishu`; Lean `v4.32.0`,
Mathlib `v4.32.0`).

Sources: `daishu/docs/research-direction-2026-10-11.md`, Section 3.2 (Theorems A and B,
Corollaries C to F); `daishu/paper/signed_assignment.tex`, Section `sec:amplitude`
(Definition `def:filtration`, Proposition `prop:two-readings`, Lemmas `lem:bit` and
`lem:lift`, Theorem `thm:compiler`, Corollary `cor:integer-observable`, Proposition
`prop:sugeno`, Theorem `thm:lattice`, Theorem `thm:equivalence`);
`daishu/paper/greedy_intersection.tex`, Sections 2 and 3.

The research document gives sketches.  This file is the authoritative natural-language
version of what is proved: every definition and result below is the reading of the Lean
declaration named next to it, with the same hypotheses, the same conclusion and the same
constants.  Where the Lean statement is stronger than the research document or the papers,
this file states the Lean version and Section 4 records the difference.  Proofs follow the
Lean proofs step by step.

**Build status.**  `lake build` succeeds with no warning.  The development contains no
`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern`.  Every theorem in
the table of Section 3 depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound` (checked with `#print axioms`).  Concrete instances are checked by the kernel
with `decide +kernel` (Section 5).

Notation.  `E = {0, …, m-1}` (Lean `Fin m`).  For `S ⊆ E`, `1_S ∈ {0,1}^E` is its
indicator vector, read as bits (`indicator S`) or as reals (`fun e => if e ∈ S then 1 else
0`).  `⌈log₂(x+1)⌉` is the number of binary digits of `x ∈ ℕ` (Lean `Nat.size x`).


## 1. Definitions

### 1.1 Circuits (`Circuit.lean`, `Models.lean`)

**Definition 1.1 (circuit).**  Fix a set `Op` of operations and a number `n` of inputs.
An *operand* is an input coordinate `i < n`, the *constant source*, or a *wire* `j ∈ ℕ`.  A
*gate* is an operation together with two operands; a unary operation ignores its second
operand.  A *circuit* is a finite list of gates `g₀, …, g_{s-1}` together with a finite list
of output operands.  Gate `k` produces wire `k`.  (`Arg`, `Gate`, `Circuit`.)

**Definition 1.2 (size).**  The size of a circuit is the number of its gates,
`size(C) = s`.  Inputs and the constant are operands, not gates, and cost nothing.
(`Circuit.size`.)

**Definition 1.3 (reading, evaluation).**  A *reading* of `Op` in a carrier `α` is a value
`z ∈ α` for the constant source and a map `op_o : α × α → α` for each `o ∈ Op`.  At an input
`x ∈ α^n` the wire values are computed in order,
`v_k = op_{o_k}(read(a_k), read(b_k))` for `g_k = (o_k, a_k, b_k)`, where
`read(input i) = x_i`, `read(const) = z`, `read(wire j) = v_j` if `j < k`, and
`read(wire j) = z` if `j ≥ k`.  The *outputs* of `C` at `x` are the list of the values read
at the output operands, with all wires built.  (`Interp`, `Arg.read`, `wires`,
`Circuit.eval`.)

A reference to a wire `j ≥ k` reads the constant.  Replacing such an operand by the
constant source gives a circuit with the same size and the same values, so for the gate
sets below that have a constant source this convention adds nothing.  Lattice circuits have
no constant and are restricted by Definition 1.9.

**Definition 1.4 (gate sets).**

| gate set | operations | constant source | Lean |
|---|---|---|---|
| signed tropical | `max(a,b)`, `a + b`, `a - b` | `0` | `STOp`, `stInterp ℝ` (also over `ℤ`) |
| Boolean | `a ∧ b`, `a ∨ b`, `¬a` | `false` | `BoolOp`, `boolInterp` |
| lattice | `min(a,b)`, `max(a,b)` | none (Definition 1.9) | `LatOp`, `latInterp α z` |
| subtraction-free | `min(a,b)`, `a + b`, `max(a,b)` | `0` | `TropOp`, `tropInterp` |

Read over `Bool` (with `false < true`), `min` is `∧` and `max` is `∨` (`min_bool`,
`max_bool`), so lattice circuits read over `Bool` are the monotone Boolean circuits.

**Definition 1.5 (computes).**  A circuit `C` on `n` inputs *computes* `f : X → α` on a set
`X ⊆ α^n` if its output list at every `x ∈ X` is the one-element list `[f(x)]`.  A circuit
computes a vector `(f₁, …, f_N)` if its output list is `[f₁(x), …, f_N(x)]`.

**Definition 1.6 (binary output).**  For a list of bits `b₀, b₁, …` (least significant
first), `bitsVal(b) = ∑_j 2^j b_j` (`bitsVal`).  A Boolean circuit `B` on `m` inputs
*outputs `f(S)` in binary* if `bitsVal(B(1_S)) = f(S)` for every `S ⊆ E`.  Any number of
output bits is allowed.

### 1.2 The threshold integral (`GapSum.lean`)

**Definition 1.7 (sorted values, threshold sets, gap sum).**  For `D ∈ ℝ^E`:

* `s₀ = 0` and `s₁ ≤ ⋯ ≤ s_m` are the entries of `D` in increasing order (insertion sort of
  `D₀, …, D_{m-1}`) (`sortedVals`, `sortedVal D k`);
* `Δ_k = s_{k+1} - s_k` and `G_k = {e : D_e ≤ s_k}` for `k < m` (`threshSet D k`);
* for `F : 2^E → ℝ`, the *threshold integral* is the gap sum
  `C_F(D) = ∑_{k<m} Δ_k F(G_k)` (`gapSum F D`).

### 1.3 Matroids (`Matroid.lean`)

**Definition 1.8.**  A matroid on `E` is a Mathlib `Matroid (Fin m)` whose ground set is
`Set.univ`.  For `S ⊆ E`, `r(S) = M.eRk S` (an element of `ℕ ∪ {∞}`, finite here) and
`rk M S ∈ ℕ` is its value (`rk`, `coe_rk`).  The rank is `k = r(E)` (`rank M`).  For
`w ∈ ℝ^E` the basis weights are `{w(B) : B a basis}` with `w(B) = ∑_{e∈B} w_e`
(`basisWeights`), and `h_M(w) = max_B w(B)` is their supremum (`maxBasisWeight`), which is
the greatest basis weight (`isGreatest_maxBasisWeight`).

### 1.4 Monotone observables (`Lattice.lean`)

**Definition 1.9.**

* `g : 2^E → {0,1}` is *monotone* if `S ⊆ T` and `g(S) = 1` imply `g(T) = 1`
  (`MonotoneObs`).
* `Λ_g(D) = max_{A : g(A) = 1} min_{e∈A} D_e`, with the maximum over the empty family equal to
  `0` (`sugeno`, defined with `iSup`/`iInf` in `ℝ`).  The minimum over `A = ∅` would also be
  `0` in `ℝ`; every result below assumes `g(∅) = 0`, so `A = ∅` never occurs.
* A *lattice circuit* is a circuit over `{min, max}` in which every operand of gate `k` is an
  input or a wire `j < k`, and every output is an input or a wire `j < size`: no constant and
  no reference to a wire not yet built (`Circuit.IsLattice`).
* `C` *computes `h` as a lattice circuit* if, read over `ℝ` with `min`, `max`, it computes
  `h` on `ℝ^E_{≥0}` (`LatComputes`); `C` *computes `g` monotonically* if, read over `Bool`,
  it computes `g` from indicator vectors (`MonComputes`).
* `Lat(h)` and `LatDepth(h)` (`latSize`, `latDepth`) are the least size and depth of a
  lattice circuit computing `h` as a lattice circuit; `Mon(g)` and `MonDepth(g)`
  (`monSize`, `monDepth`) are the least size and depth of a lattice circuit computing `g`
  monotonically.  The depth of a circuit is the length of a longest path from a source to
  an output, computed by reading every gate as `1 + max` (`Circuit.depth`).

### 1.5 Further definitions

* `Size_{min,+,max}(h)`: the least size of a `(min, +, max)` circuit computing `h` on `ℝ^E`
  (`tropSize`, `Subtractionfree.lean`).
* `min_B w(B)` (`minBasisWeight`) and the spanning predicate `Span_M(S) = [r(S) = k]`
  (`spanning`).
* The rank thresholds `g_u(S) = [u ≤ r(S)]` (`rankThreshold M u`).
* The binary matroid of `A ∈ GF(2)^{r×m}` (`binaryMatroid A`, `Binary.lean`): ground set
  `E`, and `I ⊆ E` independent iff the columns `A_e`, `e ∈ I`, are linearly independent over
  `GF(2)` as a family (`binaryMatroid_indep`).
* The base polytope `B(M) = conv{1_B : B a basis}` (`basePolytope`) and the support function
  `σ_P(w) = sup_{x∈P} ⟨w, x⟩` (`supportFn`, `Polytope.lean`).


## 2. Results

### 2.1 Homomorphism lemma (`wires_map`, `Circuit.eval_map`; relative forms `wires_map_of`, `Circuit.eval_map_of`)

**Lemma 2.1.**  Let `I` be a reading in `α`, `J` a reading in `β`, and `φ : α → β` with
`φ(z_I) = z_J` and `φ(op^I_o(a,b)) = op^J_o(φa, φb)` for all `o, a, b`.  Then for every gate
list and every input `x`, the wire values of `J` at `φ∘x` are the images under `φ` of the
wire values of `I` at `x`, and the same holds for the outputs.  In the relative form the
commutation is required only for `a, b` satisfying a predicate `P` that holds at `z_I`, at
every input coordinate and at every wire value of `I` at `x`.

*Proof.*  Induction on the number of gates.
1. With no gates both wire lists are empty.
2. Append a gate `(o, a, b)`.  By induction the earlier wire lists correspond under `φ`.
3. Each operand reads corresponding values: an input by definition, the constant because
   `φ(z_I) = z_J`, a wire because the earlier lists correspond (an index out of range reads
   `z_I` and `z_J`).  In the relative form the values read on the `I` side satisfy `P`,
   being inputs, `z_I` or earlier wires.
4. The new wire: `op^J_o(φ read a, φ read b) = φ(op^I_o(read a, read b))`.  ∎

### 2.2 Builders and inlining (`Den`, `inline_spec`, `length_inline`)

All circuits are built by appending gates.  `Den I gs a f` states that operand `a` is valid
in the gate list `gs` and carries `f(x)` at every input `x`; it is preserved by appending
gates (`Den.mono`), and appending `(o, a, b)` to a list where `a, b` denote `f, g` produces a
wire denoting `op_o(f, g)` (`den_emit`).

**Lemma 2.2 (inlining).**  Let `C` be a circuit over `Op` on `n'` inputs and, for each
`o ∈ Op`, let `gad_o` be a builder over `Op'` that, given representations of `a` and `b`,
appends gates and returns a representation of `op^{J(x)}_o(a, b)` for a reading `J(x)` of
`Op` (which may depend on the outer input `x`).  Represent input `i` of `C` by `ρ_i`
carrying `φ_i(x)` and the constant by a representation of `z_{J(x)}`.  Then appending the
gadgets of the gates of `C` in order returns representations of the outputs of `C` read
through `J(x)` at the inputs `φ_i(x)`; if `gad_o` appends `cost(o)` gates, the inlined
circuit has `∑_k cost(o_k)` gates.

*Proof.*  Induction over the gates of `C`, carrying the representations of the wires built
so far (`inlineGates_spec`).  Each operand of `C` is translated to an input
representation, the constant representation, or an earlier wire representation; a wire
index out of range translates to the constant, as it reads on the source side
(`tr_spec`).  The gadget hypothesis gives the new wire.  The gate count adds up gate by
gate.  ∎

### 2.3 The sorting network (`Sorting.lean`: `isortV_eq_insertionSort`, `isortB_spec`)

**Lemma 2.3.**  Let `ins(a, []) = [a]`, `ins(a, b :: l) = min(a,b) :: ins(max(a,b), l)` and
`isort([]) = []`, `isort(a :: l) = ins(a, isort(l))`.  Then `isort` equals Mathlib's
`List.insertionSort`.  As a signed tropical builder, with each comparator realized as
`max(a,b)`, `a + b`, `min(a,b) = (a+b) - max(a,b)` (three gates), it has
`3 ∑_{i<m} i = 3 m(m-1)/2` gates on a list of length `m` and outputs the list sorted in
increasing order.

*Proof.*
1. If `l` is sorted and `a ≤` every entry of `l`, then `ins(a, l) = a :: l` (induction on
   `l`).
2. If `l` is sorted, `ins(a, l)` is the ordered insertion of `a` into `l`: for `a ≤ b`,
   `ins(a, b :: l) = a :: ins(b, l) = a :: b :: l` by Step 1; for `a > b`,
   `ins(a, b :: l) = b :: ins(a, l)` and induction.
3. `isort = insertionSort` by induction, since `isort(l)` is sorted (Mathlib's
   `pairwise_insertionSort`).
4. The builder: `min(a,b) + max(a,b) = a + b` gives the comparator; the gate count is
   `3 · (number of comparators)`, with `k` comparators to insert into a list of length
   `k`.  ∎

### 2.4 Lemma `lem:bit` (`bit_identity`, `le_or_succ_le`, `sub_min_eq_max`)

**Lemma 2.4.**  Let `D ∈ ℝ^E_{≥0}`, `e ∈ E` and `k < m`.  Then
`Δ_k - min(max(D_e - s_k, 0), Δ_k) = Δ_k · 1[e ∈ G_k]`.  Moreover
`Δ - min(t, Δ) = max(Δ - t, 0)` for all reals, so the left side equals
`max(Δ_k - max(D_e - s_k, 0), 0)`, the form computed by the circuit at four gates.

*Proof.*
1. `s₀ = 0 ≤ s₁` because `D ≥ 0`, so `s₀ ≤ s₁ ≤ ⋯ ≤ s_m` (`sortedVal_mono`).
2. `D_e = s_j` for some `1 ≤ j ≤ m` (`exists_sortedVal_eq`).  If `j ≤ k` then `D_e ≤ s_k`;
   otherwise `j ≥ k+1` and `D_e ≥ s_{k+1}` (`le_or_succ_le`).
3. If `D_e ≤ s_k`, the inner maximum is `0` and both sides are `Δ_k`.
4. If `D_e ≥ s_{k+1}` and `D_e > s_k`, then `D_e - s_k ≥ Δ_k`, the minimum is `Δ_k`, and both
   sides are `0`.  If `D_e ≥ s_{k+1}` and `D_e ≤ s_k`, then `s_{k+1} = s_k`, `Δ_k = 0`, and
   both sides are `0`.  ∎

### 2.5 Layer cake (`sum_gap_lt`, `eq_sum_gap`, `sum_eq_gapSum_card`)

**Lemma 2.5.**  Let `D ∈ ℝ^E_{≥0}`.
1. For `j ≤ m`: `∑_{k<m} Δ_k [s_k < s_j] = s_j`.
2. For every `e`: `D_e = ∑_{k<m} Δ_k [s_k < D_e]`.
3. For every `I ⊆ E`: `∑_{e∈I} D_e = C_F(D)` with `F(S) = |I \ S|`.

*Proof.*
1. For `k ≥ j` the indicator is `0`, since `s_k ≥ s_j`.  For `k < j`, the term is `Δ_k`: if
   `s_k < s_j` directly, and if `s_k = s_j` then `s_k ≤ s_{k+1} ≤ s_j` forces `Δ_k = 0`.  So
   the sum is `∑_{k<j} Δ_k = s_j - s₀ = s_j` (telescoping).
2. Item 1 with `D_e = s_j` (`exists_sortedVal_eq`).
3. Sum item 2 over `e ∈ I`, exchange the sums, and use
   `|{e ∈ I : s_k < D_e}| = |I \ G_k|`.  ∎

The gap sum is linear in `F` (`gapSum_add`, `gapSum_smul`, `gapSum_finsetSum`) and, on
`D ≥ 0`, monotone in `F` (`gapSum_mono`), since `Δ_k ≥ 0`.

### 2.6 Lemma `lem:lift` (`Lift.lean`: `lift`, `lift_vanish`, `eval_liftInterp`)

Represent a bit `b` at amplitude `Δ` by `ampl_Δ(b) = Δ` if `b`, `0` otherwise (`ampl`), and
read the Boolean gates at amplitude `Δ` as `a ∧ b ↦ max(a + b - Δ, 0)`, `a ∨ b ↦ max(a, b)`,
`¬a ↦ Δ - a`, constant `0` (`liftInterp Δ`).

**Lemma 2.6.**  Let `B` be a Boolean circuit of size `s` on `m` inputs.  The lifted circuit
(`liftCircuit B`, on `m + 1` inputs, input `m` carrying `Δ`) has at most `3s` gates, and for
every `Δ ≥ 0` and every `β ∈ {0,1}^m`, at the input `(Δβ₀, …, Δβ_{m-1}, Δ)` its outputs are
`Δ` times the outputs of `B` at `β`.  If `Δ = 0`, every wire of the lifted circuit carries
`0` (`lift_vanish`).

*Proof.*
1. `ampl_Δ` commutes with the gates for `Δ ≥ 0`, by the eight cases of two bits
   (`ampl_op`); for example `ampl_Δ(1 ∧ 1) = Δ = max(Δ + Δ - Δ, 0)` and
   `ampl_Δ(0 ∧ 0) = 0 = max(-Δ, 0)`.
2. Lemma 2.1 gives the outputs of the reading `liftInterp Δ` (`eval_liftInterp`).
3. Each Boolean gate is replaced by a gadget of `3`, `1` or `1` signed tropical gates
   (`liftGad`, `liftCost`), and Lemma 2.2 shows the lifted circuit computes the reading of
   Step 2; its size is at most `3s` (`liftCost_sum_le`).
4. At `Δ = 0` all inputs are `0`, and a signed tropical circuit with all inputs `0` has all
   wires `0`: Lemma 2.1 for the map from a one-point reading to `0`
   (`wires_eq_zero`).  ∎

### 2.7 Theorem `thm:compiler` (`Compiler.lean`: `thm_compiler`, `compiler_size`)

**Theorem 2.7 (compiler).**  Let `F = (F₁, …, F_N) : 2^E → {0,1}^N` be computed by one
Boolean circuit `B` of size `s` from the indicator vector of its argument
(`B(1_S) = [F₁(S), …, F_N(S)]` for every `S`).  Then a signed tropical circuit of size at
most `3ms + mN + 6m²` computes `(C_{F₁}(D), …, C_{F_N}(D))` at every `D ∈ ℝ^E_{≥0}`.

*Proof.*  The circuit (`compiler B`) is built as follows (`compileB`).
1. Sort `D` (Lemma 2.3): operands for `s₁, …, s_m`; `s₀` is the constant `0`.
2. For each gap `k < m`: one gate for `Δ_k = s_{k+1} - s_k`; four gates per element for
   `max(Δ_k - max(D_e - s_k, 0), 0)` (`bitB`); the lifted `B` at amplitude `Δ_k` on these
   operands (`liftB`, at most `3s` gates); `N` additions into `N` running sums (`gapB`).
3. Value at every `D` (`compileB_spec`): the `u`-th sum is
   `∑_{k<m} [B read at amplitude Δ_k on the membership values]_u` (`compVal`).
4. On `D ≥ 0` (`compVal_eq`, `gapOut_eq`): the membership values are `Δ_k · 1[e ∈ G_k]`
   (Lemma 2.4), so by Lemma 2.6 the lifted outputs are `Δ_k F_u(G_k)`, including the gaps
   with `Δ_k = 0`, where they are `0`; summing over `k` gives `C_{F_u}(D)`.
5. Size (`compileCost_le`): `3 m(m-1)/2 + m(1 + 4m + 3s + N) ≤ 3ms + mN + 6m²`.  ∎

### 2.8 Corollary `cor:integer-observable` (`integer_observable`)

**Corollary 2.8.**  Let `f : 2^E → ℕ` and let a Boolean circuit `B` of size `s` with `L`
outputs output `f(S)` in binary from the indicator vector of `S`.  Then a signed tropical
circuit of size at most `3ms + mL + 6m² + 2L` computes `C_f(D)` at every `D ∈ ℝ^E_{≥0}`.

*Proof.*
1. Theorem 2.7 for the `L` output bits `f_j` gives operands for `c_j = C_{f_j}(D)`.
2. Horner's rule `y = c₀ + (y' + y')`, two gates per bit (`hornerB`), gives
   `∑_j 2^j c_j` (`hornerB_spec`).
3. `∑_j 2^j C_{f_j}(D) = C_{∑_j 2^j f_j}(D) = C_f(D)` by linearity of the gap sum
   (`hornerV_gapSum`, `hornerV_bits`, `hornerV_compVal`).  ∎

### 2.9 Proposition `prop:sugeno` (`gapSum_eq_sugeno`)

**Proposition 2.9.**  Let `g` be monotone with `g(∅) = 0`, and `F(S) = g(E \ S)`.  Then
`C_F(D) = Λ_g(D)` for every `D ∈ ℝ^E_{≥0}`.

*Proof.*
1. If `g(E) = 0` then `g ≡ 0` by monotonicity, both sides are `0` (the empty maximum is
   `0`).
2. Let `g(E) = 1`.  Then `s < Λ_g(D)` iff `g({e : s < D_e}) = 1` (`lt_sugeno_iff`): a set
   attaining the maximum lies in `{s < D}` when its minimum exceeds `s`, and
   `{s < D}` itself is a candidate when `g` holds there (it is nonempty since `g(∅) = 0`, and
   a finite minimum of values above `s` is above `s`).
3. `E \ G_k = {s_k < D}` (`compl_threshSet`), so `F(G_k) = [s_k < Λ_g(D)]`.
4. `Λ_g(D)` is `0 = s₀` or an entry of `D`, hence one of `s₀, …, s_m` (`sugeno_mem`), and
   Lemma 2.5 (item 1) gives `∑_k Δ_k [s_k < Λ_g(D)] = Λ_g(D)`.  ∎

### 2.10 Theorem `thm:lattice` (`thm_lattice`, `latComputes_iff`, `eval_eq_sugeno`)

**Theorem 2.10.**  Let `g` be monotone with `g(∅) = 0` and `g(E) = 1`.
1. If a lattice circuit `C` computes `g` monotonically, then over `ℝ` it computes `Λ_g` at
   every `D ∈ ℝ^E` (`eval_eq_sugeno`).
2. A lattice circuit computes `Λ_g` as a lattice circuit iff it computes `g` monotonically
   (`latComputes_iff`).
3. `Lat(Λ_g) = Mon(g)` and `LatDepth(Λ_g) = MonDepth(g)` (`thm_lattice`).

*Proof.*
1. A lattice circuit reads no constant, so its values do not depend on the value given to the
   constant (`wires_latInterp`).  For every threshold `t`, `x ↦ [t ≤ x]` is monotone, hence
   commutes with `min` and `max`; Lemma 2.1 gives
   `[t ≤ C(D)] = C(1[t ≤ D_e])` over `Bool` (`thr_eval`).
2. Item 1: `C(1[t ≤ D]) = g({t ≤ D})`, and `t ≤ Λ_g(D)` iff `g({t ≤ D}) = 1`
   (`le_sugeno_iff`), so `t ≤ C(D)` iff `t ≤ Λ_g(D)` for every `t`, and the two are equal.
3. Item 2, `⇐`: item 1.  `⇒`: the embedding `0 ↦ 0`, `1 ↦ 1` of `Bool` into `ℝ` is monotone,
   so by Lemma 2.1 `C` over `ℝ` at `1_S` is the image of `C` over `Bool` at `1_S`; and
   `Λ_g(1_S) = g(S)` (`sugeno_indicator`); the embedding is injective.
4. Item 3: by item 2 the two sets of circuits in the definitions of `Lat(Λ_g)` and `Mon(g)`
   are equal, and size and depth are functions of the circuit.  ∎

### 2.11 Greedy as a gap sum (`Matroid.lean`)

**Lemma 2.11 (bases along a chain, `exists_isBase_chain`).**  For sets
`X₀ ⊆ X₁ ⊆ ⋯ ⊆ X_p = E` there is a basis `B` with `B ∩ X_i` a basis of `X_i` for every
`i ≤ p`.

*Proof.*  By induction on `i`, choose `J_i` a basis of `X_i` with `J_{i+1} ∩ X_i = J_i`
(Mathlib's `IsBasis.exists_isBasis_inter_eq_of_superset`).  Then
`J_i ∩ X_j = J_j` for `j ≤ i`, and `B = J_p` is a basis of `M`.  ∎

**Proposition 2.12.**  Let `M` be a matroid on `E` (ground set `E`).
1. (`maxBasisWeight_eq_gapSum`) For every `D ∈ ℝ^E_{≥0}`,
   `h_M(D) = ∑_{k<m} Δ_k r({e : D_e > s_k}) = C_F(D)` with `F(S) = r(E \ S)`.
2. (`maxBasisWeight_add_const`) For every `w ∈ ℝ^E` and `c ∈ ℝ`,
   `h_M(w + c·1) = h_M(w) + c k`.
3. (`maxBasisWeight_indicator`) For every `T ⊆ E`, `h_M(1_T) = r(T)`.

*Proof.*
1. Upper bound: for a basis `B`, `D(B) = C_{|B \ ·|}(D)` (Lemma 2.5, item 3) and
   `|B \ S| ≤ r(E \ S)` (independent subset), so `D(B) ≤ C_F(D)` (`gapSum_mono`).
   Attainment: the sets `E \ G_k = {D > s_k}` form a chain; Lemma 2.11 gives a basis `B`
   with `|B ∩ (E \ G_k)| = r(E \ G_k)` for every `k`, so `D(B) = C_F(D)`.
2. Every basis has `k` elements (`card_base`), so `(w + c·1)(B) = w(B) + ck` for every
   basis.
3. `1_T(B) = |B ∩ T| ≤ r(T)`, with equality for a basis extending a basis of `T`
   (`IsBasis.exists_isBase`).  ∎

### 2.12 Theorem A (`TheoremA.lean`: `theoremA`, `theoremACircuit_correct`, `theoremACircuit_spec`)

**Theorem A (greedy compiled).**  Let `M` be a matroid on `E` with ground set `E`, rank
function `r` and rank `k`, and `L = ⌈log₂(k+1)⌉`.  If a Boolean circuit `B` of size `s`
outputs `r(S)` in binary from the indicator vector of `S`, then a signed tropical circuit of
size at most `3ms + mL + 9m² + 4m + 4L + 1` computes `h_M(w)` at every `w ∈ ℝ^E`.

*Proof.*  The circuit is `theoremACircuit B k`.
1. Normalization: `μ = min_e w_e` by `m - 1` gadgets `min(a,b) = a - max(a - b, 0)` of three
   gates (`minListB`, `minV`); `D_e = w_e - μ ≥ 0` at one gate each.
2. The observable: `F(S) = r(E \ S)`.  Negating the `m` inputs of `B` (`negInputs`, `m`
   gates) and keeping its first `L` outputs (`truncOuts`) gives a Boolean circuit of size
   `s + m` that outputs `F(S)` in binary, because `r ≤ k < 2^L` (`bitsVal_take_of_lt`).
3. Corollary 2.8 on `D` computes `C_F(D) = h_M(D)` (Proposition 2.12, item 1) with at most
   `3m(s + m) + mL + 6m² + 2L` gates.
4. `μk` by doubling along the binary digits of `k`, at most `2L` gates (`mulConstB`).
5. One addition: `μk + h_M(D) = h_M(w)` (Proposition 2.12, item 2).
6. Count: `3m + m + 3m(s+m) + mL + 6m² + 2L + 2L + 1 = 3ms + mL + 9m² + 4m + 4L + 1`.  ∎

### 2.13 Theorem B (`Converse.lean`: `theoremB`, `theoremB_of_forall`, `simulate_eval`)

**Theorem B (simulating back).**  Let `M` be a matroid on `E` with ground set `E`.  If a
signed tropical circuit `C` of size `S` computes `h_M` on `{0,1}^E` (that is,
`C(1_T) = [h_M(1_T)]` for every `T`), then a Boolean circuit of size at most `15S² + 40S`
outputs `r(T)` in binary from the indicator vector of `T`.  (`theoremB_of_forall`: the
same conclusion when `C` computes `h_M` on all of `ℝ^E`.)

*Proof.*  Let `W = S + 2`.  The Boolean circuit is `simulate W C`.
1. Integer values: on inputs in `{-1, 0, 1}`, the wire produced by gate `j` has absolute
   value at most `2^{j+1}` (`abs_wires_getElem_le`), since
   `|max(a,b)| ≤ max(|a|,|b|)` and `|a ± b| ≤ 2 max(|a|,|b|)`; so every wire and every
   output is at most `2^S` in absolute value (`abs_wires_le`, `abs_read_le`).  The reading
   over `ℝ` is the image of the reading over `ℤ` (Lemma 2.1, `eval_intCast`).
2. Two's complement: read the gates in `W`-bit vectors (`bvInterp W`: `+`, `-` modulo
   `2^W`, and `max` through the signed comparison).  For `|a|, |b| ≤ 2^S < 2^{W-1}`, the
   signed comparison of the `W`-bit images of `a` and `b` is the comparison of `a` and `b`
   (`toInt_ofInt_of_abs_le`, `ofInt_op`); Lemma 2.1 in relative form with
   `P(v) = [|v| ≤ 2^S]` gives: the bit-vector reading is the image of the integer reading
   (`wires_bv`).
3. Gadgets (`bvGad`): a ripple-carry adder of full adders of eleven gates (`faB`,
   `rcaB`), `11W` gates for `+`; `x - y = x + ¬y + 1`, `12W + 1` gates; and `max` at
   `15W + 10` gates: the carry out of `x + ¬y + 1`, the signed comparison bit
   `(x_{W-1} ⊕ y_{W-1}) ⊕ carry = ¬[x < y]` (Lean's `BitVec.slt_eq_not_carry`), and the
   selection `(lt ∧ y_i) ∨ (¬lt ∧ x_i)`.  The adder is proved against `BitVec` addition by
   induction along the bits (`rcaV_bitsOf`, from `BitVec.getLsbD_add_add_bool` and
   `BitVec.carry_succ`).
4. Inlining (Lemma 2.2, with each wire represented by `W` operands) gives
   `simulate W C (1_T) = bits of the W-bit output of C at 1_T` (`simulate_eval`), and the
   size is at most `S(15W + 10) = 15S² + 40S` (`simulate_size`).
5. At `1_T`: the integer output is `h_M(1_T) = r(T)` (Proposition 2.12, item 3), with
   `0 ≤ r(T) ≤ 2^S < 2^W`, so the bits are the binary digits of `r(T)`.  ∎

### 2.14 Corollary C for binary matroids (`Binary.lean`)

**Proposition 2.14 (the binary matroid).**  For `A ∈ GF(2)^{r×m}` and `S ⊆ E`, the rank
of `S` in the binary matroid of `A` is `dim span{A_e : e ∈ S}` (`eRk_binaryMatroid`), which
is Mathlib's `Matrix.rank` of the submatrix of the columns in `S`
(`eRk_binaryMatroid_eq_rank`).

*Proof.*  The binary matroid is the column matroid `colMatroid A` of `Elimination.lean` over
`GF(2)`, whose proof holds over every field `K`:
1. Augmentation (`colK_indep_aug`): if `I`, `J` are independent with `|I| < |J|` and every
   `e ∈ J \ I` had `A_e ∈ span(A_I)`, then `span(A_J) ⊆ span(A_I)` and
   `|J| = dim span(A_J) ≤ dim span(A_I) = |I|`.  So the independence system is a matroid
   (Mathlib's `IndepMatroid.ofFinset`).
2. A basis `I` of `S` spans `A_S`: for `e ∈ S \ I`, `I + e` is dependent, so
   `A_e ∈ span(A_I)` (Mathlib's `linearIndepOn_insert`).  Hence
   `r(S) = |I| = dim span(A_I) = dim span(A_S)`.
3. `Matrix.rank` is the dimension of the span of the columns (Mathlib's
   `rank_eq_finrank_span_cols`).  ∎

**Proposition 2.15 (elimination without branching, `elimV`, `card_flagSet_elimV`).**  Keep
`r` slots, each with an occupancy bit `f_p` and a vector `b_p ∈ GF(2)^r`, initially empty.
Process the columns `e = 0, …, m-1` in order, with the input bit `x_e`:
1. `v_i = x_e ∧ A_{i,e}` (`colV`);
2. for `p = 0, …, r-1`: `v_i ← v_i ⊕ ((v_p ∧ f_p) ∧ b_{p,i})` (`redStep`, `reduceV`);
3. `ℓ_p = v_p ∧ ¬(∃ q < p, v_q)` (`leadV`), `f_p ← f_p ∨ ℓ_p`,
   `b_{p,i} ← (ℓ_p ∧ v_i) ∨ (¬ℓ_p ∧ b_{p,i})` (`insertV`).

At `x = 1_S` the number of occupied slots at the end is `dim span{A_e : e ∈ S}`.

*Proof.*  Read over `GF(2)` (`zst`, `zvec`), every step is the corresponding step of the
elimination `elimK` of `Elimination.lean` (`zvec_redStep`, `zvec_reduceV`, `zvec_colV`), and
storing is the same, since a stored vector has leading entry `1` and the scaling of `insertK`
is the identity (`zst_insertV`); hence `zst (elimV A x) = elimK A x` (`zst_elimV`).  For
`elimK`, over every field: invariant after the columns processed so far, with `T` the processed
columns in `S` (`InvK`): (a) every occupied slot `p` holds a vector with `b_{p,p} = 1` and
`b_{p,q} = 0` for `q < p` (`EchelonK`); (b) the occupied vectors span `span{A_e : e ∈ T}`.
1. Reduction: each step subtracts a multiple of an occupied vector, so `v' - v` lies in the
   span of the occupied vectors (`reduceK_sub_mem`); and `v'_p = 0` at every occupied slot
   `p`, because the step at `p` clears coordinate `p` and the later steps at `p' > p` do not
   change it, `b_{p',p}` being `0` (`reduceK_occ`).
2. If `v' = 0`: nothing is stored (`insertK_of_zero`); `A_e ∈ span` when `x_e = 1`, so the
   span is unchanged.
3. If `v' ≠ 0`: then `x_e = 1` (a zero column reduces to zero, `reduceK_zero`); its least
   nonzero position `q` is empty by step 1, `ℓ_p = [p = q]` (`leadV_eq`), the new vector,
   scaled to a leading `1`, sits at `q` (invariant a), and
   `span(occupied ∪ {v'}) = span(occupied ∪ {A_e}) = span{A_e : e ∈ T + e}`
   (`span_insert_congrK`, `span_insert_smul`) (invariant b) (`colStepK_inv`).
4. Echelon vectors are linearly independent: in a vanishing combination, the least index
   with a nonzero coefficient has coordinate equal to that coefficient
   (`linearIndepOn_of_echelonK`).  So the number of occupied slots is the dimension
   (`card_occ_elimK`, `card_flagSet_elimV`).  ∎

**Proposition 2.16 (the rank circuit, `binaryRankCircuit_spec`, `binaryRankCircuit_rank`).**
For `A ∈ GF(2)^{r×m}`, the Boolean circuit `binaryRankCircuit A` has exactly
`m(9r² + 5r) + 11 r ⌈log₂(r+1)⌉` gates and outputs `r(S)` (the rank in the binary matroid
of `A`) in binary from the indicator vector of `S`.

*Proof.*
1. Per column (`colStepB`, `9r² + 5r` gates): the masked column costs nothing (input `e`
   where `A_{i,e} = 1`, the constant elsewhere); reduction `r(1 + 5r)`; the bits `ℓ_p`,
   each a disjunction of `r` masked entries, a negation and a conjunction, `r(r + 2)`; the
   occupancy bits `r`; the stored vectors `r(1 + 3r)`.  Each builder is proved to compute the
   corresponding step of Proposition 2.15 (`redB_spec`, `leadB_spec`, `updB_spec`,
   `colStepB_spec`, `elimB_spec`).
2. The count: `r` ripple-carry increments of `⌈log₂(r+1)⌉` bits, `11` gates per bit
   (`countB_spec`), give the number of occupied slots, which is less than `2^{⌈log₂(r+1)⌉}`.
3. Propositions 2.15 and 2.14.  ∎

**Corollary C (binary matroids, `corollaryC_binary`, `corollaryC_binary_poly`).**  For every
`A ∈ GF(2)^{r×m}`, with `k` the rank of its binary matroid and
`s = m(9r² + 5r) + 11 r ⌈log₂(r+1)⌉`, a signed tropical circuit of size at most
`3ms + m⌈log₂(k+1)⌉ + 9m² + 4m + 4⌈log₂(k+1)⌉ + 1` computes `h_M` at every `w ∈ ℝ^E`;
in particular one of size at most `100(m+1)²(r+1)²`.

*Proof.*  Theorem A with Proposition 2.16; for the polynomial bound, `k ≤ r`
(`rank_binaryMatroid_le`) and `⌈log₂(x+1)⌉ ≤ x`.  ∎

### 2.15 Corollary D (`Counting.lean`: `corollaryD_count`, `corollaryD`)

Let `codeCount(m, s, L) = (s+1)(3(m+s+1)²)^s (m+s+1)^L`.

**Lemma 2.17 (counting, `ncard_computed_le`).**  The set of functions `f : 2^E → ℕ` with
`f(S) < 2^L` for all `S` that are output in binary by some Boolean circuit of size at most
`s` has at most `codeCount(m, s, L)` elements.

*Proof.*
1. Codes (`Code`, `decode`): a number of gates `≤ s`, `s` gate codes (an operation and two
   operand symbols out of `m + 1 + s`: inputs, the constant, wires `< s`), and `L` output
   symbols.  There are `codeCount(m, s, L)` codes (`card_code`).
2. Every circuit `B` of size `≤ s` whose values are below `2^L` has a code with the same
   values (`exists_code`): renumbering keeps every wire value, since an operand that refers
   to a wire `j ≥ s ≥ size(B)` reads the constant in `B` as well (`wires_normArg`); cutting
   or padding the outputs to `L` bits keeps the value below `2^L`
   (`bitsVal_ofFn_getD`).  ∎

**Corollary D, counting form (`corollaryD_count`).**  At most
`codeCount(m, 15S² + 40S, ⌈log₂(m+1)⌉)` matroids on `E` (ground set `E`) have a signed
tropical circuit of size at most `S` that computes `h_M` on `{0,1}^E`.

*Proof.*  Map such a matroid to its rank function `T ↦ rk M T`.  This is injective
(`eq_of_eRk_eq`: independence of finite sets is determined by the rank function).  By
Theorem B the rank function is output in binary by a Boolean circuit of size at most
`15S² + 40S`, and its values are below `2^{⌈log₂(m+1)⌉}` since `r(T) ≤ |T| ≤ m`
(`rk_lt_two_pow_size`).  Lemma 2.17 bounds the image.  ∎

**Corollary D (`corollaryD`).**  Let `N` be at most the number of matroids on `E`
(hypothesis `hN`).  If `codeCount(m, 15S² + 40S, ⌈log₂(m+1)⌉) < N`, then some matroid on
`E` has no signed tropical circuit of size at most `S` computing `h_M` on `{0,1}^E`.

*Proof.*  Otherwise every matroid (a finite set of them, `finite_matroids`) is counted in
the counting form, and `N ≤` their number `≤ codeCount(…) < N`.  ∎

### 2.16 Corollary E (`Polytope.lean`: `supportFn_basePolytope`, `corollaryE`, `corollaryE_binary`)

**Proposition 2.18.**  `σ_{B(M)}(w) = h_M(w)` for every `w ∈ ℝ^E`.

*Proof.*
1. `⟨w, 1_B⟩ = w(B)` (`dot_indVec`), and `1_B ∈ B(M)` for the heaviest basis `B`.
2. `x ↦ ⟨w, x⟩` is linear, hence convex, so every `x ∈ B(M)` has `⟨w, x⟩ ≤ ⟨w, 1_B⟩` for some
   basis `B` (Mathlib's `ConvexOn.exists_ge_of_mem_convexHull`), and `⟨w, 1_B⟩ ≤ h_M(w)`.  ∎

**Corollary E (`corollaryE`, `corollaryE_binary`).**  Let `vxc` be any function from subsets
of `ℝ^E` to `ℕ` and `c ∈ ℕ` such that every set `P` whose support function is computed at
every `w ∈ ℝ^E` by a signed tropical circuit of size `t` has `vxc(P) ≤ ct` (hypothesis
`hHL`).  Then for every matroid `M` with a Boolean rank circuit of size `s`,
`vxc(B(M)) ≤ c(3ms + mL + 9m² + 4m + 4L + 1)`; and for every `A ∈ GF(2)^{r×m}`,
`vxc(B(binary matroid of A)) ≤ 100 c (m+1)²(r+1)²`.

*Proof.*  Proposition 2.18 turns the circuits of Theorem A and Corollary C into circuits
for the support function; apply `hHL`.  ∎

### 2.17 Corollary F (`Subtractionfree.lean`)

**Proposition 2.19 (`maxBasisWeight_eq_sum_sugeno`).**  For every `w ∈ ℝ^E`,
`h_M(w) = ∑_{u=1}^{k} Λ_{g_u}(w)` with `g_u(S) = [u ≤ r(S)]`.

*Proof.*
1. Each `g_u` (`1 ≤ u ≤ k`) is monotone, `g_u(∅) = 0`, `g_u(E) = 1`.
2. `Λ_g(w + c·1) = Λ_g(w) + c` (`sugeno_add_const`, from `le_sugeno_iff`), and
   `h_M(w + c·1) = h_M(w) + ck` (Proposition 2.12, item 2).  So it suffices to take
   `w = D ≥ 0` (with `c = min_e w_e`).
3. On `D ≥ 0`: `∑_u Λ_{g_u}(D) = ∑_u C_{g_u(E \ ·)}(D) = C_{∑_u g_u(E \ ·)}(D)`
   (Proposition 2.9, linearity), and `∑_{u=1}^{k} [u ≤ r(X)] = r(X)` for `r(X) ≤ k`
   (`sum_thresholds`), so this is `C_{r(E \ ·)}(D) = h_M(D)` (Proposition 2.12, item 1).  ∎

**Corollary F, upper bound, circuit form (`corollaryF_upper`).**  Let `C₁, …, C_k` be
lattice circuits such that `C_u` computes `g_u` monotonically.  The `(min, +, max)` circuit
that inlines them and adds their outputs (`corFCircuit`) has exactly
`∑_u size(C_u) + (k - 1)` gates (natural subtraction: `0` when `k = 0`) and computes `h_M`
at every `w ∈ ℝ^E`.

*Proof.*  Theorem 2.10 (item 1) gives `C_u(w) = Λ_{g_u}(w)` for all `w ∈ ℝ^E`; inline
(Lemma 2.2, one gate per gate, `latB_spec`), add `k` values at `k - 1` gates (`sumB_spec`);
Proposition 2.19.  ∎

**Lemma 2.20 (`exists_monCircuit`).**  Every monotone `g` with `g(∅) = 0` and `g(E) = 1` is
computed monotonically by a lattice circuit, the disjunctive normal form
`max_{A : g(A) = 1} min_{e ∈ A} x_e` (`dnfCircuit`).  Hence `Mon(g)` is attained
(`monSize_spec`).

**Corollary F, upper bound (`corollaryF_upper_mon`).**
`Size_{min,+,max}(h_M) ≤ ∑_{u=1}^{k} Mon(g_u) + (k - 1)` (natural subtraction).

*Proof.*  Choose `C_u` attaining `Mon(g_u)` (Lemma 2.20) and apply the circuit form.  ∎

**Corollary F, lower bound (`corollaryF_lower`).**  Assume (hypothesis `hJSS`) that every
`(min, +, max)` circuit computing `min_B w(B)` at every `w ∈ ℝ^E` has at least
`Mon(Span_M)` gates.  Then `Mon(Span_M) ≤ Size_{min,+,max}(h_M)`.

*Proof.*
1. `min_B w(B) = -h_M(-w)` (`minBasisWeight_eq`).
2. Exchanging `min` and `max` in a `(min, +, max)` circuit for `f` gives one of the same size
   for `w ↦ -f(-w)` (`swap_eval`): negation carries `min` to `max`, `max` to `min`, `+` to
   `+` and `0` to `0` (Lemma 2.1).
3. A circuit attaining `Size_{min,+,max}(h_M)` (it exists by the upper bound) gives a circuit
   of the same size for `min_B w(B)`; apply `hJSS`.  ∎


## 3. Correspondence table

Status "proved" means: proved in Lean without hypotheses beyond those stated.  Status
"hypothesis" names the external result that enters as an explicit hypothesis of the Lean
theorem.

| Item (this file) | Lean declaration | File | Status |
|---|---|---|---|
| Def 1.1 to 1.3, circuits, size, evaluation | `Arg`, `Gate`, `Circuit`, `Interp`, `wires`, `Circuit.size`, `Circuit.eval` | `Circuit.lean` | definition |
| Def 1.4, gate sets | `STOp`/`stInterp`, `BoolOp`/`boolInterp`, `LatOp`/`latInterp`, `TropOp`/`tropInterp` | `Models.lean` | definition |
| Def 1.6, binary output | `bitsVal`, `indicator` | `Models.lean` | definition |
| Def 1.7, gap sum `C_F` | `sortedVal`, `threshSet`, `gapSum` | `GapSum.lean` | definition |
| Def 1.8, `r`, `k`, `h_M` | `rk`, `rank`, `maxBasisWeight`, `isGreatest_maxBasisWeight` | `Matroid.lean` | definition, proved |
| Def 1.9, `Λ_g`, lattice circuits, `Lat`, `Mon` | `sugeno`, `Circuit.IsLattice`, `latSize`, `latDepth`, `monSize`, `monDepth`, `Circuit.depth` | `Lattice.lean` | definition |
| Lemma 2.1, homomorphism lemma | `wires_map`, `wires_map_of`, `Circuit.eval_map`, `Circuit.eval_map_of` | `Circuit.lean` | proved |
| Lemma 2.2, inlining | `inline_spec`, `length_inline` | `Inline.lean` | proved |
| Lemma 2.3, sorting network | `isortV_eq_insertionSort`, `isortB_spec` | `Sorting.lean` | proved |
| Lemma 2.4, `lem:bit` | `bit_identity`, `le_or_succ_le`, `sub_min_eq_max` | `GapSum.lean` | proved |
| Lemma 2.5, layer cake | `sum_gap_lt`, `eq_sum_gap`, `sum_eq_gapSum_card` | `GapSum.lean` | proved |
| Lemma 2.6, `lem:lift` with vanishing | `lift`, `lift_vanish`, `eval_liftInterp` | `Lift.lean` | proved |
| Theorem 2.7, `thm:compiler` | `thm_compiler`, `compiler_size`, `compVal_eq` | `Compiler.lean` | proved |
| Corollary 2.8, `cor:integer-observable` | `integer_observable` | `Compiler.lean` | proved |
| Proposition 2.9, `prop:sugeno` | `gapSum_eq_sugeno` | `Lattice.lean` | proved |
| Theorem 2.10, `thm:lattice` | `thm_lattice`, `latComputes_iff`, `eval_eq_sugeno` | `Lattice.lean` | proved |
| Lemma 2.11, bases along a chain | `exists_isBase_chain` | `Matroid.lean` | proved |
| Proposition 2.12, greedy, translation, `h_M(1_T)` | `maxBasisWeight_eq_gapSum`, `maxBasisWeight_add_const`, `maxBasisWeight_indicator` | `Matroid.lean` | proved |
| Theorem A | `theoremA`, `theoremACircuit_correct`, `theoremACircuit_spec` | `TheoremA.lean` | proved |
| Theorem B | `theoremB`, `theoremB_of_forall` | `Converse.lean` | proved |
| Proposition 2.14, binary matroid, rank, `Matrix.rank` | `binaryMatroid`, `eRk_binaryMatroid`, `eRk_binaryMatroid_eq_rank` (from `colMatroid`, `eRk_colMatroid`, `eRk_colMatroid_eq_rank`) | `Binary.lean`, `Elimination.lean` | proved |
| Proposition 2.15, elimination | `elimV`, `zst_elimV`, `card_flagSet_elimV` (from `colStepK_inv`, `card_occ_elimK`) | `Binary.lean`, `Elimination.lean` | proved |
| Proposition 2.16, rank circuit | `binaryRankCircuit`, `binaryRankCircuit_spec`, `binaryRankCircuit_rank` | `Binary.lean` | proved |
| Corollary C, binary matroids | `corollaryC_binary`, `corollaryC_binary_poly` | `Binary.lean` | proved |
| Lemma 2.17, counting circuits | `ncard_computed_le`, `exists_code`, `card_code` | `Counting.lean` | proved |
| Corollary D, counting form | `corollaryD_count` | `Counting.lean` | proved |
| Corollary D | `corollaryD` | `Counting.lean` | hypothesis `hN`: a lower bound on the number of matroids (Knuth 1974) |
| Proposition 2.18, support function | `supportFn_basePolytope` | `Polytope.lean` | proved |
| Corollary E | `corollaryE`, `corollaryE_binary` | `Polytope.lean` | hypothesis `hHL`: Hertrich and Loho's `vxc(P) ≤ O(nnc(P))` composed with the conversion of signed tropical circuits into networks |
| Proposition 2.19 | `maxBasisWeight_eq_sum_sugeno` | `Subtractionfree.lean` | proved |
| Corollary F, upper bound | `corollaryF_upper`, `corollaryF_upper_mon`, `exists_monCircuit` | `Subtractionfree.lean` | proved |
| Corollary F, lower bound | `corollaryF_lower`, `swap_eval`, `minBasisWeight_eq` | `Subtractionfree.lean` | hypothesis `hJSS`: Jukna, Seiwert and Sergeev, Proposition 2, for minimum-weight bases |


## 4. Differences from the research document and the papers

1. **Size measure.**  As in Definition `def:models` of the paper, size counts gates only;
   sources cost nothing.
2. **Sorting network.**  The paper sorts with Batcher's network, `O(m log² m)` comparators;
   `BLUEPRINT.md` (D3) planned odd-even transposition with the 0-1 principle.  Lean uses the
   insertion-sort network, `m(m-1)/2` comparators, whose output is identified with Mathlib's
   `List.insertionSort`, so correctness needs no 0-1 principle.  The cost `3m(m-1)/2` is
   absorbed by the `m²` term: the compiler bound `3ms + mN + 6m²` and the bound of Theorem A
   contain no `m log² m` term, which is stronger than `O(ms + mN + m² + m log² m)` and
   `O(ms + m log k + m² + m log² m)`.  `greedy_intersection.tex` uses the same network and
   the same constants.
3. **The threshold integral** is defined as the gap sum (`BLUEPRINT.md`, D4).  The gap sum
   makes sense for every `F`, so Theorem 2.7 and Corollary 2.8 drop the hypothesis
   `F(E) = 0`; `greedy_intersection.tex` now defines `C_F` the same way.  The integral form
   and Proposition `prop:two-readings` were formalized afterwards (`Integral.lean`,
   `notes/E2-integral.md`).
4. **Order of summation in Corollary 2.8.**  The paper applies Horner's rule inside each gap
   and accumulates one sum, at `O(mL)` gates; Lean compiles the `L` bits as `L` observables
   and applies Horner's rule once to the `L` sums, at `mL + 2L` gates, by linearity.  Same
   bound up to the constant, and `greedy_intersection.tex` states `3ms + mL + 6m² + 2L`.
5. **Theorem A** is stated with explicit constants, `3ms + mL + 9m² + 4m + 4L + 1`, as in
   `greedy_intersection.tex`.  The rank circuit may have any number of outputs; the first
   `⌈log₂(k+1)⌉` are used.
6. **Theorem B.**  The hypothesis is that `C` computes `h_M` on `{0,1}^E`, as in
   `greedy_intersection.tex`, which is weaker than the research document's "computes
   `h_M`"; `theoremB_of_forall` gives the research document's form.  The bound is
   `15S² + 40S` with `W = S + 2` bits, not the manuscript's `13S² + 40S + 3`: the Lean
   Boolean model reads the constant `false` as a free source (Definition 1.4), so `false`
   costs nothing and `true` one negation inside each gadget that needs it; its full adder
   spends eleven gates where the manuscript's spends nine, and its maximum gadget `15W + 10`
   where the manuscript's spends `13W + 1`.  Both bounds are `O(S²)`.  The manuscript will be
   aligned with the Lean constant.
7. **Boolean constants.**  The paper's Boolean circuits have `∧, ∨, ¬`; the Lean model also
   has the constant `false` as a free source.  For a hypothesis (Theorem A, Theorem 2.7) this
   makes the Lean statement apply to more circuits.  For a conclusion (Theorem B,
   Proposition 2.16) a constant can be removed at two gates when `m ≥ 1` (`x₀ ∧ ¬x₀`); this
   is not formalized.
8. **Corollary C** is formalized here for binary matroids, with `r` the number of rows of
   the representation.  The rank circuit has `m(9r² + 5r) + 11r⌈log₂(r+1)⌉` gates, which is
   `O(mr²)`, and the resulting signed circuit is `O(m²r²)`.  Finite fields, `ℚ`, duals,
   graphic, cographic and transversal matroids, and gammoids were added afterwards
   (`Classes/`, see `PHASE2.md`).
9. **Corollary D** is stated here as a finite statement with an explicit count, with the lower
   bound on the number of matroids as the hypothesis `hN`.  The asymptotic reading and the
   bound on the number of matroids were formalized afterwards (`SparsePaving.lean`,
   `Asymptotic.lean`, `notes/E3-asymptotic.md`).  The Lean form counts circuits that compute
   `h_M` only on `{0,1}^E`, which is the stronger statement.
10. **Corollary E** formalizes the identity `σ_{B(M)} = h_M` and the composition with
    Theorem A and Corollary C; the virtual extension complexity is an abstract function
    constrained only by the hypothesis `hHL`.
11. **Corollary F.**  The upper bound is proved in the form stated.  `Mon(g)` counts lattice
    circuits read over `Bool`, which are the monotone Boolean circuits without constants of
    Definition `def:lattice`.  The lower bound depends on `hJSS`.
12. **Lemma `lem:lift`** is stated for circuits whose amplitude is an input (input `m`); in
    the compiler the amplitude is an internal wire, which Lemma 2.2 handles.  The vanishing
    statement is proved for all wires of the lifted circuit at `Δ = 0`.
13. **Matroids** are Mathlib's `Matroid (Fin m)` with ground set `univ`, and the rank
    function is Mathlib's `eRk`; no separate rank axioms are introduced (BLUEPRINT D6
    planned a separate Finset rank function, which turned out unnecessary).


## 5. Sanity examples (`Examples.lean`)

The constructed circuits are evaluated by the kernel (`decide +kernel`) over `ℤ`, and the
values are transferred to `ℝ` through Lemma 2.1 (`eval_intCast`).

* `U_{1,2}` as the binary matroid of `[[1, 1]]`: the rank circuit (39 gates) outputs
  `min(|S|, 1)`; the circuit of Theorem A returns `3` at `(3, -1)` and `-2` at `(-2, -7)`,
  hence `h_M(3, -1) = 3` and `h_M(-2, -7) = -2` (Theorem A applied to a concrete matroid,
  with negative weights).
* `U_{2,3}` as the binary matroid of `[[1,0,1],[0,1,1]]`: the rank circuit outputs
  `min(|S|, 2)` on all eight sets, so the binary matroid has rank function `min(|S|, 2)`.
* The compiler on `F(S) = [S ≠ ∅]` at `D = (3, 1, 2)` returns `C_F(D) = 2`.
* The four-gate majority circuit is a lattice circuit, computes majority over `Bool`, and
  over `ℝ` returns the Sugeno value `2` of `(3, 1, 2)`, the second largest entry.
* The simulation of Theorem B on `max(x₀, x₁)` with `3` bits returns `[S ≠ ∅]` in binary.
* Theorem B is not vacuous: for every binary matroid, Corollary C and Theorem B produce a
  Boolean rank circuit.

These examples guard against the failure modes listed in the task: the size counts gates
(`majCircuit.size = 4`, `binaryRankCircuit A12` has 39 gates), the default read is never
the source of a value in these instances, the hypotheses of Theorems A and B are met by
concrete non-trivial matroids, and the circuits compute values that depend on the input.


## 6. Scope and limitations

* **Formalized after Phase 1 (2026-10-12), documented in `PHASE2.md` and `notes/`:** the
  integral form of the threshold integral and Proposition `prop:two-readings`, Lemma
  `lem:lipschitz` and the Lipschitz statement of Corollary `cor:integer-observable`
  (`Integral.lean`); the `±` normal form, Proposition `prop:normal-form` (`NormalForm.lean`);
  the asymptotic reading of Corollary D, with the number of matroids proved
  (`SparsePaving.lean`, `Asymptotic.lean`; `corollaryD_unconditional` discharges `hN`);
  Corollary C for matroids over finite fields and over `ℚ`, duals, graphic, cographic and
  transversal matroids, and gammoids (`Classes/`).
* **Not formalized:** Corollary C for unions; uniformity (that the circuits are
  produced by a polynomial-time algorithm), although every construction is an explicit Lean
  function.
* **External results as hypotheses:** Hertrich and Loho's bound with the network conversion
  (`corollaryE`, `hHL`), and Jukna, Seiwert and Sergeev's Proposition 2 (`corollaryF_lower`,
  `hJSS`).  None is stated as an `axiom`.  The hypothesis `hN` of `corollaryD` (the number of
  matroids) is discharged by `Asymptotic.corollaryD_unconditional`.
* **Model conventions:** a reference to a wire not yet built reads the constant
  (Definition 1.3); lattice circuits exclude it by Definition 1.9.  Boolean circuits read the
  constant `false` for free (Section 4, item 7).
* **Corollary C** uses the number `r` of rows of the representation; `r ≥ k`.
* **Sanity checks** of the full Theorem A pipeline are run on `U_{1,2}`; on `U_{2,3}` only the
  rank circuit is evaluated, because kernel evaluation of the 1,700-gate Theorem A circuit
  of `U_{2,3}` did not finish within ten minutes.


## 7. Module sizes

| Module | Lines | Content |
|---|---|---|
| `Circuit.lean` | 348 | circuits, homomorphism lemma, builders |
| `Inline.lean` | 166 | inlining |
| `Models.lean` | 138 | gate sets, binary values |
| `Sorting.lean` | 163 | insertion-sort network |
| `GapSum.lean` | 188 | gap sum, lem:bit, layer cake |
| `Lift.lean` | 173 | lem:lift |
| `Compiler.lean` | 548 | thm:compiler, cor:integer-observable |
| `Lattice.lean` | 383 | prop:sugeno, thm:lattice |
| `Matroid.lean` | 258 | greedy as a gap sum |
| `TheoremA.lean` | 329 | Theorem A |
| `Converse.lean` | 690 | Theorem B |
| `Subtractionfree.lean` | 481 | Corollary F |
| `Binary.lean` | 671 | Corollary C, binary matroids |
| `Counting.lean` | 284 | Corollary D |
| `Polytope.lean` | 87 | Corollary E |
| `Examples.lean` | 190 | sanity examples |
| total | 5097 | |
