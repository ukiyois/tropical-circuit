"""Module headers of the Lean artifact that replace the headers of the development.

Keys are module paths of the development (relative to SignedTropical/, without .lean).
The texts use the names of the artifact (after renaming) and cite the paper by its
IPCO numbering."""

HEADERS = {}

HEADERS["Circuit"] = r"""/-!
# Circuits

Definition 1 of the paper: a circuit is a finite directed acyclic graph with unrestricted
fan-out whose sources are the input coordinates and one constant; its size is the number of
gates.

Here a circuit on `n` inputs is a list of gates together with a list of output operands.
Gate `k` produces wire `k`.  An operand (`Arg`) is an input coordinate, the constant
source, or a wire.  Sources are operands, not gates, so `Circuit.size` is exactly the
number of operation gates.  Sharing is free: any number of gates may read the same wire.

Evaluation is total: a wire that does not exist yet reads the constant.  Such a reference
can be replaced by the constant source without changing any value or the size, so for gate
sets that contain a constant source this convention adds no expressive power.  Lattice
circuits have no constant source; for them `Lattice.lean` imposes well-formedness.

The main result is the homomorphism lemma `wires_map`: a map that sends the constant to
the constant and commutes with every operation commutes with evaluation.  Its form
`wires_map_of` only asks for commutation on values satisfying a predicate that holds at
every wire.

The second half sets up the builder discipline used for every construction: gates are
only ever appended, and `Den I gs a f` records that operand `a` carries `f x` at every
input `x` in the gate list `gs`; this is stable under appending (`Den.mono`).
-/"""

HEADERS["Models"] = r"""/-!
# Gate sets

* A *(max,+,-)-circuit* has binary `max`, `+` and `-` gates; its sources are the inputs and
  the constant `0` (`MPMOp`, `mpmInterp`), as in Definition 1 of the paper.
* A *Boolean* circuit has `∧`, `∨` and `¬` gates; its sources are the input bits and the
  constant `false` (`BoolOp`, `boolInterp`).  The negation gate reads its first operand.
* A *lattice* circuit has binary `min` and `max` gates and no constants (`LatOp`,
  `latInterp`).  Read over `Bool`, where `min` is `∧` and `max` is `∨`, the same circuits
  are the monotone Boolean circuits without constants.  The absence of constants is the
  predicate `IsLattice` of `Lattice.lean`.
* The *subtraction-free* gate set has `min`, `+` and `max` gates (`TropOp`, `tropInterp`),
  with the same sources as the (max,+,-) one; only `Subtractionfree.lean` uses it.

Size is the number of gates in every model (`Circuit.size`).
-/"""

HEADERS["Sorting"] = r"""/-!
# A sorting network over `max`, `+`, `-`

The circuit of Theorem 3 of the paper needs the sorted entries of `D`, computed by a fixed
comparator network.  The network used here is insertion sort: inserting `a` into a list
`b₁ ≤ b₂ ≤ ⋯` by the comparators `(a, b₁), (max a b₁, b₂), …` (`insV`), and sorting by
inserting the entries one at a time (`isortV`).  On a list of length `k` it has
`k (k - 1) / 2` comparators.

A comparator costs three (max,+,-) gates: `max a b`, `a + b`, and
`min a b = (a + b) - max a b` (`cmpB`).

The network computes `List.insertionSort` exactly (`isortV_eq_insertionSort`), so its
correctness is Mathlib's `List.sortedLE_insertionSort` and `List.perm_insertionSort`; no
0-1 principle is needed.  Its quadratic cost is absorbed by the `m²` term of Theorem 3.
-/"""

HEADERS["GapSum"] = r"""/-!
# Sums over the sorted levels

Definition 2 of the paper.  For `D : Fin m → ℝ` sort the entries and prepend a zero:
`s₀ = 0, s₁ ≤ ⋯ ≤ s_m` (`sortedVal`), and put `G_k = {e : D_e ≤ s_k}` (`sublevelSet`).  For
a set function `F` let `C_F(D) = ∑_{k<m} (s_{k+1} - s_k) F(G_k)` (`levelSum`).  The integral
form of Definition 2 is proved in `Integral.lean`; no size statement uses it, so the
circuits need no measure theory.  The sum is defined for every `F`, without `F(E) = 0`.

On `D ≥ 0` the prepended zero keeps `s` monotone (`sortedVal_mono`), every entry of `D`
is one of the `s_j` (`exists_sortedVal_eq`), which gives equation (2) in the proof of
Theorem 3 (`bit_identity`), and the layer-cake identity
`∑_k (s_{k+1} - s_k) [s_k < s_j] = s_j` (`sum_gap_lt`) writes a modular function as a
level sum (`sum_eq_levelSum_card`), which Lemma 5 uses.
-/"""

HEADERS["Lift"] = r"""/-!
# Simulating a Boolean circuit at scale `Δ`

The gate-by-gate simulation in the proof of Theorem 3 of the paper.  Represent the Boolean
value `b` by `Δ·b` (`scaledVal`).  Then

* `Δ(b₁ ∧ b₂) = max(Δb₁ + Δb₂ - Δ, 0)`,
* `Δ(b₁ ∨ b₂) = max(Δb₁, Δb₂)`,
* `Δ(¬b) = Δ - Δb`,

for every `Δ ≥ 0` (`scaledVal_op`), which is the case check of the homomorphism lemma for the
reading `simInterp Δ` of the Boolean gates (`eval_simInterp`).  The simulating circuit
replaces each Boolean gate by the corresponding gadget of three, one or one (max,+,-)
gates (`simGad`), so it has at most `3 s` gates.

At `Δ = 0` all inputs are `0`, and a (max,+,-)-circuit whose inputs are all `0` carries
`0` on every wire (`wires_eq_zero`); this is also the instance `Δ = 0` of `eval_simInterp`.
-/"""

HEADERS["Compiler"] = r"""/-!
# Theorem 3: (max,+,-)-circuits for the sums of Definition 2

Theorem 3 and Corollary 26 of the paper.  Given one Boolean circuit `B` with `N` outputs,
computing `F = (F₁, …, F_N)` from the indicator vector of its argument, the circuit
`sumCircuit` on input `D`:

1. sorts `D` with the insertion-sort network (`isortB`), `3 · m (m - 1) / 2` gates;
2. for each `k < m`: forms `Δ_k = s_{k+1} - s_k` (one gate), the `m` scaled indicators
   `max(Δ_k - max(D_e - s_k, 0), 0) = Δ_k · 1[e ∈ G_k]` (four gates each, equation (2) of
   the paper), simulates `B` once at scale `Δ_k` (at most `3 s` gates,
   `Simulation.lean`), and adds the `N` outputs to `N` running sums (`N` gates).

On `D ≥ 0` the `u`-th running sum ends at `∑_k Δ_k F_u(G_k) = C_{F_u}(D)` (`compVal_eq`).
For `k` with `Δ_k = 0` every scaled indicator and every simulated output is `0`, so it does
not matter which set the indicators describe there; in the proof this is the case `Δ = 0`
of the homomorphism lemma, and no separate argument is needed.

The size is at most `3 m s + m N + 6 m²` (`sumCircuit_size`, `thm_levelSum`).

For an integer-valued `f` whose `L` bits are the outputs of `B`, Horner's rule on the `L`
outputs gives `∑ⱼ 2ʲ C_{bⱼ}(D) = C_f(D)` at `2 L` more gates (`integer_levelSum`,
Corollary 26).
-/"""

HEADERS["LevelCompiler"] = r"""/-!
# Corollary 4: the sums at given levels

Corollary 4 of the paper: the construction of Theorem 3 run at levels that are computed
inside the circuit and are not the values it reads.  Given a Boolean circuit `B` with `q`
inputs and `N` outputs, operands carrying levels `Λ ∈ ℝ^L` and operands carrying query
values `Q ∈ ℝ^q`, the circuit (`levB`):

1. sorts `Λ` with the insertion-sort network, `3 L (L - 1) / 2` gates, and prepends `s₀ = 0`;
2. for each `k < L`: forms `Δ_k = s_{k+1} - s_k`, the `q` scaled indicators
   `max(Δ_k - max(Q_j - s_k, 0), 0)`, simulates `B` at scale `Δ_k` and adds the `N`
   outputs to `N` running sums (`gapB` of `SumCircuit.lean`, with `gapB_spec` for different
   query values and levels).

Its size is `levCost B L = 3 L(L-1)/2 + L (1 + 4 q + Σ simCost + N)` (`levB_spec`), at most
`3 L²/2 + L (1 + 4 q + 3 s + N)` (`levCost_le`).  When `Λ ≥ 0` and every `Q_j` is one of
`s_0 = 0, s_1, …, s_L`, the indicators are exact (`bitQ_eq`), and output `u` is
`Σ_{k<L} Δ_k F_u([Q ≤ s_k])` (`levVal_eq`), `F_u` the `u`-th output of `B` as a function of
its input bits.  With `Q = Λ = D` this is the circuit of Theorem 3.
-/"""

HEADERS["Integral"] = r"""/-!
# The sums of Definition 2 as integrals; a Lipschitz bound

Definition 2 of the paper and the remark after it.  For `D ≥ 0` the sublevel set
`G_t(D) = {e : D_e ≤ t}` (`sublevel D t`) equals `G_k` for `s_k ≤ t < s_{k+1}`
(`sublevel_eq_sublevelSet`) and `E` for `t ≥ s_m` (`sublevel_eq_univ`), so `t ↦ F(G_t(D))` is
a step function whose Lebesgue integral is the level sum:

* `levelSum_eq_intervalIntegral`: `C_F(D) = ∫_0^{s_m} F(G_t(D)) dt` for every `F`, where
  `s_m = max_e D_e` (`sortedVal_last_eq_iSup`);
* `levelSum_eq_integral_Ioi`: `C_F(D) = ∫_0^∞ F(G_t(D)) dt` when `F(E) = 0`;
* `levelSum_eq_integral_lovasz`: `C_F(D) = ∫_0^∞ g({e : D_e ≥ t}) dt` with `g(S) = F(E \ S)`
  when `F(E) = 0`, that is, `C_F(D)` is the Lovász extension of `g` at `D`;
  `levelSum_compl_eq_integral` is the same identity started from `g` with `g(∅) = 0`;

each together with the integrability of the integrand.

If `0 ≤ F ≤ c` then `|C_F(D) - C_F(D')| ≤ c ‖D - D'‖₁` (`abs_levelSum_sub_le`), with the
cases `lipschitz` (Boolean `F`, `c = 1`) and `integer_levelSum_lipschitz`
(`c = max_S f(S)`); these bounds are not used in the paper.  Neither needs `F(E) = 0`: the
value `F(E)` does not enter the level sum (`levelSum_ite_univ`), since a difference `Δ_k`
with `G_k = E` is `0`.
-/"""

HEADERS["Lattice"] = r"""/-!
# Lattice circuits and the Sugeno form

Auxiliary results, not stated in the paper; `Subtractionfree.lean` uses them, and
`Rainbow/POSLRank.lean` imports that module.

A lattice circuit has `min` and `max` gates and no constants: no operand is the constant
source and no operand refers to a wire not yet built (`Circuit.IsLattice`).  Read over
`Bool`, where `min` is `∧` and `max` is `∨`, the same circuits are the monotone Boolean
circuits without constants.

* `thr_eval`: for a lattice circuit and every level `t`, comparing the outputs with `t`
  gives the outputs of the same circuit over `Bool` on the compared inputs.  This is the
  homomorphism lemma for `x ↦ [t ≤ x]`, which commutes with `min` and `max`.
* `sugeno`: `Λ_g(D) = max_{A : g(A)} min_{e ∈ A} D_e`, with the convention that the maximum
  over an empty family is `0` (the convention of `ℝ`'s `iSup`).
* `levelSum_eq_sugeno`: for monotone `g` with `g(∅) = 0` and `F(S) = g(E \ S)`,
  `C_F(D) = Λ_g(D)` on `D ≥ 0`.
* `thm_lattice`: for monotone `g` with `g(∅) = 0` and `g(E) = 1`, a lattice circuit
  computes `Λ_g` on `ℝ_{≥0}^E` exactly when, read over `Bool`, it computes `g`.  The
  forward direction holds on all of `ℝ^E` (`eval_eq_sugeno`).
-/"""

HEADERS["Subtractionfree"] = r"""/-!
# Circuits without subtraction for `h_M`

Auxiliary results, not stated in the paper; `Rainbow/POSLRank.lean` imports this module.

For the rank levels `g_u(S) = [u ≤ r(S)]`, `h_M(w) = ∑_{u=1}^{k} Λ_{g_u}(w)` at every
`w ∈ ℝ^m` (`maxBasisWeight_eq_sum_sugeno`): on `D ≥ 0` this is the Sugeno form summed over
`u` against Lemma 5, and both sides move by `k c` under `w ↦ w + c·1`.  Each `Λ_{g_u}` is
computed on all of `ℝ^m` by the lattice circuit of a monotone Boolean circuit for `g_u`
(`eval_eq_sugeno`), and `k - 1` additions sum them (`monotone_upper`), which bounds the
size of `(min,+,max)`-circuits for `h_M` (`monotone_upper_mon`).  The lower bound
`monotone_lower` takes Proposition 2 of Jukna, Seiwert and Sergeev as the hypothesis `hJSS`;
the part proved here is the reduction from the maximization form: exchanging `min` and `max`
in a circuit for `h_M` gives a circuit of the same size for `min_B w(B) = -h_M(-w)`
(`swap_eval`).
-/"""

HEADERS["Converse"] = r"""/-!
# Theorem B: the converse simulation

Theorem B of the paper.  A (max,+,-)-circuit of size `S` that computes `h_M` on `{0,1}^E`
yields a Boolean circuit of size at most `15 S² + 40 S` that outputs `r(T)` in binary from
the indicator vector of `T`.

Proof route.

1. `h_M(1_T) = r(T)` (`maxBasisWeight_indicator`).
2. On inputs in `{0, 1}` the circuit, read over `ℤ`, has the same values as over `ℝ`
   (homomorphism lemma for `ℤ → ℝ`), and wire `j` carries an integer of absolute value at
   most `2^{j+1}`, so every wire is at most `2^S` (`abs_wires_le`).
3. With `W = S + 2` bits, two's complement arithmetic (`BitVec W`, `bvInterp`) agrees with
   the integers on all wires (`wires_bv`): `+` and `-` are ring operations modulo `2^W`,
   and `max` is read through the two's complement comparison, which is exact on values of
   absolute value at most `2^S < 2^{W-1}`.
4. Each (max,+,-) gate is simulated on `W`-bit vectors by a Boolean gadget: a ripple-carry
   adder (`11W` gates), a subtractor `x + ¬y + 1` (`12W + 1` gates), and the maximum in two's
   complement (`15W + 10` gates), whose comparison bit is Lean's `BitVec.slt_eq_not_carry`.
   The gadgets are proved against `BitVec` addition through `BitVec.getLsbD_add_add_bool`
   and `BitVec.carry_succ`.
5. Inlining with these gadgets (`inline_spec`) gives a Boolean circuit whose outputs are
   the bits of the output of the (max,+,-)-circuit, which is `r(T) ∈ [0, 2^S]`.

The Boolean model of the paper has `∧, ∨, ¬`; this one also reads the constant source
`false` (`boolInterp`).  When `m ≥ 1`, `false = x₀ ∧ ¬x₀` costs two gates.
-/"""

HEADERS["TheoremA"] = r"""/-!
# Theorem A: maximum-weight bases

Theorem A of the paper.  Let `M` be a matroid on `E = Fin m` with rank function `r` and
`k = r(E)`.  If a Boolean circuit of size `s` outputs `r(S)` in binary from the indicator
vector of `S`, then `h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^E` by a
(max,+,-)-circuit of size at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`, where
`L = ⌈log₂(k + 1)⌉` (`Nat.size k`).

The circuit (`theoremACircuit`):

1. `μ = min_e w_e` by `m - 1` minimum gadgets of three gates (`minListB`);
2. `D_e = w_e - μ ≥ 0`, `m` gates;
3. the circuit of Corollary 26 on `D` for `F(S) = r(E \ S)`, whose Boolean circuit is the
   given one with its inputs negated (`negInputs`, `m` more gates) and its outputs truncated
   to the `L` low bits (`truncOuts`; the higher bits are `0` because `r ≤ k < 2^L`);
4. `μ k` by doubling, at most `2 L` gates (`mulConstB`);
5. one addition.

Correctness: `h_M(w) = μ k + h_M(w - μ·1)` (`maxBasisWeight_add_const`) and
`h_M(D) = C_F(D)` on `D ≥ 0` (`maxBasisWeight_eq_levelSum`, Lemma 5).
-/"""

HEADERS["Matroid"] = r"""/-!
# Maximum-weight bases as a level sum

Lemma 5 of the paper: `h_M` is the Lovász extension of the rank function.

Matroids are Mathlib's `Matroid (Fin m)` with ground set `univ`.  For a set
`S : Finset (Fin m)` the rank is `M.eRk S : ℕ∞`, and `rk M S : ℕ` is its value as a natural
number (`coe_rk`).  The largest weight of a base is `h_M(w) = max_B w(B)`
(`maxBasisWeight`), the greatest element of the finite nonempty set of base weights
(`isGreatest_maxBasisWeight`).

Results:

* `maxBasisWeight_eq_levelSum`: for `D ≥ 0`,
  `h_M(D) = ∑_{k<m} (s_{k+1} - s_k) r({e : D_e > s_k}) = C_F(D)` with `F(S) = r(E \ S)`.
  The upper bound reads each base weight as the level sum of `|B \ G_k|`
  (`sum_eq_levelSum_card`) and bounds `|B ∩ U| ≤ r(U)`; the lower bound is a base that
  restricts to a base of every strict upper level set `{e : D_e > s_k}`, which exists
  because these sets form a chain (`exists_isBase_chain`).
* `maxBasisWeight_add_const`: `h_M(w + c·1) = h_M(w) + c k` with `k = r(E)`, since every
  base has `k` elements.
* `maxBasisWeight_indicator`: `h_M(1_T) = r(T)`.
-/"""

HEADERS["Binary"] = r"""/-!
# Binary matroids: Corollary 6(1)

Corollary 6(1) of the paper, for binary matroids (linear matroids over `GF(2)` with a fixed
representation).

1. **The binary matroid** of a matrix `A ∈ GF(2)^{r × m}` (`binaryMatroid`): the column
   matroid of `Elimination.lean` over `GF(2)`, so a set of columns is independent iff the
   columns are linearly independent over `GF(2)`.  Its rank function is the dimension of the
   span of the columns (`eRk_binaryMatroid`), which is Mathlib's `Matrix.rank` of the column
   submatrix (`eRk_binaryMatroid_eq_rank`).
2. **Elimination without branching** (`elimV`): the columns are processed in order; each
   is reduced against an echelon basis kept in a fixed array of `r` slots, and a nonzero
   remainder is stored in the slot of its leading position.  Every step is a fixed Boolean
   formula of the input bits, so the whole procedure is a Boolean circuit.  Read over
   `GF(2)`, it is the elimination `elimK` of `Elimination.lean` (`zst_elimV`), so the number
   of occupied slots is the rank (`card_flagSet_elimV`).
3. **The rank circuit** (`binaryRankCircuit`) outputs this number in binary.  It has
   `m (9 r² + 5 r) + 11 r ⌈log₂(r+1)⌉` gates (`binaryRankCircuit_size`).
4. **Corollary 6(1)** (`classes_binary`): Theorem A applied to this circuit.
-/"""

HEADERS["Counting"] = r"""/-!
# Counting Boolean circuits: the first step of Corollary 27

Corollary 27 of the paper: most matroids need large (max,+,-)-circuits.  There are
`2^{2^m / poly(m)}` matroids on `m` elements and `2^{O(s log s)}` Boolean circuits of size
`s`, and Theorem B transfers the bound.  This module proves the counting step; the
conclusion is in `Asymptotic.lean`.

* **Counting Boolean circuits** (`ncard_computed_le`): the functions
  `S ↦ bitsVal(B(1_S))` with values below `2^L` computed by Boolean circuits of size at
  most `s` number at most `codeCount m s L = (s+1) (3 (m+s+1)²)^s (m+s+1)^L`.  Every such
  circuit is equivalent to a decoded code (`exists_code`): operands are renumbered into
  `m + 1 + s` symbols, a reference to a wire that does not exist becomes the constant
  (which it reads anyway), and the outputs are cut or padded to `L` bits.
* **Matroids are determined by their rank function** (`eq_of_eRk_eq`).
* **Counting form** (`count_codes`): at most `codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉`
  matroids on `Fin m` have a (max,+,-)-circuit of size at most `S` computing `h_M` on
  `{0,1}^m` (Theorem B and the two facts above).
* **Conditional form** (`count_bound`): given a lower bound `N` on the number of matroids
  on `Fin m`, if `codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉ < N` then some matroid has no
  (max,+,-)-circuit of size at most `S` computing `h_M`, not even on `{0,1}^m` (hypothesis
  `hN`; `Asymptotic.lean` removes it).
-/"""

HEADERS["Asymptotic"] = r"""/-!
# Corollary 27: most matroids need large (max,+,-)-circuits

Corollary 27 of the paper: for all large `m`, most matroids `M` on `m` labeled elements
have no (max,+,-)-circuit for `h_M` of size less than `2^{m/2}/m²`.

Matroids are Mathlib's `Matroid (Fin m)` with ground set `univ`; let `N(m)` be their
number.  Let `A(m)` be the number of those `M` for which a (max,+,-)-circuit of size less
than `2^{m/2}/m²` computes `h_M` on `{0,1}^m` (at the indicator vectors of all sets).

* **Explicit form** (`count_explicit`): for `m ≥ 128`, `2^{⌊2^m/m³⌋} A(m) ≤ N(m)`.
  Every size below `2^{m/2}/m²` is at most `S = ⌊2^{m/2}/m²⌋`, and `S² m⁴ ≤ 2^m`
  (`floor_sq_mul_le`).  By `count_codes` (Theorem B and the counting of Boolean circuits),
  `A(m) ≤ codeCount m s L` with `s = 15S² + 40S ≤ 55·2^m/m⁴` and `L = ⌈log₂(m+1)⌉ ≤ m`, and
  `codeCount m s L ≤ 2^{m + (2m+2)s + mL}` (`codeCount_le`).  On the other side
  `N(m) ≥ 2^a` with `m(m+1)a ≥ 2^m` (`exists_two_pow_le_ncard_matroids`, from
  `SparsePaving.two_pow_ceil_le_ncard_matroids`), and `⌊2^m/m³⌋ + m + (2m+2)s + mL ≤ a`
  (`exponent_le`).
* **Corollary 27** (`count_tendsto`): `A(m)/N(m) → 0`.  The same holds for circuits that
  compute `h_M` at every `w ∈ ℝ^m` (`count_tendsto_of_forall`), and the fraction of matroids
  for which every (max,+,-)-circuit computing `h_M` on `{0,1}^m` has size at least
  `2^{m/2}/m²` tends to `1` (`count_most`).
* **The conditional form without its hypothesis** (`count_unconditional`).
-/"""

HEADERS["Inline"] = r"""/-!
# Inlining a circuit, one gadget per gate

Given a circuit `C` over a gate set `Op` and, for each operation, a gadget that builds
gates of another gate set `Op'`, `inline` appends to a gate list the gadgets for the gates
of `C` in order and returns the representations of the outputs of `C`.  A source wire is
represented by a value of an arbitrary type `ρ`: one operand for the simulation at scale
`Δ` (`Simulation.lean`) and for `Subtractionfree.lean`, a list of operands carrying the bits
of an integer for the converse simulation (`Converse.lean`).

`inline_spec` is the only correctness statement: if every gadget implements the
corresponding operation of a reading `J x` of `Op` (which may depend on the input `x` of
the outer circuit), then every output representation carries the corresponding output of
`C` read through `J x`.  `length_inline` counts the appended gates.
-/"""

# literal replacements inside bodies, per module (old text, new text)
BODY = {
    "Circuit": [(
        "(`signed_assignment.tex`, the common source of\n"
        "the threshold identity in the proof of Thm. `thm:lattice` and of amplitude lifting,\n"
        "Lemma `lem:lift`)",
        "(the common source of the threshold identity of `Lattice.lean` and of\n"
        "the simulation in the proof of Theorem 3)")],
    "BoolAlg.Impl": [
        ("The algorithms of Phase 2 (`greedy_intersection.tex`, Lemma `lem:observer` and the proof of\n"
         "Theorem `thm:D`) are built",
         "The circuits of Lemma 22 and of the proof of Theorem D of the paper are built"),
        ("Unfolded, this is the Phase 1 form of a gadget\n  specification",
         "Unfolded, this is the form of a gadget\n  specification in `Circuit.lean`"),
        # step citations of the current paper (the docstrings cite an earlier step layout)
        ("(`lem:observer`, Steps 1 and 3, \"evaluate the rank circuit on ...\")",
         "(the rank evaluations of `lem:observer`, Step 2, and of `thm:D`,\nSteps 2 and 4)")],
    "BoolAlg.Arith": [
        ("**Truncated subtraction** (`lem:observer`, Step 3; `thm:D`, Step 2)",
         "**Truncated subtraction** (`lem:observer`, Step 2; `thm:D`, Step 2)"),
        ("**Comparison** (`lem:observer`, Steps 1 and 4; `thm:D`, Step 4)",
         "**Comparison** (`lem:augment`, Step 3; `lem:oneupdate`, Step 2; `thm:D`, Step 4)"),
        ("**Equality** (`lem:observer`, Step 1)",
         "**Equality** (`lem:observer`, Step 2; `cor:transversal`, Step 2)")],
    "BoolAlg.Bits": [
        ("(`lem:observer`, Step 2 \"its element of least index\" and Step 4\n"
         "\"the sink of least index ..., then predecessors of least index\")",
         "(`lem:augment`, Step 1, \"the sink of least index in the first layer\n"
         "containing a sink, the predecessors of least index\")")],
    "BoolAlg.Count": [
        ("**Sum of `r` numbers** of width `w` (`lem:observer`, Step 3): on",
         "**Sum of `r` numbers** of width `w`: on"),
        ("(`lem:observer`, Step 3, \"an independence\ntest `[r_{N_G}(J) = |J|]`\"; `cor:transversal`, Step 3)",
         "(`lem:observer`, Step 2;\n`cor:transversal`, Step 2)")],
    "BoolAlg.ExchangeBits": [
        ("(Step 3 of the proof of `lem:observer`)",
         "(`lem:augment`, Steps 1 and 3)")],
    "BoolAlg.Rel": [
        ("* **Warshall's algorithm** (`warshallB`, `2r³` gates, the count of `lem:observer`): one round",
         "* **Warshall's algorithm** (`warshallB`, `2r³` gates): one round"),
        ("gates), the reflexive transitive closure (`rtcV_eq_true_iff`, `Relation.ReflTransGen`).",
         "gates), the reflexive transitive closure (`rtcV_eq_true_iff`, `Relation.ReflTransGen`).\n"
         "  Run on the bits `[W ≤ t]`, `warshallV` gives the bits of the Floyd–Warshall algorithm of\n"
         "  `lem:oneupdate`, Step 2 (`Rainbow/Events.lean`)."),
        ("/-- **Warshall's algorithm** (`lem:observer`, Step 2, \"Warshall's algorithm closes them\n"
         "transitively with `2m³` gates\"): `2r³` gates;",
         "/-- **Warshall's algorithm**: `2r³` gates;")],
    "Rainbow.POSL": [
        ("`N_G = M` (Lemma `lem:observer`, Step 5)",
         "`N_G = M` (Proposition `prop:posl`, Step 4)")],
    "Rainbow.POSLRank": [
        ("Lemma `lem:observer`, Steps 1 to 3, the mathematical content",
         "Lemma `lem:observer`, Steps 1 and 2, the mathematical content"),
        ("* `mem_POG_iff` (Step 1): `f ∈ PO_G` iff",
         "* `mem_POG_iff` (Definition `def:posl`): `f ∈ PO_G` iff"),
        ("* `uG_lt_uG_iff` (Step 2): at `G = G_t`",
         "* `uG_lt_uG_iff` (Step 1): at `G = G_t`"),
        ("**The rank of `N(t)`** (Lemma `lem:observer`, Step 3)",
         "**The rank of `N(t)`** (Lemma `lem:observer`, Step 2)"),
        ("**The rank of `N_G` read from `G`** (Lemma `lem:observer`, Step 3)",
         "**The rank of `N_G` read from `G`** (Lemma `lem:observer`, Step 2)"),
        ("`PO_G` from rank queries (Lemma `lem:observer`, Step 1)",
         "`PO_G` from rank queries (Definition `def:posl`)"),
        ("read from `G` (Lemma `lem:observer`, Step 2): at",
         "read from `G` (Lemma `lem:observer`, Step 1): at")],
    "Rainbow.PossiblyOptimal": [
        ("  minimum base of some `u` with `|u_e - v_e| ≤ t/2` for every `e`; are equivalent.",
         "  minimum base of some `u` with `|u_e - v_e| ≤ t/2` for every `e`; are equivalent.\n"
         "  Conditions (1), (2) and (5) are items 1 to 3 of the proposition."),
        ("minimum base for some `u` with `‖u - v‖_∞ ≤ t/2`. -/",
         "minimum base for some `u` with `‖u - v‖_∞ ≤ t/2`.  Conditions (1), (2) and (5) are\n"
         "items 1 to 3 of Proposition `prop:pos`. -/")],
    "Rainbow.TheoremD": [
        ("* Step 4 (`minCommonBaseWeight_pad`)", "* Steps 4 and 5 (`minCommonBaseWeight_pad`)"),
        ("* The circuit of Step 4 (`negNegCircuit`", "* The circuit of Step 5 (`negNegCircuit`"),
        ("/-! ### Step 4: common independent sets as common bases of the padded matroids -/",
         "/-! ### Steps 4 and 5: common independent sets as common bases of the padded matroids -/"),
        ("**Theorem `thm:D`, Step 4.**", "**Theorem `thm:D`, Steps 4 and 5.**"),
        ("/-! ### The circuit of Step 4 -/", "/-! ### The circuit of Step 5 -/"),
        ("/-- The circuit of Step 4 (`negNegB`)", "/-- The circuit of Step 5 (`negNegB`)")],
    "Rainbow.Defs": [
        ("`greedy_intersection.tex`, Sections 4 and 5.  This module fixes the objects that every module\n"
         "of the Phase 2 development refers to.",
         "Sections 4 and 5 of the paper.  This module fixes the objects that every module on\n"
         "rainbow bases refers to."),
        ("Conventions, as in Phase 1:", "Conventions:"),
        ("weights of Phase 1)", "weights of `Matroid.lean`)")],
    "Subtractionfree": [
        ("/-- The circuit of Corollary F: the lattice circuits, inlined, then summed. -/",
         "/-- The lattice circuits, inlined, then summed. -/"),
        ("**Corollary F, upper bound, circuit form.**", "**Upper bound, circuit form.**"),
        ("/-! ### Corollary F, with `Mon` -/", "/-! ### Upper bound with `Mon` -/"),
        ("**Corollary F, upper bound.**", "**Upper bound.**"),
        ("/-! ### Corollary F, lower bound, from Jukna, Seiwert and Sergeev -/",
         "/-! ### Lower bound, from Jukna, Seiwert and Sergeev -/"),
        ("**Corollary F, lower bound.**", "**Lower bound.**")],
    "GapSum": [
        ("**The threshold integral, as a gap sum** (`eq:gap-sum`):",
         "**The sum of Definition 2**:"),
        ("**Lemma `lem:bit` (exact membership at amplitude).**",
         "**Exact membership at amplitude** (Lemma `lem:bit`).")],
    "Counting": [
        ("**Corollary D, counting form.**", "**Corollary 27, counting form.**"),
        ("**Corollary D.**", "**Corollary 27, conditional form.**")],
}
