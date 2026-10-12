# E4: further matroid classes (Corollary `cor:classes`, item 2)

Modules: `SignedTropical/Classes/Dual.lean`, `SignedTropical/Classes/Field.lean` and
`SignedTropical/Classes/Rational.lean`, namespace `SignedTropical.Classes`.  All three build
with `lake build SignedTropical.Classes.<Module>` with zero errors and zero warnings.  No
`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
`#print axioms` of every theorem listed below reports only `propext`, `Classical.choice` and
`Quot.sound`.  No external result enters as a hypothesis.

Scope.  The assignment replaces the general argument of `cor:classes` item 2 (simulation of
polynomial-time computation by circuits, out of scope) by explicit Boolean rank circuits for
concrete classes, each composed with Theorem A (`theoremA`, `TheoremA.lean`): duals
(Section 1.1), matroids represented over a finite field (Section 1.2) and matroids
represented over `ℚ` by integer matrices (Section 1.3, the optional item).  Graphic and
cographic matroids were reassigned to the coordinator (`Classes/Graphic.lean`, not part of
E4).  Transversal matroids and gammoids are assigned to a later agent.

Conventions, as in Phase 1.  A matroid on `E = {0, ..., m-1}` is `M : Matroid (Fin m)` with
`M.E = Set.univ`.  For `S ⊆ E`, `r(S)` is `M.eRk S` (in `ℕ∞`) or `rk M S` (in `ℕ`), and the
rank is `k = r(E)` (`rank M`).  A Boolean circuit `B : Circuit BoolOp m` *outputs `r(S)` in
binary* if `bitsVal (B.eval boolInterp 1_S) = r(S)` for every `S`, where `1_S` is the
indicator vector (`indicator S`) and `bitsVal` reads a list of bits least significant first;
this is the hypothesis of `theoremA`.  The size of a circuit is its number of gates.
`⌈log₂(n+1)⌉` is `Nat.size n`.  `h_M(w) = max_{B base} w(B)` is `maxBasisWeight M w`.  The
dual `M✶` is Mathlib's `Matroid.dual`.


## 1. Results and proofs

### 1.1 Duality (`Classes/Dual.lean`)

**Lemma 1 (rank of the dual), `rk_dual`.**  Let `M` be a matroid on `E = Fin m` with ground
set `E`.  For every `S ⊆ E`, `r✶(S) + r(E) = r(E \ S) + |S|`, where `r✶` is the rank function
of `M✶`.

*Proof.*  Step 1, Mathlib's `Matroid.eRk_dual_add_eRank` gives this identity in `ℕ∞` with
`M.eRank` for `r(E)` and `S.encard` for `|S|`.  Step 2, all terms are finite, so it holds in
`ℕ`.  ∎

**Construction (`dualRankCircuit B k`).**  Input: a Boolean circuit `B` on `m` inputs and a
number `k` (used with `k = r(E)`).  Put `W = ⌈log₂(m+1)⌉`.

1. One gate: the constant `1 = ¬0`.
2. `m` gates: the negated inputs `¬x_e`; then `B` on them, `s` gates.
3. A `W`-bit counter (`countB` of `Binary.lean`) that starts at the `W` bits of
   `c₀ = 2^W - (k mod 2^W)` (bit `j` is read from the wire `1` if bit `j` of `c₀` is `1` and
   from the constant source otherwise, no gates, `constBits`) and adds the `m` input bits one
   ripple-carry increment at a time, `11 W` gates per input bit.
4. A `W`-bit ripple-carry adder (`rcaB`) that adds the `W` low bits of the output of `B`
   (truncated or padded with the constant `0`, `fit`), `11 W` gates.

**Lemma 2 (size and value), `dualRankCircuit_spec`, `dualRankCircuit_size`.**  The circuit
has exactly `s + m + 1 + 11 (m+1) ⌈log₂(m+1)⌉` gates, `s` the size of `B`, and on input `x` it
outputs the `W` low bits of `2^W - (k mod 2^W) + |{e : x_e = 1}| + bitsVal(B(¬x))`.

*Proof.*  Step 1, size: the gate lists of the four parts have lengths `1`, `m + s`, `11 W m`
and `11 W` (`mapB_spec`, `length_inline`, `countB_spec`, `rcaB_spec`).  Step 2, value: the
counter carries `ofNat_W(c₀ + |{e : x_e = 1}|)` (`countB_spec`, `bitRep_constBits`); the
adder adds `ofNat_W(bitsVal(B(¬x)))` (`bitRep_fit`) with carry-in `0`, and `W`-bit addition is
addition modulo `2^W` (`rcaV_bitsOf`, `ofNat_add_ofNat_add_false`).  ∎

**Theorem 3 (duality, Boolean rank circuits), `dualRankCircuit_rank`, `dual_rankCircuit`.**
Let `M` be a matroid on `E = Fin m` with ground set `E`.  If a Boolean circuit `B` of size `s`
outputs `r(S)` in binary for every `S ⊆ E`, then the Boolean circuit
`dualRankCircuit B (rank M)`, of size `s + m + 1 + 11 (m+1) ⌈log₂(m+1)⌉`, outputs `r✶(S)` in
binary for every `S ⊆ E`.

*Proof.*  Step 1, by Lemma 2 the output value is
`(2^W - (k mod 2^W) + |{e : (1_S)_e = 1}| + bitsVal(B(¬1_S))) mod 2^W`.  Step 2, `¬1_S` is
`1_{E \ S}`, so `bitsVal(B(¬1_S)) = r(E \ S)`, and `|{e : (1_S)_e = 1}| = |S|`.  Step 3,
`r✶(S) ≤ |S| ≤ m < 2^W`.  Step 4, by Lemma 1 and `k = 2^W ⌊k/2^W⌋ + (k mod 2^W)`,
`2^W - (k mod 2^W) + |S| + r(E \ S) = r✶(S) + 2^W (1 + ⌊k/2^W⌋)`, so the value is
`r✶(S) mod 2^W = r✶(S)`.  ∎

**Theorem 4 (duality, signed tropical circuits), `theoremA_dual`.**  Under the hypotheses of
Theorem 3, `h_{M✶}` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size at
most `3 m s' + m L + 9 m² + 4 m + 4 L + 1`, where
`s' = s + m + 1 + 11 (m+1) ⌈log₂(m+1)⌉` and `L = ⌈log₂(k✶+1)⌉` for the rank `k✶` of `M✶`.

*Proof.*  Step 1, `M✶` has ground set `E` (`Matroid.dual_ground`).  Step 2, Theorem A applied
to `M✶` and the circuit of Theorem 3.  ∎

### 1.2 Matroids represented over a finite field (`Elimination.lean`, `Classes/Field.lean`)

Since the consolidation of 2026-10-12 the column matroid and the elimination below are in
`Elimination.lean`, shared with `Binary.lean`: `binaryMatroid A` is `colMatroid A` over `GF(2)`
by definition, and the Boolean elimination of `Binary.lean` is read through `elimK`
(`zst_elimV`).  `Classes/Field.lean` keeps the one-hot codes, the rank circuit and Theorem A.

Notation.  `K` is a field, `A ∈ K^{r × m}`, and `A_{·,e}` is column `e` (`colK A e`).  For
the circuits `K` is finite with `q = |K|` elements, and `q ≥ 2` (`Fintype.one_lt_card`).

**Definition (column matroid), `colMatroid A`.**  The matroid on `E = Fin m` with ground set
`E` whose independent sets are the sets `I` of columns that are linearly independent over `K`
(`colMatroid_indep`).  It is built with `IndepMatroid.ofFinset`.  Augmentation
(`colK_indep_aug`): if `I, J` are independent with `|I| < |J|` and no `e ∈ J \ I` keeps
`I + e` independent, every column of `J` lies in the span of the columns of `I`, so
`|J| = dim span J ≤ dim span I = |I|`, a contradiction.  This generalizes `binaryMatroid` of
`Binary.lean`, which is not edited: over `GF(2)` the two coincide
(`colMatroid_eq_binaryMatroid`).

**Lemma 5 (rank), `eRk_colMatroid`, `eRk_colMatroid_eq_rank`.**  For every `S ⊆ E`, the rank
of `S` in the column matroid is the dimension of the span of the columns in `S`, which is
Mathlib's `Matrix.rank` of the column submatrix `A.submatrix id (↑) : K^{r × S}`.

*Proof.*  Step 1, take a basis `I` of `S` in the matroid.  Step 2, every column of `S` lies in
the span of the columns of `I`: otherwise `I + e` would be independent, against maximality.
Step 3, so `span S = span I` and `dim span S = |I| = r(S)`.  Step 4, `Matrix.rank` is the
dimension of the span of the columns (`Matrix.rank_eq_finrank_span_cols`).  ∎

**Elimination without branching, on values.**  The state has `r` slots; slot `p` has an
occupancy bit `f_p` and a vector `b_p ∈ K^r`, all empty at the start (`initK`).  Column `e`
with input bit `x_e` is processed by (`colStepK`):

1. `v_i = x_e A_{i,e}` (`colValK`);
2. for `p = 1, ..., r`: `v_i ← v_i - c_p b_{p,i}`, where `c_p = v_p` if `f_p` and `c_p = 0`
   otherwise (`redStepK`, `reduceK`);
3. `ℓ_p = [v_p ≠ 0 and v_q = 0 for all q < p]` (`leadV` of the nonzero pattern `nzK v`),
   `f_p ← f_p ∨ ℓ_p` and `b_{p,i} ← v_i v_p⁻¹` if `ℓ_p`, `b_{p,i}` otherwise (`insertK`).

`elimK A x` runs the columns `e = 0, ..., m-1` in order.

**Lemma 6 (one column), `colStepK_inv`.**  Call a state *echelon* if every occupied slot `p`
has `b_{p,p} = 1` and `b_{p,q} = 0` for `q < p` (`EchelonK`).  If the state is echelon and its
stored vectors span the columns of a set `T`, then after column `e` the state is echelon and
its stored vectors span the columns of `T + e` if `x_e = 1`, of `T` if `x_e = 0` (`InvK`).

*Proof.*  Step 1, reduction changes `v` by an element of the span of the stored vectors
(`reduceK_sub_mem`).  Step 2, after the reduction `v_p = 0` at every occupied slot `p`
(`reduceK_occ`): the step at slot `p` sets `v_p = 0` because `b_{p,p} = 1`, and the later
steps at slots `q > p` do not change coordinate `p` because `b_{q,p} = 0`.  Step 3, if the
remainder `v` is `0` the state does not change, and when `x_e = 1` Step 1 puts column `e` in
the span of the stored vectors, so the span is unchanged.  Step 4, otherwise let `q` be the
least index with `v_q ≠ 0`.  Then `x_e = 1` (for `x_e = 0` the remainder is `0`,
`reduceK_zero`), slot `q` is empty by Step 2, `ℓ = 1_q`, and the new vector `v_q⁻¹ v` has a
`1` at `q` and zeros before `q`, so the state stays echelon.  Its span is
`span(stored ∪ {v_q⁻¹ v}) = span(stored ∪ {v}) = span(stored ∪ {A_{·,e}})` by Step 1
(`span_insert_smul`, `span_insert_congrK`), the span of the columns of `T + e`.  ∎

**Lemma 7 (the elimination computes the rank), `card_occ_elimK`.**  For every `S ⊆ E`, the
number of occupied slots of `elimK A 1_S` is `dim span{A_{·,e} : e ∈ S}`.

*Proof.*  Step 1, by Lemma 6 and induction over the columns (`foldl_colStepK_inv`), the final
state is echelon and its stored vectors span the columns of `S`.  Step 2, echelon vectors are
linearly independent (`linearIndepOn_of_echelonK`): in a vanishing combination, the least
occupied index with a nonzero coefficient sees only its own vector, whose coordinate there is
`1`.  So the number of occupied slots is the dimension of the span (`card_occ_of_invK`).  ∎

**One-hot codes.**  A value `U(x) ∈ K` is carried by `q` operands `u_a`, `a ∈ K`, where `u_a`
carries `[U(x) = a]` (`OH`).  Gadgets, with their exact gate counts:

* a binary operation `g : K × K → K` (`op2B`), `2 q²` gates: output `c` is
  `⋁_{g(a,b) = c} (u_a ∧ v_b)`, one conjunction and one disjunction per pair (`orAndB`);
* inversion (`OH.inv`), no gates: the code of `U⁻¹` at `a` is the code of `U` at `a⁻¹`
  (Lean's `0⁻¹ = 0` keeps this a permutation);
* masking `F ? V : 0` (`maskB`), `q` gates: `¬F ∨ v_0` at `0`, `F ∧ v_a` at `a ≠ 0`;
* selection `L ? U : V` (`muxB`), `3 q` gates: `(L ∧ u_a) ∨ (¬L ∧ v_a)`;
* the code of `x_e A_{i,e}` (`colOH`), no gates: at `a = A_{i,e}` it is `1` if `a = 0` and
  `x_e` otherwise; at `a ≠ A_{i,e}` it is `¬x_e` if `a = 0` and `0` otherwise.

**Lemma 8 (the rank circuit), `fieldRankCircuit_spec`, `fieldRankCircuit_rank`.**  Let `K` be
finite.  The Boolean circuit `fieldRankCircuit A` has exactly
`m (6 q² r² + 3 q r² + r² + q r + 6 r + 1) + 11 r ⌈log₂(r+1)⌉ + 1` gates and outputs, for
every `S ⊆ E`, the number of occupied slots of `elimK A 1_S` in binary, which is the rank of
`S` in `colMatroid A`.

*Proof.*  Step 1, the circuit: one gate for the constant `1`; the empty state needs no gates
(the code of `0` is the wire `1`); per column (`colStepKB`), `1` gate for `¬x_e`, the
reduction `r (1 + q + 4 r q²)` gates (per slot `¬f_p`, the mask `c_p`, and per entry one
product and one difference, `redKB`, `axpyKB`), the bits `[v_p ≠ 0]` `r` gates (negation of
the code at `0`), the leading bits `r (r + 2)` gates (`leadB`), the occupancy bits `r` gates,
and the update `r (1 + r (2 q² + 3 q))` gates (per slot `¬ℓ_p`, and per entry the product
`v_i v_p⁻¹` and a selection, `updKB`), in total `6 q² r² + 3 q r² + r² + q r + 6 r + 1`
(`colCostK`, `colStepKB_length`); finally a counter of the `r` occupancy bits with
`⌈log₂(r+1)⌉` bits, `11 r ⌈log₂(r+1)⌉` gates (`countB`).  Step 2, by induction over the
gadgets (`colStepKB_spec`, `elimKB_spec`), the operands of the state carry the state of
`elimK` (`StKDen`).  Step 3, the count is exact since it is at most `r < 2^{⌈log₂(r+1)⌉}`.
Step 4, Lemma 7 and Lemma 5.  ∎

**Lemma 9 (explicit polynomials), `fieldSize_le`, `theoremA_fieldSize_le`.**  For `q ≥ 2`
and all `m, r`: the size `s` of Lemma 8 is at most `8 q² (m+1) (r+1)²`; and if `k ≤ r` then
`3 m s + m ⌈log₂(k+1)⌉ + 9 m² + 4 m + 4 ⌈log₂(k+1)⌉ + 1 ≤ 25 q² (m+1)² (r+1)²`.

*Proof.*  Step 1, `⌈log₂(r+1)⌉ ≤ r` and `⌈log₂(k+1)⌉ ≤ k ≤ r`.  Step 2, write `q = q' + 2`;
after these replacements the right side minus the left side is an explicit polynomial in
`m, q', r` with nonnegative coefficients (written out in the Lean proof and checked by
`ring`).  ∎

**Theorem 10 (finite fields, Boolean rank circuits), `field_rankCircuit`.**  Let `K` be a
finite field with `q` elements and `A ∈ K^{r × m}`.  There is a Boolean circuit of size
exactly `m (6 q² r² + 3 q r² + r² + q r + 6 r + 1) + 11 r ⌈log₂(r+1)⌉ + 1`, which is at most
`8 q² (m+1) (r+1)²`, that outputs in binary, for every `S ⊆ E`, Mathlib's `Matrix.rank` of
the column submatrix of `A` on `S`; this number is also the rank of `S` in `colMatroid A`.

*Proof.*  Step 1, `fieldRankCircuit A` (with a decidable equality on `K` chosen
classically).  Step 2, size by Lemma 8 and Lemma 9.  Step 3, value by Lemma 8 and Lemma 5.  ∎

**Theorem 11 (finite fields, signed tropical circuits), `theoremA_field`.**  Let `K` be a
finite field with `q` elements, `A ∈ K^{r × m}` and `M = colMatroid A` of rank `k`.  Then
`h_M` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size at most
`3 m s + m L + 9 m² + 4 m + 4 L + 1`, where `s` is the size in Theorem 10 and
`L = ⌈log₂(k+1)⌉`; this is at most `25 q² (m+1)² (r+1)²`.  For `q = 2` the last bound is the
bound `100 (m+1)² (r+1)²` of `cor:classes` item 1.

*Proof.*  Step 1, Theorem A applied to `M` and `fieldRankCircuit A` (Lemma 8).  Step 2,
`k ≤ r` (`rank_colMatroid_le`: the span of the columns lies in `K^r`) and Lemma 9.  ∎

### 1.3 Matroids represented over `ℚ` (`Classes/Rational.lean`)

Notation.  `A ∈ ℤ^{r × m}` with `|A_{ij}| < 2^b` for all entries (bit length at most `b`).
The matroid is `colMatroid A_ℚ`, the column matroid of `A` read over `ℚ`; scaling each column
of a rational matrix by a common denominator of its entries does not change the column
matroid, so every matroid represented over `ℚ` has such a representation (this remark is not
formalized).  For a prime `p`, `A_p` is `A` read in `ZMod p`, and `rank_p(S)` is the rank of
`S` in `colMatroid A_p` (`modRk A p S`, defined as `0` when `p` is not prime).  `A_I` is the
`r × I` submatrix of the columns in `I` (`colsOf`) and `G_I = A_Iᵀ A_I` its Gram matrix
(`gram A I`).

**Lemma 12 (a small prime that does not divide `D`), `exists_prime_not_dvd`.**  Let `D` be a
nonzero integer with `|D| < 2^L`, and `N ≥ 1` with `(N+1) N^L < 2^N`.  Then some prime
`p ≤ N` does not divide `D`.

*Proof.*  Suppose every prime `p ≤ N` divides `D`.  Step 1, the product of these primes
divides `|D|` (`Finset.prod_primes_dvd`) and is at least `2^{π(N)}`, where `π(N)` is their
number; so `2^{π(N)} ≤ |D| < 2^L` and `π(N) < L`.  Step 2,
`lcm(1, ..., N) = ∏_{p ≤ N} p^{⌊log_p N⌋} ≤ N^{π(N)} ≤ N^L` (Mathlib's
`Nat.lcmUpto_eq_prod_pow_log`).  Step 3, Chebyshev's bound `2^N ≤ (N+1) lcm(1, ..., N)`
(Mathlib's `Chebyshev.two_pow_le_mul_lcmUpto`) gives `2^N ≤ (N+1) N^L`, against the
hypothesis.  ∎

**Lemma 13 (the bound on the primes), `primeBound_spec`.**  Let `N = 2^{2s+1}` with
`s = ⌈log₂(L+2)⌉` (`primeBound L`).  Then `N ≥ 1`, `(N+1) N^L < 2^N` and `N ≤ 8 (L+1)²`.

*Proof.*  Step 1, `L + 1 < 2^s ≤ 2 (L+1)` and `s + 1 ≤ 2^s`.  Step 2, `N = 2 · 2^s · 2^s`, so
`N ≤ 8 (L+1)²`.  Step 3, `(N+1) N^L ≤ 2 N^{L+1} = 2^{(2s+1)(L+1)+1}`, and
`(2s+1)(L+1) + 1 < N` by Step 1, so `(N+1) N^L < 2^N`.  ∎

**Lemma 14 (reduction modulo `p` does not increase the rank), `linearIndepOn_rat_of_zmod`,
`modRk_le`.**  Let `p` be prime and `I ⊆ E`.  If the columns of `A_p` in `I` are linearly
independent over `ZMod p`, the columns of `A` in `I` are linearly independent over `ℚ`.
Hence `rank_p(S) ≤ rank_ℚ(S)` for every `S ⊆ E`.

*Proof.*  Step 1, for integer vectors, independence over `ℚ` is independence over `ℤ`
(Mathlib's `LinearIndependent.iff_fractionRing`); take a relation
`Σ_{i ∈ t} g_i A_{·,i} = 0` with `g_i ∈ ℤ`, `t ⊆ I`, and suppose some `g_i ≠ 0`.  Step 2,
`g = d g'` with `d = gcd(g) ≠ 0` and `gcd(g') = 1` (`Finset.extract_gcd`), and
`Σ g'_i A_{·,i} = 0`.  Step 3, reduced modulo `p` this is a relation between the columns of
`A_p`, so `p` divides every `g'_i` and hence `gcd(g') = 1`, a contradiction.  Step 4, a basis
of `S` modulo `p` is independent over `ℚ` and contained in `S`, so
`rank_p(S) ≤ rank_ℚ(S)`.  ∎

**Lemma 15 (the Gram determinant), `gram_det_ne_zero`, `linearIndepOn_zmod_of_not_dvd`,
`natAbs_det_gram_le`, `natAbs_det_gram_lt`.**  Let `I ⊆ E`.
(a) If the columns of `A` in `I` are independent over `ℚ`, then `det G_I ≠ 0`.
(b) If `p` is prime and does not divide `det G_I`, the columns of `A_p` in `I` are
independent over `ZMod p`.
(c) `|det G_I| ≤ |I|! (r 4^b)^{|I|}`, and if `|I| ≤ r` then `|det G_I| < 2^{2 r (r+b) + 1}`.

*Proof.*  Step 1, (a): if `det G_I = 0`, some `v ≠ 0` has `G_I v = 0` over `ℚ`
(`Matrix.exists_mulVec_eq_zero_iff`); then `|A_I v|² = vᵀ G_I v = 0`, so `A_I v = 0`, a
nontrivial relation between the columns.  Step 2, (b): `det G_I` is nonzero modulo `p`, so
if `A_I g = 0` modulo `p` then `G_I g = A_Iᵀ (A_I g) = 0` and `g = 0`.  Step 3, (c): every
entry of `G_I` is a sum of `r` products of two entries of `A`, so its absolute value is at
most `r 4^b`, and Mathlib's `Matrix.det_le` bounds `|det G_I|` by `|I|! (r 4^b)^{|I|}`.
With `k = |I| ≤ r`, `k! (r 4^b)^k ≤ (r · r · 4^b)^k ≤ (4^r 4^b)^k ≤ 4^{r(r+b)}`, using
`k! ≤ k^k` and `r² ≤ 4^r`.  ∎

**Theorem 16 (the rank over `ℚ` is the largest rank modulo a small prime),
`exists_le_modRk`, `rk_rat_eq_max`.**  Let `N = primeBound (2 r (r+b) + 1)`, so
`N ≤ 32 (r (r+b) + 1)²`.  For every `S ⊆ E`, `rank_ℚ(S) = max_{p ≤ N prime} rank_p(S)`
(the maximum of an empty family read as `0`).

*Proof.*  Step 1, `≥` is Lemma 14.  Step 2, for `≤` take a basis `I` of `S` over `ℚ`; then
`|I| = rank_ℚ(S) ≤ r` (`rank_colMatroid_le`), and `D = det G_I` is a nonzero integer with
`|D| < 2^L`, `L = 2 r (r+b) + 1` (Lemma 15 (a), (c)).  Step 3, Lemmas 12 and 13 give a prime
`p ≤ N` that does not divide `D`.  Step 4, `I` is independent modulo `p` (Lemma 15 (b)), so
`rank_p(S) ≥ |I| = rank_ℚ(S)`.  ∎

**Lemma 17 (the rank circuit over `ℚ`), `ratRankCircuit`, `ratRankCircuit_spec`.**  Let
`W = ⌈log₂(r+1)⌉ + 1`.  For every `N`, the Boolean circuit `ratRankCircuit A N` has at most
`(N+1) (8 N² (m+1) (r+1)² + 15 W + 10)` gates and outputs in binary, for every `S ⊆ E`,
`max_{p ≤ N prime} rank_p(S)`.

*Proof.*  Step 1, the construction (`maxRankB`): for the primes `p ≤ N` in increasing order,
inline the rank circuit modulo `p` (`primeRankCircuit`, the circuit of Lemma 8 for `A_p`, of
size at most `8 p² (m+1) (r+1)²` by Lemma 9 with `q = p`), pad its output to `W` bits with the
constant `0` (`fit`), and replace the running maximum, a `W`-bit number starting at `0`, by
the signed maximum of `Converse.lean` (`bvGad W .max`, `15 W + 10` gates).  Step 2, all values
are at most `r < 2^{W-1}` (`bitsVal_primeRankCircuit_le`), and on such numbers the signed
maximum of `W`-bit two's complement numbers is the maximum (`bvMax_ofNat`); by induction over
the primes (`maxRankB_spec`, `inline_input_spec`) the output is the maximum.  Step 3, there
are at most `N + 1` primes, each costing at most `8 N² (m+1) (r+1)² + 15 W + 10` gates.  ∎

**Theorem 18 (`ℚ`, Boolean rank circuits), `rat_rankCircuit`.**  Let `A ∈ ℤ^{r × m}` with
`|A_{ij}| < 2^b` for all entries.  A Boolean circuit of size at most
`2^19 (m+1) (r+1)² (r (r+b) + 1)^6` outputs in binary, for every `S ⊆ E`, Mathlib's
`Matrix.rank` over `ℚ` of the column submatrix of `A` on `S`; this number is also the rank of
`S` in `colMatroid A_ℚ`.

*Proof.*  Step 1, Lemma 17 with `N = primeBound (2 r (r+b) + 1)` and Theorem 16.  Step 2,
`ratSize_le`: with `T = r (r+b) + 1` and `N ≤ 32 T²`, `N + 1 ≤ 33 T²`,
`8 N² ≤ 8192 T⁴`, and `15 W + 10 ≤ 25 (r+1) ≤ 25 T⁴ (m+1) (r+1)²`, so the size is at most
`33 · 8217 · T^6 (m+1) (r+1)² ≤ 2^19 (m+1) (r+1)² T^6`.  Step 3, Lemma 5 converts the rank to
`Matrix.rank`.  ∎

**Theorem 19 (`ℚ`, signed tropical circuits), `theoremA_rat`.**  Under the hypotheses of
Theorem 18, with `M = colMatroid A_ℚ`, `h_M` is computed at every `w ∈ ℝ^m` by a signed
tropical circuit of size at most `2^21 (m+1)² (r+1)² (r (r+b) + 1)^6`.

*Proof.*  Step 1, Theorem A applied to the circuit of Theorem 18.  Step 2,
`theoremA_ratSize_le`: with `s ≤ 2^19 (m+1) (r+1)² T^6` and `L = ⌈log₂(k+1)⌉ ≤ r`,
`3 m s ≤ 3 · 2^19 (m+1)² (r+1)² T^6` and
`m L + 9 m² + 4 m + 4 L + 1 ≤ 9 (m+1)² (r+1)² ≤ 2^19 (m+1)² (r+1)² T^6`.  ∎


## 2. Correspondence table

| Paper | Lean names | Module | Status |
|:--|:--|:--|:--|
| `cor:classes` item 2, duals: `r✶(S) = |S| + r(E \ S) - r(E)` | `rk_dual` | `Classes/Dual.lean` | proved |
| `cor:classes` item 2, duals: Boolean rank circuit of size `s + m + 1 + 11 (m+1) ⌈log₂(m+1)⌉` | `dualRankCircuit`, `dualRankCircuit_spec`, `dualRankCircuit_size`, `dualRankCircuit_rank`, `dual_rankCircuit` | `Classes/Dual.lean` | proved |
| `cor:classes` item 2, duals: signed tropical circuit for `h_{M✶}` | `theoremA_dual` | `Classes/Dual.lean` | proved |
| `cor:classes` item 2, finite fields: column matroid and its rank | `colMatroid`, `colMatroid_indep`, `eRk_colMatroid`, `eRk_colMatroid_eq_rank` (`Elimination.lean`); `rank_colMatroid_le` | `Elimination.lean`, `Classes/Field.lean` | proved |
| `cor:classes` item 2, finite fields: elimination without branching | `elimK`, `colStepK_inv`, `card_occ_elimK` | `Elimination.lean` | proved |
| `cor:classes` item 2, finite fields: Boolean rank circuit, size `≤ 8 q² (m+1) (r+1)²` | `fieldRankCircuit`, `fieldRankCircuit_spec`, `fieldRankCircuit_rank`, `fieldSize_le`, `field_rankCircuit` | `Classes/Field.lean` | proved |
| `cor:classes` item 2, finite fields: signed tropical circuit, size `≤ 25 q² (m+1)² (r+1)²` | `theoremA_fieldSize_le`, `theoremA_field` | `Classes/Field.lean` | proved |
| `cor:classes` item 2, over `ℚ`: small primes (Chebyshev) | `exists_prime_not_dvd`, `primeBound`, `primeBound_spec` | `Classes/Rational.lean` | proved |
| `cor:classes` item 2, over `ℚ`: reduction modulo `p`, Gram determinant | `linearIndepOn_rat_of_zmod`, `gram`, `gram_det_ne_zero`, `linearIndepOn_zmod_of_not_dvd`, `natAbs_det_gram_le`, `natAbs_det_gram_lt` | `Classes/Rational.lean` | proved |
| `cor:classes` item 2, over `ℚ`: rank over `ℚ` = largest rank modulo `p ≤ N` | `modRk`, `modRk_le`, `exists_le_modRk`, `rk_rat_eq_max` | `Classes/Rational.lean` | proved |
| `cor:classes` item 2, over `ℚ`: Boolean rank circuit, size `≤ 2^19 (m+1) (r+1)² (r(r+b)+1)^6` | `primeRankCircuit`, `maxRankB`, `ratRankCircuit`, `ratRankCircuit_spec`, `ratSize_le`, `rat_rankCircuit` | `Classes/Rational.lean` | proved |
| `cor:classes` item 2, over `ℚ`: signed tropical circuit, size `≤ 2^21 (m+1)² (r+1)² (r(r+b)+1)^6` | `theoremA_ratSize_le`, `theoremA_rat` | `Classes/Rational.lean` | proved |
| `cor:classes` item 2, graphic and cographic | (coordinator, `Classes/Graphic.lean`) | | not in E4 |
| `cor:classes` item 2, transversal matroids, gammoids | | | later agent |
| `cor:classes` item 2, general polynomial-time rank oracles (Pippenger and Fischer) | | | out of scope |


## 3. Differences from the paper

1. Item 2 of `cor:classes` argues through the simulation of polynomial-time computation by
   circuits of size `O(T log T)`.  That simulation is out of scope; the formalization gives
   explicit circuits for concrete classes instead.  Proposed replacement for the list of
   `cor:classes` after item 1 (unchanged), matching what is formalized; the graphic and
   cographic item is a placeholder for the coordinator's module:

   > \item A matroid represented by an $r\times m$ matrix over a finite field with $q$
   > elements: it has a Boolean rank circuit of size
   > $m(6q^{2}r^{2}+3qr^{2}+r^{2}+qr+6r+1)+11r\lceil\log_2(r+1)\rceil+1\le8q^{2}(m+1)(r+1)^{2}$,
   > so $h_M$ has a signed tropical circuit of size at most $25q^{2}(m+1)^{2}(r+1)^{2}$.
   > \item A matroid represented over $\mathbb Q$ by an $r\times m$ integer matrix whose
   > entries have absolute value less than $2^{b}$: it has a Boolean rank circuit of size at
   > most $2^{19}(m+1)(r+1)^{2}(r(r+b)+1)^{6}$, so $h_M$ has a signed tropical circuit of size
   > at most $2^{21}(m+1)^{2}(r+1)^{2}(r(r+b)+1)^{6}$.
   > \item The dual $M^{*}$ of a matroid $M$ whose rank function is output in binary by a
   > Boolean circuit of size $s$: $M^{*}$ has a Boolean rank circuit of size
   > $s'=s+m+1+11(m+1)\lceil\log_2(m+1)\rceil$, so $h_{M^{*}}$ has a signed tropical circuit
   > of size at most $3ms'+mL^{*}+9m^{2}+4m+4L^{*}+1$, where $L^{*}$ is the number of binary
   > digits of the rank of $M^{*}$.
   > \item [Graphic and cographic matroids: placeholder.]

   Proposed proofs for these items, in the style of the proof of item 1:

   > \emph{Item 2.}  Run the elimination of item 1 over the field, each field element carried
   > by $q$ wires of which exactly one is true.  A field operation costs $2q^{2}$ gates, one
   > conjunction and one disjunction for each pair of arguments; inversion is a permutation of
   > the wires, masking by a bit costs $q$ gates and selecting between two elements $3q$.  The
   > column step computes $v_i=x_eA_{ie}$ without gates, then
   > $v\leftarrow v-[f_p]\,v_p\,b_p$ for $p=1,\ldots,r$, the leading positions $\ell_p$, the
   > bits $f_p\leftarrow f_p\vee\ell_p$ and $b_p\leftarrow\ell_p\,?\,v_p^{-1}v:b_p$, in
   > $6q^{2}r^{2}+3qr^{2}+r^{2}+qr+6r+1$ gates.  By induction on the columns, the occupied
   > slots hold vectors with leading entry $1$ at distinct positions spanning the selected
   > columns, so their number is the rank.  Counting them costs $11r\lceil\log_2(r+1)\rceil$
   > gates and the constant $1$ one gate; Theorem~\ref{thm:A} with $k\le r$ and $q\ge2$ gives
   > the second bound.

   > \emph{Item 3.}  Put $L=2r(r+b)+1$ and $N=2^{2\lceil\log_2(L+2)\rceil+1}$, so that
   > $N\le8(L+1)^{2}$ and $(N+1)N^{L}<2^{N}$.  The rank of $S$ over $\mathbb Q$ is the largest
   > rank of $S$ modulo a prime $p\le N$.  Reduction modulo $p$ does not increase the rank: a
   > rational relation between columns scales to an integer relation whose coefficients have
   > greatest common divisor $1$, and it stays nontrivial modulo $p$.  Conversely, for a
   > basis $I$ of $S$ over $\mathbb Q$ the Gram determinant $D=\det(A_I^{\mathsf T}A_I)$ is
   > a nonzero integer with $|D|\le|I|!\,(r4^{b})^{|I|}<2^{L}$.  If every prime $p\le N$
   > divided $D$, there would be fewer than $L$ of them, so
   > $\operatorname{lcm}(1,\ldots,N)\le N^{L}$, while
   > $2^{N}\le(N+1)\operatorname{lcm}(1,\ldots,N)$.  So some prime $p\le N$ does not divide
   > $D$; then $A_I^{\mathsf T}A_I$ is invertible modulo $p$ and $I$ stays independent
   > modulo $p$.  The circuit runs the circuits of item 2 for all primes $p\le N$, of sizes at
   > most $8p^{2}(m+1)(r+1)^{2}$, and keeps a running maximum in
   > $W=\lceil\log_2(r+1)\rceil+1$ bits with the signed maximum of the proof of
   > Theorem~\ref{thm:B} ($15W+10$ gates per prime), in total at most
   > $(N+1)(8N^{2}(m+1)(r+1)^{2}+15W+10)\le2^{19}(m+1)(r+1)^{2}(r(r+b)+1)^{6}$ gates.

   > \emph{Item 4.}  $r^{*}(S)=|S|+r(E\setminus S)-r(E)$.  With $W=\lceil\log_2(m+1)\rceil$,
   > one gate gives the constant $1$, $m$ negations and the given circuit give
   > $r(E\setminus S)$, a $W$-bit counter started at $2^{W}-(r(E)\bmod2^{W})$ adds the $m$
   > input bits in $11Wm$ gates, and a ripple-carry adder adds the low $W$ bits of
   > $r(E\setminus S)$ in $11W$ gates.  The arithmetic is modulo $2^{W}$ and
   > $0\le r^{*}(S)\le m<2^{W}$, so the result is $r^{*}(S)$.

   The general statement ("every matroid whose rank is computed in time polynomial in $m$
   and in the length of a fixed description") can stay as an unformalized remark citing
   Pippenger and Fischer, and transversal matroids and gammoids await the matroid
   intersection circuit.  The introduction sentence "and every class with a polynomial-time
   rank oracle on a fixed description has polynomial-size rank circuits
   (Corollary~\ref{cor:classes})" would then read "the same elimination over a field with
   $q$ elements costs $O(q^{2}mr^{2})$ gates, matroids represented over $\mathbb Q$ by
   integer matrices with entries of $b$ bits have rank circuits of size polynomial in $m$,
   $r$ and $b$, and passing to the dual costs $O(m\log m)$ gates
   (Corollary~\ref{cor:classes})".

2. The rank circuit for the dual hardwires the number `r(E)` as constant bits.  This is the
   same convention as in Theorem A, whose circuit hardwires `k`.

3. The circuit size for a field with `q` elements is polynomial in `q`, not in `log q`: the
   one-hot code is the price of making inversion free.  For a fixed field this is
   polynomial in `m` and `r`, which is what `cor:classes` needs.

4. The `ℚ` bound is explicit and polynomial, but its exponents are not optimized: the prime
   bound `N` is quadratic in `L = 2 r (r+b) + 1` (a choice of `N` of order `L log L` and
   Hadamard's inequality would lower the degree), and the circuit uses all primes `p ≤ N`
   with one-hot field arithmetic.  The paper's original route (simulation of a
   polynomial-time algorithm) gives no explicit exponent.


## 4. Module line counts

| Module | Lines |
|:--|:--|
| `SignedTropical/Classes/Dual.lean` | 231 |
| `SignedTropical/Elimination.lean` | 436 |
| `SignedTropical/Classes/Field.lean` | 646 |
| `SignedTropical/Classes/Rational.lean` | 584 |


## 5. Not done, and why

* Graphic and cographic matroids (item 3 of the assignment): reassigned to the coordinator,
  who writes `SignedTropical/Classes/Graphic.lean`.
* Transversal matroids and gammoids: assigned to a later agent with a matroid intersection
  circuit.
* The general class "rank computable in polynomial time" (simulation of Turing machines by
  circuits) is out of scope by the assignment.
