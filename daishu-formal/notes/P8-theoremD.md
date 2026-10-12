# P8: Theorem D (Theorem `thm:D`, matroid intersection)

Natural-language companion of `SignedTropical/Rainbow/TheoremDRank.lean` (phase 1, the rank
circuits of Steps 2 and 4) and `SignedTropical/Rainbow/TheoremD.lean` (phase 2, Theorem `thm:D`
itself), namespace `SignedTropical.Rainbow.TheoremD`.

Sources: `daishu/paper/greedy_intersection.tex`, Theorem `thm:D` and its proof (Section 5);
Lemma `lem:doubling` and its Lean form `Rainbow/Doubling.lean` (P1x,
`notes/P1x-partition-doubling.md`); the truncation `Rainbow/Truncation.lean`
(`notes/Truncation.md`); the Boolean library `BoolAlg` (P6a, `notes/P6a-boolalg.md`); the rank
circuit of the dual `Classes/Dual.lean` (E4), a related construction; Theorem C,
`Rainbow/TheoremCFinal.lean` (`TheoremCFinal.theoremC_final`, P7 and P6c,
`notes/P7-theoremC.md`, `notes/P6c-observer.md`) with the real-vector gadgets of
`Rainbow/OneUpdate.lean` (`TheoremC.realsR`).

Build status: `lake build SignedTropical.Rainbow.TheoremDRank` and
`lake build SignedTropical.Rainbow.TheoremD` succeed with no error and no warning.  No `sorry`,
`admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
`#print axioms` of all declarations: in `TheoremDRank` (29 declarations) the 22 theorems
depend on `propext`, `Classical.choice` and `Quot.sound`, the 7 definitions on `propext` and
`Quot.sound`; in `TheoremD` (35 declarations) every declaration depends on a subset of
`propext`, `Classical.choice`, `Quot.sound` (`maxB` on none).  Imports: `TheoremDRank` imports
`BoolAlg.Count`, `Rainbow.Doubling`, `Rainbow.Truncation`; `TheoremD` imports `TheoremDRank`
and `Rainbow.TheoremCFinal` (all finished modules).

Conventions.  `E = Fin m`; every matroid has ground set `E` (hypothesis `M.E = Set.univ`).  A
*rank circuit* of `M` is a Boolean circuit `C` on `m` inputs that outputs `r(S)` in binary from
the indicator vector of every `S ⊆ E`, in the form of the hypothesis of Theorem A:
`∀ S, (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk S`; its size is `s = C.size`.
`W = ⌈log₂(m+1)⌉` is `Nat.size m`; `popCost m = 11(2m − 1 − W) ≤ 22m` is the exact size of the
population count of `m` bits (P6a).  `N = M₁ ⊕ M₂✶` is `Doubling.double M₁ M₂`, on
`E × {1, 2} = Fin (m + m)`, with `(e, 1) = Fin.castAdd m e` and `(e, 2) = Fin.addNat e m`; for
`S ⊆ E × {1, 2}`, `A = fst S = {e : (e, 1) ∈ S}` and `B = snd S = {e : (e, 2) ∈ S}`.  The
truncation of `M` at `j` is `Trunc.truncate M j`, with rank function `min(r, j)`.  Subtraction
of natural numbers is truncated at `0`.  Every gate count is exact.  For `w ∈ ℝ^E` and
`X ⊆ E`, `w(X) = Σ_{e ∈ X} w_e`; `weight w` (`Doubling.weight`) is `w_e` on `(e, 1)` and `0` on
`(e, 2)`.  Signed tropical circuits have the gates `max`, `+`, `−` and the constant source `0`
(`STOp`, `stInterp ℝ`).


## 1. Results

### 1.1 Rank facts

**Lemma 1.**  Let `M` be a matroid on `E`.

1. `rk_le_card`: `r(S) ≤ |S|`.
2. `rk_lt_two_pow`: `r(S) < 2^W`.
3. `rank_le_card`: the rank of `M` is at most `m`.
4. `bitsVal_eq_rk`: if `C` is a rank circuit of `M`, then `bitsVal (C(1_S)) = r(S)` in `ℕ`.
5. `rank_truncate_eq_min`: if `M` has ground set `E`, the truncation at `j` has rank
   `min(r(E), j)`.

*Proof.*  Step 1, item 1 is Mathlib's `eRk_le_encard` read in `ℕ` (`coe_rk`, and the
cardinality of a finite set is its size).  Step 2, item 2: `r(S) ≤ |S| ≤ m < 2^W`
(`Nat.lt_size_self`).  Step 3, item 3: a base has `r(E)` elements (`card_base`), at most `m`.
Step 4, item 4: the map `ℕ → ℕ∞` is injective and `r(S)` read in `ℕ∞` is `M.eRk S`
(`coe_rk`).  Step 5, item 5: the truncation has ground set `E` (`truncate_E`), so its rank is
its rank of `E`, which is `min(r(E), j)` by `rk_truncate`.

### 1.2 Rank queries and the dual part

**Proposition 2 (rank query).**  `queryB_impl`.  For a Boolean circuit `C` on `m` inputs, the
builder `queryB C` (run `C` on a carried vector `V` of `m` bits and keep `W` outputs, padding
with the constant `0` when `C` has fewer) carries `bitsVal (C(V)) mod 2^W` on `W` bits, with
exactly `C.size` gates.

*Proof.*  Step 1, running `C` costs `C.size` gates and carries `bitsVal (C(V))` (`runB_num`).
Step 2, fitting to `W` bits is free and keeps the value modulo `2^W` (`numFit_impl`).  Step 3,
`Impl.comp`.

**Proposition 3 (the dual part).**  `dualB_impl`.  For a Boolean circuit `C₂` on `m` inputs and
`k₂ ∈ ℕ`, the builder `dualB C₂ k₂` carries, on `W + 1` bits,
`|{i : V_i}| + (bitsVal (C₂(¬V)) mod 2^W) − k₂`, with exactly
`m + s₂ + popCost m + 11W + 12 max(W + 1, ⌈log₂(k₂+1)⌉) + W + 3` gates.

*Proof.*  Step 1, the population count of `V` (`vecPopcountB_impl`): `popCost m` gates, on `W`
bits.  Step 2, the `m` negations of `V` (`vecNotB_impl`), then the rank query of Proposition 2
on them: `m + s₂` gates, on `W` bits.  Step 3, both on the same vector (`Impl.pair`), then their
sum on `W + 1` bits (`numAddB_impl`, `11W` gates).  Step 4, the subtraction of the constant
`k₂` on `W + 1` bits (`numSubConstB_impl`, `12 max(W + 1, ⌈log₂(k₂+1)⌉) + (W + 1) + 2` gates).
The counts add (`ring`).

### 1.3 Step 2 of the proof of Theorem `thm:D`: the rank circuit of `N = M₁ ⊕ M₂✶`

**Definition 4.**  `doubleB C₁ C₂ k₂` reads `m + m` bits `x`: the rank query of `C₁`
(Proposition 2) on the first copies `x(·, 1)`, the dual part of `C₂`, `k₂` (Proposition 3) on
the second copies `x(·, 2)` fitted to `W` bits, and their sum on `W + 1` bits.
`doubleRankCircuit C₁ C₂ k₂ = circuitOf (doubleB C₁ C₂ k₂)`, a Boolean circuit on `m + m`
inputs.

**Theorem 5 (size and value).**  `doubleB_impl`, `doubleRankCircuit_spec`,
`doubleRankCircuit_size`, `doubleRankCircuit_size_le`.  For Boolean circuits `C₁`, `C₂` on `m`
inputs and `k₂ ∈ ℕ`, `doubleRankCircuit C₁ C₂ k₂` has exactly
`s₁ + s₂ + m + popCost m + 23W + 12 max(W + 1, ⌈log₂(k₂+1)⌉) + 3` gates and `W + 1` outputs,
and at every `x ∈ {0, 1}^{E × {1, 2}}` the value of its outputs is
`(bitsVal (C₁(x(·, 1))) mod 2^W) + ((|{e : x(e, 2)}| + (bitsVal (C₂(¬x(·, 2))) mod 2^W) − k₂) mod 2^W)`.
For `k₂ ≤ m` the size is `s₁ + s₂ + m + popCost m + 35W + 15 ≤ s₁ + s₂ + 58m + 15`.

*Proof.*  Step 1, the rank query of `C₁` reads the operands of the first copies, a free
rearrangement (`Impl.pre`), `s₁` gates.  Step 2, the dual part reads the operands of the second
copies (`Impl.pre`) and its result is fitted to `W` bits (`numFit_impl`, free, the value modulo
`2^W`).  Step 3, both on the same input (`Impl.pair`) and their sum (`numAddB_impl`, `11W`
gates); the counts add.  Step 4, `circuitOf_num` turns the implementation into a circuit with
this size, `W + 1` outputs and this value.  Step 5, for `k₂ ≤ m`, `⌈log₂(k₂+1)⌉ ≤ W`
(`Nat.size_le_size`), so the maximum is `W + 1` and `23W + 12(W + 1) + 3 = 35W + 15`; moreover
`popCost m ≤ 22m` (`popCost_le`) and `W ≤ m` (`size_le_self`).

**Theorem 6 (Theorem `thm:D`, Step 2).**  `doubleRankCircuit_rank`, `double_rankCircuit`.  Let
`M₁`, `M₂` be matroids on `E` with ground set `E`, and let `C₁`, `C₂` be Boolean circuits of
sizes `s₁`, `s₂` that output `r₁(S)`, `r₂(S)` in binary from the indicator vector of every
`S ⊆ E`.  Then `doubleRankCircuit C₁ C₂ r₂(E)` outputs in binary, from the indicator vector of
every `S ⊆ E × {1, 2}`, the rank `r_N(S)` in `N = M₁ ⊕ M₂✶`, which is
`r₁(A) + |B| + r₂(E \ B) − r₂(E)` for `S = A × {1} ∪ B × {2}`.  Its size is
`s₁ + s₂ + m + popCost m + 35⌈log₂(m+1)⌉ + 15 ≤ s₁ + s₂ + 58m + 15`.  `double_rankCircuit`
states the existence of such a circuit, with both size statements and the correctness.

*Proof.*  Step 1, write `A = fst S`, `B = snd S`.  At `x = 1_S`, the first copies of `x` form
`1_A`, the negated second copies form `1_{E \ B}`, and the set entries of the second copies form
`B` (`indicator`, `mem_fst`, `mem_snd`).  Step 2, `C₁` outputs `r₁(A)` and `C₂` outputs
`r₂(E \ B)` (Lemma 1(4)), both below `2^W` (Lemma 1(2)), so the reductions modulo `2^W` change
nothing.  Step 3, `r₂✶(B) + r₂(E) = r₂(E \ B) + |B|` (`Doubling.rk_dual_add_rank`), so the
subtraction is exact, `|B| + r₂(E \ B) − r₂(E) = r₂✶(B)`, and `r₂✶(B) < 2^W` (Lemma 1(2) for
`M₂✶`).  Step 4, `r₁(A) + r₂✶(B) = r_N(A × {1} ∪ B × {2})` (`Doubling.rk_pair_eq_add`) and
`A × {1} ∪ B × {2} = S` (`pair_fst_snd`); read in `ℕ∞` by `coe_rk`.  Step 5, the size:
`r₂(E) ≤ m` (Lemma 1(3)) and Theorem 5.

### 1.4 Step 4 of the proof of Theorem `thm:D`: truncations

**Definition 7.**  `truncB C j`: the rank query of Proposition 2, then the minimum with the
constant `j` (`numMinConstB`, a comparison with `j` and a selection).
`truncRankCircuit C j = circuitOf (truncB C j)`, a Boolean circuit on `m` inputs.

**Theorem 8 (size and value).**  `truncB_impl`, `truncRankCircuit_spec`,
`truncRankCircuit_size`.  For a Boolean circuit `C` on `m` inputs and `j ∈ ℕ`,
`truncRankCircuit C j` has exactly `s + 8 max(W, ⌈log₂(j+1)⌉) + 3` gates and
`max(W, ⌈log₂(j+1)⌉)` outputs, and at every `x` the value of its outputs is
`min(bitsVal (C(x)) mod 2^W, j)`.  For `j ≤ m` the size is `s + 8W + 3`.

*Proof.*  Step 1, Proposition 2, then `numMinConstB_impl j W`: one gate for the constant `j`,
the comparison `[a ≤ j]` (`5W' + 1` gates) and the selection (`3W' + 1` gates), on
`W' = max(W, ⌈log₂(j+1)⌉)` bits.  Step 2, `circuitOf_num`.  Step 3, for `j ≤ m`,
`⌈log₂(j+1)⌉ ≤ W`.

**Theorem 9 (Theorem `thm:D`, Step 4, one truncation).**  `truncRankCircuit_rank`,
`truncate_rankCircuit`.  Let `M` be a matroid on `E` with ground set `E` and `C` a Boolean
circuit of size `s` that outputs `r(S)` in binary from the indicator vector of every `S ⊆ E`.
For every `j`, `truncRankCircuit C j` outputs in binary, from the indicator vector of every
`S ⊆ E`, the rank `min(r(S), j)` of `S` in the truncation of `M` at `j`.  For `j ≤ m` its size
is `s + 8⌈log₂(m+1)⌉ + 3`.

*Proof.*  Step 1, Theorem 8 at `x = 1_S`, where `C` outputs `r(S) < 2^W` (Lemma 1(2), (4)), so
the value is `min(r(S), j)`.  Step 2, this is the rank of `S` in the truncation
(`Trunc.rk_truncate`), read in `ℕ∞` by `coe_rk`.  Step 3, the size is Theorem 8.

### 1.5 Steps 2 and 4 together

**Definition 10.**  `doubleTruncRankCircuit C₁ C₂ k₂ j =
doubleRankCircuit (truncRankCircuit C₁ j) (truncRankCircuit C₂ j) (min(k₂, j))`.

**Theorem 11 (Theorem `thm:D`, Steps 2 and 4).**  `doubleTruncRankCircuit_rank`,
`doubleTruncRankCircuit_size`, `doubleTruncRankCircuit_size_le`,
`double_truncate_rankCircuit`.  Let `M₁`, `M₂`, `C₁`, `C₂` be as in Theorem 6, let `j ∈ ℕ`, and
let `T₁`, `T₂` be the truncations of `M₁`, `M₂` at `j`.  Then
`doubleTruncRankCircuit C₁ C₂ r₂(E) j` outputs in binary, from the indicator vector of every
`S ⊆ E × {1, 2}`, the rank of `S` in `N_j = T₁ ⊕ T₂✶`.  For `j ≤ m` its size is
`s₁ + s₂ + m + popCost m + 51⌈log₂(m+1)⌉ + 21 ≤ s₁ + s₂ + 74m + 21`.
`double_truncate_rankCircuit` states the existence of such a circuit for `j ≤ m`.

*Proof.*  Step 1, `T₁`, `T₂` have ground set `E` (`truncate_E`) and rank circuits
`truncRankCircuit C₁ j`, `truncRankCircuit C₂ j` (Theorem 9).  Step 2, `T₂` has rank
`min(r₂(E), j)` (Lemma 1(5)).  Step 3, Theorem 6 for `T₁`, `T₂` gives the correctness.  Step 4,
the size: `min(r₂(E), j) ≤ j ≤ m`, so Theorem 5 applies to circuits of sizes `s₁ + 8W + 3` and
`s₂ + 8W + 3` (Theorem 8): the total is `s₁ + s₂ + m + popCost m + 51W + 21`, and
`popCost m ≤ 22m`, `W ≤ m`.


### 1.6 Phase 2: the values

**Definition 12.**  For `w ∈ ℝ^E`: `commonBaseWeights M₁ M₂ w` is the set of the weights `w(X)`
of the common bases `X` of `M₁` and `M₂`, and `minCommonBaseWeight M₁ M₂ w` is its infimum;
`commonIndepWeights M₁ M₂ w` is the set of the weights of the common independent sets, and
`maxCommonIndepWeight M₁ M₂ w` is its supremum; `maxCommonIndepCard M₁ M₂ = J` is the supremum
in `ℕ` of the sizes of the common independent sets.

**Lemma 13.**

1. `commonBaseWeights_finite`, `commonIndepWeights_finite`: both sets of weights are finite.
2. `isLeast_minCommonBaseWeight`: if `M₁` and `M₂` have a common base, then
   `minCommonBaseWeight M₁ M₂ w` is the least weight of a common base.
3. `isGreatest_maxCommonIndepWeight`: `maxCommonIndepWeight M₁ M₂ w` is the greatest weight of a
   common independent set.
4. `card_le_maxCommonIndepCard`, `exists_card_eq_maxCommonIndepCard`, `exists_commonIndep_card`,
   `maxCommonIndepCard_le`: every common independent set has at most `J` elements, some has
   exactly `J`, every `j ≤ J` is the size of a common independent set, and `J ≤ m`.
5. `le_rank_of_indep`: an independent set of `M` has at most `r(E)` elements.

*Proof.*  Step 1, item 1: both sets lie in the image of the finite set of subsets of `E` under
`X ↦ w(X)`.  Step 2, items 2 and 3: a finite nonempty set of reals contains its infimum and its
supremum, which bound it (`csInf_mem`, `csSup_mem`, `csInf_le`, `le_csSup`); the set of item 2
is nonempty by the common base, that of item 3 contains `w(∅) = 0`.  Step 3, item 4: the sizes
of the common independent sets are at most `m` and include `0`, so `J` is one of them
(`Nat.sSup_mem`) and bounds them (`le_csSup`); a subset with `j` elements of a common independent
set with `J` elements is a common independent set (`exists_subset_card_eq`, `Indep.subset`).
Step 4, item 5: `card_le_rk` and `rk_le_rank`.

### 1.7 Steps 1 and 3: Theorem C on `N = M₁ ⊕ M₂✶`

**Proposition 14 (reading at `weight w`).**  `weightCircuit`, `weightCircuit_spec`.  For a signed
tropical circuit `C` on `E × {1, 2}`, the circuit `weightCircuit C` on `E` runs `C` with the
input `(e, 1)` reading `w_e` and the input `(e, 2)` reading the constant `0`.  It has the size of
`C` and outputs `C(weight w)` at every `w ∈ ℝ^E`.

*Proof.*  Step 1, `runB_impl` with a free rearrangement of the operands (`Impl.pre`, cases on
`Fin.addCases`): the operand of `(e, 1)` is the input `e`, which carries `w_e = weight w (e, 1)`
(`weight_castAdd`); the operand of `(e, 2)` is the constant source, which carries
`0 = weight w (e, 2)` (`weight_addNat`).  Step 2, `circuitOf_spec`.

**Theorem 15 (Theorem `thm:D`, Steps 1 and 3).**  `exists_minCommonBase_circuit`.  Let `M₁`,
`M₂` have ground set `E` and a common base, and let `B` be a Boolean circuit that outputs in
binary the rank in `N = M₁ ⊕ M₂✶` of every `S ⊆ E × {1, 2}`.  Then a signed tropical circuit on
`E` with at most `2436 m⁴ (2m)⁶ (|B| + 2m) + 2` gates outputs the minimum weight of a common base
of `M₁` and `M₂` at every `w ∈ ℝ^E`.

*Proof.*  Step 1, `M₁` and `M₂` have equal rank (`rank_eq_rank_of_isBase`), so `N` has ground
set `E × {1, 2}` (`double_ground`), rank `m` (`rank_double_eq`) and a rainbow base for the `m`
blocks `{(e, 1), (e, 2)}` (`exists_isRainbowBase_iff`).  Step 2, Theorem C
(`TheoremCFinal.theoremC_final`, with `2m` elements and `k = m` blocks) gives a circuit `C_N` on
`E × {1, 2}` with at most `2436 m⁴ (2m)⁶ (|B| + 2m) + 2` gates that outputs `Opt_N(w')` at every
`w'`.  Step 3, `weightCircuit C_N` (Proposition 14) has the same size and outputs
`Opt_N(weight w)`, which is the infimum of the weights of the common bases (`Doubling.opt_eq`),
that is `minCommonBaseWeight M₁ M₂ w`.

### 1.8 Part (1): the minimum weight of a common base

**Theorem 16 (Theorem `thm:D`, first part).**  `theoremD_commonBase`.  Let `M₁`, `M₂` be
matroids on `E` with ground set `E` and a common base, and let `C₁`, `C₂` be Boolean circuits of
sizes `s₁`, `s₂` that output `r₁(S)`, `r₂(S)` in binary from the indicator vector of every
`S ⊆ E`.  Then a signed tropical circuit of size at most
`2436 m⁴ (2m)⁶ (s₁ + s₂ + 60m + 15) + 2 ≤ 2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2` outputs the minimum
weight of a common base at every `w ∈ ℝ^E`.

*Proof.*  Step 1, Theorem 15 with `B = doubleRankCircuit C₁ C₂ r₂(E)` (Theorem 6), which has at
most `s₁ + s₂ + 58m + 15` gates (Theorem 5, `r₂(E) ≤ m`), so `|B| + 2m ≤ s₁ + s₂ + 60m + 15`.
Step 2 (`size_commonBase_le`), `m⁴ (2m)⁶ = 64 m¹⁰` and `s + 60m + 15 ≤ 75(s + m)` for `m ≥ 1`,
so `m⁴ (2m)⁶ (s + 60m + 15) ≤ 4800 m¹⁰ (s + m)`; for `m = 0` both sides are `0`.

### 1.9 Step 4: common independent sets as common bases of truncations

**Proposition 17 (Step 4, one size).**  `isGreatest_neg_minCommonBaseWeight`.  Let `M₁`, `M₂`
have ground set `E`, and let some common independent set have `j` elements.  Let `β_j(u)` be the
minimum weight of a common base of the truncations of `M₁` and `M₂` at `j`.  Then `−β_j(−w)` is
the greatest weight `w(X)` of a common independent set `X` with `j` elements.

*Proof.*  Step 1, `j ≤ r₁(E)` and `j ≤ r₂(E)` (Lemma 13(5)), so the common bases of the
truncations at `j` are the common independent sets with `j` elements
(`Trunc.isBase_truncate_both_iff`), and there is one.  Step 2, `β_j(−w)` is the least `(−w)(X)`
over these sets `X` (Lemma 13(2)), and `(−w)(X) = −w(X)` (`sum_neg_distrib`).  Step 3, so
`−β_j(−w)` is `w(X)` for the minimizing `X`, and every such `w(Y)` is at most `−β_j(−w)`.

**Lemma 18.**  `foldr_max_spec`.  For a list `l` of reals, `max(0, l)` (the right fold of `max`
from `0`) is at least `0` and at least every entry of `l`, and it is `0` or an entry of `l`.

*Proof.*  Induction on `l`: the fold of `a :: l` is `max(a, fold of l)`.

**Theorem 19 (Theorem `thm:D`, Step 4).**  `maxCommonIndepWeight_eq`.  Let `M₁`, `M₂` have
ground set `E` and let `J` be the largest size of a common independent set.  Then the maximum
weight of a common independent set is `max(0, −β_1(−w), …, −β_J(−w))`.

*Proof.*  Step 1, the right side `v` is the weight of a common independent set: `0 = w(∅)`, or
`−β_j(−w)` with `1 ≤ j ≤ J`, which is attained (Proposition 17, with Lemma 13(4) for a common
independent set with `j` elements).  Step 2, every `w(X)`, `X` common independent, is at most
`v`: if `X = ∅`, then `w(X) = 0 ≤ v`; otherwise `1 ≤ |X| ≤ J` (Lemma 13(4)) and
`w(X) ≤ −β_{|X|}(−w) ≤ v` (Proposition 17, Lemma 18).  Step 3, so `v` is the greatest weight of a
common independent set, which is `maxCommonIndepWeight` (Lemma 13(3), `IsGreatest.unique`).

### 1.10 The circuit of Step 4

**Definition 20.**  `negB`, `negRunB`, `maxB`, `maxIndepB`, `maxIndepCircuit`.  For signed
tropical circuits `D_0, …, D_{J−1}` on `E`, `maxIndepCircuit D` computes `u = −w` as `0 − w_e`
(`m` gates), runs each `D_i` on `u` and negates its first output (one gate each), and takes the
maximum of `0` and these `J` values (one `max` gate each, starting from the constant `0`).

**Proposition 21 (size and value).**  `negB_impl`, `negRunB_impl`, `maxB_spec`,
`maxIndepCircuit_spec`.  `maxIndepCircuit D` has exactly `m + Σ_i (|D_i| + 1) + J` gates and
outputs `max(0, −D_0(−w)₀, …, −D_{J−1}(−w)₀)` at every `w`, `D_i(u)₀` the first output of `D_i`.

*Proof.*  Step 1, `negB`: one gate `0 − x_e` per entry (`Impl.tab`).  Step 2, `negRunB`: running
`D` costs `|D|` gates and carries its outputs (`runB_impl`), and one gate negates the first.
Step 3, the `J` values (`Impl.tabSum`), `Σ_i (|D_i| + 1)` gates.  Step 4, `maxB`, by induction on
the list: one `max` gate per entry.  Step 5, `circuitOf_spec`; the counts add.

### 1.11 Part (2): the maximum weight of a common independent set

**Theorem 22 (Theorem `thm:D`, second part).**  `theoremD_commonIndep`.  Let `M₁`, `M₂` be
matroids on `E` with ground set `E`, and let `C₁`, `C₂` be Boolean circuits of sizes `s₁`, `s₂`
that output `r₁(S)`, `r₂(S)` in binary from the indicator vector of every `S ⊆ E`.  Then a signed
tropical circuit of size at most
`m + m (2436 m⁴ (2m)⁶ (s₁ + s₂ + 76m + 21) + 4) ≤ 2436 · 6209 m¹¹ (s₁ + s₂ + m)` outputs the
maximum weight of a common independent set at every `w ∈ ℝ^E`.  No common base is assumed.

*Proof.*  Step 1, `J ≤ m` (Lemma 13(4)).  For `i < J` and `j = i + 1`, the truncations at `j`
have a common base, a common independent set with `j` elements (Lemma 13(4),
`isBase_truncate_both_iff`), and their doubled matroid has the rank circuit
`doubleTruncRankCircuit C₁ C₂ r₂(E) j` (Theorem 11) with at most `s₁ + s₂ + 74m + 21` gates
(`j ≤ m`).  Theorem 15 gives a circuit `D_i` with at most `Y + 2` gates,
`Y = 2436 m⁴ (2m)⁶ (s₁ + s₂ + 76m + 21)`, that outputs `β_j`.  Step 2, `maxIndepCircuit D`
(Proposition 21) outputs `max(0, −β_1(−w), …, −β_J(−w))`, the maximum weight of a common
independent set (Theorem 19), with `m + Σ_i (|D_i| + 1) + J ≤ m + J (Y + 4) ≤ m + m (Y + 4)`
gates.  Step 3 (`size_commonIndep_le`), for `m ≥ 1`:
`m⁴ (2m)⁶ (s + 76m + 21) = 64 m¹⁰ (s + 76m + 21) ≤ 6208 m¹⁰ (s + m)`, so
`m + m (Y + 4) ≤ 2436 · 6208 m¹¹ (s + m) + 5m ≤ 2436 · 6209 m¹¹ (s + m)`, using
`m ≤ m¹¹ (s + m)`; for `m = 0` both sides are `0`.

### 1.12 Theorem D

**Theorem 23 (Theorem `thm:D`, matroid intersection).**  `theoremD`.  Let `M₁` and `M₂` be
matroids on `E = Fin m` (ground set `E`, `|E| = m`) with Boolean circuits of sizes `s₁` and `s₂`
that output the binary digits of their rank functions, and with a common base.  Then a signed
tropical circuit of size at most `2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2` outputs the minimum weight of
a common base at every `w ∈ ℝ^E`, and one of size at most `2436 · 6209 m¹¹ (s₁ + s₂ + m)` outputs
the maximum weight of a common independent set at every `w ∈ ℝ^E`.

*Proof.*  Theorems 16 and 22.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `thm:D` Step 2: `r_N(A × {1} ∪ B × {2}) = r₁(A) + \|B\| + r₂(E \ B) − r₂(E)` is computed on top of the two rank circuits, size `s₁ + s₂ + O(m)` | `double_rankCircuit`, `doubleRankCircuit`, `doubleRankCircuit_rank`, `doubleRankCircuit_spec`, `doubleRankCircuit_size`, `doubleRankCircuit_size_le` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Step 2: population count, `m` negations, additions, subtraction of `r₂(E)` | `dualB_impl`, `doubleB_impl`, `queryB_impl` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Step 4: rank circuits of the truncations `min(r_i, j)`: a comparison and a selection on `O(log m)` bits | `truncate_rankCircuit`, `truncRankCircuit`, `truncRankCircuit_rank`, `truncRankCircuit_spec`, `truncRankCircuit_size`, `truncB_impl` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Steps 2 and 4: the rank circuit of the doubled matroid of the truncations | `double_truncate_rankCircuit`, `doubleTruncRankCircuit`, `doubleTruncRankCircuit_rank`, `doubleTruncRankCircuit_size`, `doubleTruncRankCircuit_size_le` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Steps 1 and 3: Theorem C on `N` (`2m` elements, `m` blocks, rank `m`), read at the weights `w_e` and `0` | `exists_minCommonBase_circuit`, `weightCircuit`, `weightCircuit_spec` | `Rainbow/TheoremD` | proved |
| `thm:D` (1): the minimum weight of a common base, size `O(m¹⁰(s₁ + s₂ + m))` | `theoremD_commonBase`, `minCommonBaseWeight`, `isLeast_minCommonBaseWeight`, `size_commonBase_le` | `Rainbow/TheoremD` | proved |
| `thm:D` Step 4: common independent sets of size `j` are the common bases of the truncations; the maximum over `j`, with `0` for `j = 0` | `isGreatest_neg_minCommonBaseWeight`, `maxCommonIndepWeight_eq`, `foldr_max_spec`, `maxCommonIndepCard` and its lemmas | `Rainbow/TheoremD` | proved |
| `thm:D` Step 4: the weights `−w`, the negated outputs, the maximum | `maxIndepCircuit`, `maxIndepCircuit_spec`, `negB_impl`, `negRunB_impl`, `maxB_spec` | `Rainbow/TheoremD` | proved |
| `thm:D` (2): the maximum weight of a common independent set, size `O(m¹¹(s₁ + s₂ + m))` | `theoremD_commonIndep`, `maxCommonIndepWeight`, `isGreatest_maxCommonIndepWeight`, `size_commonIndep_le` | `Rainbow/TheoremD` | proved |
| `thm:D` | `theoremD` | `Rainbow/TheoremD` | proved |
| `thm:D`, uniformity | none | | not formalized |


## 3. Differences from the paper

1. Size of Step 2.  The paper gives `s₁ + s₂ + O(m)`; the Lean circuit has exactly
   `s₁ + s₂ + m + popCost m + 35⌈log₂(m+1)⌉ + 15 ≤ s₁ + s₂ + 58m + 15` gates.  Besides "a
   population count and two additions", the circuit needs `m` negations, to feed the indicator
   vector of `E \ B` to the second rank circuit, and the subtraction of the constant `r₂(E)`
   (which is exact, since `|B| + r₂(E \ B) − r₂(E) = r₂✶(B) ≥ 0`).  Both fit in `O(m)`.
   Proposed wording (optional), Step 2 of the proof of `thm:D`: "$r_N(A\times\{1\}\cup
   B\times\{2\})=r_1(A)+|B|+r_2(E\setminus B)-r_2(E)$: the second rank circuit reads the negated
   indicator vector of $B$, and a population count, two additions and the subtraction of the
   constant $r_2(E)$ on $O(\log m)$ bits complete a circuit of size $s_1+s_2+O(m)$."
2. Output widths.  The given rank circuits may have any number of outputs; the construction
   keeps `⌈log₂(m+1)⌉` of them, which carry the rank since `r(S) ≤ m` (as in P6a, Section 3,
   item 2).  The rank circuit of `N` has `⌈log₂(m+1)⌉ + 1` outputs (`r_N ≤ 2m`); that of a
   truncation at `j ≤ m` has `⌈log₂(m+1)⌉` outputs.  No change to the paper.
3. The constant `r₂(E)` is a parameter of the construction (`doubleRankCircuit C₁ C₂ k₂`), as
   the rank `k` is for the dual (`Classes.dualRankCircuit B k`): the circuit depends on the
   matroids only through `C₁`, `C₂` and `r₂(E)`, which the generator computes by one evaluation
   of `C₂`, as the uniformity of the paper requires (not formalized, item 7).  No change to the
   paper.
4. Truncation at `j > m`.  The comparison with a constant `j` has `max(⌈log₂(m+1)⌉,
   ⌈log₂(j+1)⌉)` bits (`truncRankCircuit_spec`, valid for every `j`); the bound
   `s + 8⌈log₂(m+1)⌉ + 3` is stated for `j ≤ m`, the only case Step 4 uses
   (`j ≤ min(r₁(E), r₂(E)) ≤ m`).  No change to the paper.
5. Explicit sizes in Theorem D.  The paper's `O(m¹⁰(s₁ + s₂ + m))` and `O(m¹¹(s₁ + s₂ + m))` are
   `2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2` and `2436 · 6209 m¹¹ (s₁ + s₂ + m)`, with the constant
   `2436 = 3 · 800 + 36` of Theorem C (`theoremC_final`: `2436 k⁴ m⁶ (s + m) + 2`); the finer
   bounds are `2436 m⁴ (2m)⁶ (s₁ + s₂ + 60m + 15) + 2` and
   `m + m (2436 m⁴ (2m)⁶ (s₁ + s₂ + 76m + 21) + 4)`.  The additive `2` of the first part is the
   one of Theorem C; it matters only for `m = 0`.  No change to the paper.
6. The second part of `thm:D` does not use the common base.  `theoremD_commonIndep` states it
   without that hypothesis, and `theoremD` states both parts under the hypotheses of the paper.
   Proposed wording (optional), end of the statement of `thm:D`: "..., and one of size
   $O(m^{11}(s_1+s_2+m))$ computes the maximum weight of a common independent set; this part
   needs no common base."
7. Uniformity is not formalized, as for Theorem C (`notes/P7-theoremC.md`, difference 5): the
   circuits are explicit Lean terms built from `C₁`, `C₂`, `r₂(E)`, the number `J` and the
   construction of Theorem C, but no statement about the time to produce them is made.
8. Step 4 in detail.  "Every `j` up to the largest size of a common independent set, decided
   once by the generator" is `j = 1, …, J` with `J = maxCommonIndepCard M₁ M₂`; the weights `−w`
   are computed once (`m` gates) and shared by the `J` circuits; "negate the output" is one gate
   `0 − x` per circuit; "the maximum over `j`, with `0` for `j = 0`" is a chain of `J` gates
   `max` starting from the constant `0`.  No change to the paper.
9. The minimum and the maximum are the infimum and the supremum of finite sets of reals
   (`minCommonBaseWeight`, `maxCommonIndepWeight`); `isLeast_minCommonBaseWeight` (with a common
   base) and `isGreatest_maxCommonIndepWeight` show that they are attained, as least and greatest
   weights.  No change to the paper.


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/TheoremDRank.lean` | 333 |
| `SignedTropical/Rainbow/TheoremD.lean` | 466 |
| total | 799 |


## 5. Not done

* Theorem `thm:D` is proved in both parts, unconditionally (Theorem C from
  `Rainbow/TheoremCFinal.lean`, whose observers are those of Lemma `lem:observer`, P6c), with
  the explicit bounds above.  Not formalized: uniformity (difference 7).


## 6. API for later agents

All names are in `SignedTropical.Rainbow.TheoremD` (`open SignedTropical.Rainbow.TheoremD`).
Throughout, `M M₁ M₂ : Matroid (Fin m)`, `C C₁ C₂ : Circuit BoolOp m`, and the rank-circuit
hypotheses are

```lean
hC : ∀ S : Finset (Fin m),
  (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))
```

(and `hC₁`, `hC₂` for `M₁`, `M₂`), with `hE : M.E = Set.univ`, `hE₁`, `hE₂`.

### 6.1 Rank circuits (`TheoremDRank.lean`)

| name | statement |
| :-- | :-- |
| `doubleRankCircuit (C₁ C₂ : Circuit BoolOp m) (k₂ : ℕ) : Circuit BoolOp (m + m)` | the rank circuit of `N` (with `k₂ = rank M₂`) |
| `doubleRankCircuit_rank hE₁ hE₂ hC₁ hC₂ (S : Finset (Fin (m + m)))` | `(bitsVal ((doubleRankCircuit C₁ C₂ (rank M₂)).eval boolInterp (indicator S)) : ℕ∞) = (double M₁ M₂).eRk (S : Set (Fin (m + m)))` |
| `doubleRankCircuit_size {k₂} (hk : k₂ ≤ m) C₁ C₂` | `(doubleRankCircuit C₁ C₂ k₂).size = C₁.size + C₂.size + m + popCost m + 35 * Nat.size m + 15` |
| `doubleRankCircuit_size_le {k₂} (hk : k₂ ≤ m) C₁ C₂` | `(doubleRankCircuit C₁ C₂ k₂).size ≤ C₁.size + C₂.size + 58 * m + 15` |
| `doubleRankCircuit_spec C₁ C₂ k₂` | exact size for every `k₂` (with `max (Nat.size m + 1) (Nat.size k₂)`), `outs.length = Nat.size m + 1`, and the value at every `x` |
| `double_rankCircuit hE₁ hE₂ hC₁ hC₂` | `∃ C : Circuit BoolOp (m + m)`, size `= C₁.size + C₂.size + m + popCost m + 35 * Nat.size m + 15`, `≤ C₁.size + C₂.size + 58 * m + 15`, and correct for `double M₁ M₂` |
| `truncRankCircuit (C : Circuit BoolOp m) (j : ℕ) : Circuit BoolOp m` | the rank circuit of `truncate M j` |
| `truncRankCircuit_rank hE hC (j) (S : Finset (Fin m))` | `(bitsVal ((truncRankCircuit C j).eval boolInterp (indicator S)) : ℕ∞) = (truncate M j).eRk (S : Set (Fin m))` |
| `truncRankCircuit_size {j} (hj : j ≤ m) C` | `(truncRankCircuit C j).size = C.size + 8 * Nat.size m + 3` |
| `truncRankCircuit_spec C j` | exact size for every `j` (with `max (Nat.size m) (Nat.size j)`), outputs, value |
| `truncate_rankCircuit hE hC {j} (hj : j ≤ m)` | `∃ C'`, size `= C.size + 8 * Nat.size m + 3`, correct for `truncate M j` |
| `doubleTruncRankCircuit (C₁ C₂ : Circuit BoolOp m) (k₂ j : ℕ) : Circuit BoolOp (m + m)` | `doubleRankCircuit (truncRankCircuit C₁ j) (truncRankCircuit C₂ j) (min k₂ j)` |
| `doubleTruncRankCircuit_rank hE₁ hE₂ hC₁ hC₂ (j) (S : Finset (Fin (m + m)))` | `(bitsVal ((doubleTruncRankCircuit C₁ C₂ (rank M₂) j).eval boolInterp (indicator S)) : ℕ∞) = (double (truncate M₁ j) (truncate M₂ j)).eRk (S : Set (Fin (m + m)))` |
| `doubleTruncRankCircuit_size {j} (hj : j ≤ m) C₁ C₂ k₂` | `size = C₁.size + C₂.size + m + popCost m + 51 * Nat.size m + 21` |
| `doubleTruncRankCircuit_size_le {j} (hj : j ≤ m) C₁ C₂ k₂` | `size ≤ C₁.size + C₂.size + 74 * m + 21` |
| `double_truncate_rankCircuit hE₁ hE₂ hC₁ hC₂ {j} (hj : j ≤ m)` | `∃ C : Circuit BoolOp (m + m)`, both size statements, correct for `double (truncate M₁ j) (truncate M₂ j)` |

### 6.2 Rank facts (`TheoremDRank.lean`)

| name | statement |
| :-- | :-- |
| `rk_le_card M S` | `rk M S ≤ #S` |
| `rk_lt_two_pow M S` | `rk M S < 2 ^ Nat.size m` |
| `rank_le_card M` | `rank M ≤ m` |
| `bitsVal_eq_rk hC S` | `bitsVal (C.eval boolInterp (indicator S)) = rk M S` |
| `rank_truncate_eq_min hE j` | `rank (truncate M j) = min (rank M) j` |

### 6.3 Boolean gadgets (`TheoremDRank.lean`, any ambient number `n` of inputs)

| name | statement |
| :-- | :-- |
| `queryB_impl C` | `Impl (vecR m) (numR (Nat.size m)) (queryB C) C.size (fun V => bitsVal (C.eval boolInterp V) % 2 ^ Nat.size m)` |
| `dualB_impl C₂ k₂` | `Impl (vecR m) (numR (Nat.size m + 1)) (dualB C₂ k₂) (m + C₂.size + popCost m + 11 * Nat.size m + (12 * max (Nat.size m + 1) (Nat.size k₂) + Nat.size m + 3))`, value `#{i \| V i} + bitsVal (C₂.eval boolInterp (¬V)) % 2 ^ Nat.size m - k₂` |
| `doubleB_impl C₁ C₂ k₂` | `Impl (vecR (m + m)) (numR (Nat.size m + 1)) (doubleB C₁ C₂ k₂)` with the cost and value of `doubleRankCircuit_spec` |
| `truncB_impl C j` | `Impl (vecR m) (numR (max (Nat.size m) (Nat.size j))) (truncB C j) (C.size + (8 * max (Nat.size m) (Nat.size j) + 3)) (fun V => min (bitsVal (C.eval boolInterp V) % 2 ^ Nat.size m) j)` |

### 6.4 Theorem D (`TheoremD.lean`)

`w : Fin m → ℝ`; `hX : ∃ X : Finset (Fin m), M₁.IsBase ↑X ∧ M₂.IsBase ↑X` (a common base).

| name | statement |
| :-- | :-- |
| `theoremD hE₁ hE₂ hC₁ hC₂ hX` | `(∃ C : Circuit STOp m, C.size ≤ 2436 * 4800 * (m ^ 10 * (C₁.size + C₂.size + m)) + 2 ∧ ∀ w, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w]) ∧ (∃ C : Circuit STOp m, C.size ≤ 2436 * 6209 * (m ^ 11 * (C₁.size + C₂.size + m)) ∧ ∀ w, C.eval (stInterp ℝ) w = [maxCommonIndepWeight M₁ M₂ w])` |
| `theoremD_commonBase hE₁ hE₂ hC₁ hC₂ hX` | `∃ C : Circuit STOp m`, `C.size ≤ 2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 60 * m + 15)) + 2`, `C.size ≤ 2436 * 4800 * (m ^ 10 * (C₁.size + C₂.size + m)) + 2`, output `[minCommonBaseWeight M₁ M₂ w]` |
| `theoremD_commonIndep hE₁ hE₂ hC₁ hC₂` | `∃ C : Circuit STOp m`, `C.size ≤ m + m * (2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 76 * m + 21)) + 4)`, `C.size ≤ 2436 * 6209 * (m ^ 11 * (C₁.size + C₂.size + m))`, output `[maxCommonIndepWeight M₁ M₂ w]` (no common base) |
| `exists_minCommonBase_circuit hE₁ hE₂ hX B hB` | for any rank circuit `B : Circuit BoolOp (m + m)` of `double M₁ M₂`: `∃ C : Circuit STOp m, C.size ≤ 2436 * (m ^ 4 * (m + m) ^ 6 * (B.size + (m + m))) + 2 ∧ ∀ w, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w]` |
| `commonBaseWeights M₁ M₂ w : Set ℝ`, `minCommonBaseWeight M₁ M₂ w : ℝ` | the weights of the common bases; their infimum |
| `isLeast_minCommonBaseWeight hX w` | `IsLeast (commonBaseWeights M₁ M₂ w) (minCommonBaseWeight M₁ M₂ w)` |
| `commonIndepWeights M₁ M₂ w : Set ℝ`, `maxCommonIndepWeight M₁ M₂ w : ℝ` | the weights of the common independent sets; their supremum |
| `isGreatest_maxCommonIndepWeight M₁ M₂ w` | `IsGreatest (commonIndepWeights M₁ M₂ w) (maxCommonIndepWeight M₁ M₂ w)` |
| `maxCommonIndepCard M₁ M₂ : ℕ` | the largest size of a common independent set; `card_le_maxCommonIndepCard h₁ h₂`, `exists_card_eq_maxCommonIndepCard`, `exists_commonIndep_card (hj : j ≤ maxCommonIndepCard M₁ M₂)`, `maxCommonIndepCard_le : maxCommonIndepCard M₁ M₂ ≤ m` |
| `isGreatest_neg_minCommonBaseWeight hE₁ hE₂ hj w` | for `hj : ∃ X, M₁.Indep ↑X ∧ M₂.Indep ↑X ∧ #X = j`: `-minCommonBaseWeight (truncate M₁ j) (truncate M₂ j) (fun e => -w e)` is the greatest `w(X)` over the common independent sets with `#X = j` |
| `maxCommonIndepWeight_eq hE₁ hE₂ w` | `maxCommonIndepWeight M₁ M₂ w = (List.ofFn fun i : Fin (maxCommonIndepCard M₁ M₂) => -minCommonBaseWeight (truncate M₁ (i + 1)) (truncate M₂ (i + 1)) fun e => -w e).foldr max 0` |
| `weightCircuit (C : Circuit STOp (m + m)) : Circuit STOp m`, `weightCircuit_spec C` | size `C.size`, and `(weightCircuit C).eval (stInterp ℝ) w = C.eval (stInterp ℝ) (weight w)` |
| `maxIndepCircuit (D : Fin J → Circuit STOp m) : Circuit STOp m`, `maxIndepCircuit_spec D` | size `m + ∑ i, ((D i).size + 1) + J`, output `[(List.ofFn fun i => -((D i).eval (stInterp ℝ) fun e => -w e).getD 0 0).foldr max 0]` |
| `negB_impl`, `negRunB_impl D`, `maxB_spec` | signed tropical gadgets: `x ↦ -x` (`m` gates), `u ↦ -D(u)₀` (`D.size + 1`), the maximum of `0` and a list (one gate per entry) |
| `size_commonBase_le m s`, `size_commonIndep_le m s` | `m ^ 4 * (m + m) ^ 6 * (s + 60 * m + 15) ≤ 4800 * (m ^ 10 * (s + m))`; `m + m * (2436 * (m ^ 4 * (m + m) ^ 6 * (s + 76 * m + 21)) + 4) ≤ 2436 * 6209 * (m ^ 11 * (s + m))` |
