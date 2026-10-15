# P8: Theorem D (Theorem `thm:D`, matroid intersection)

Natural-language companion of `SignedTropical/Rainbow/TheoremDRank.lean` (the rank circuits of
Steps 2 and 4, and the padded matroids of Step 4) and `SignedTropical/Rainbow/TheoremD.lean`
(Theorem `thm:D` itself), namespace `SignedTropical.Rainbow.TheoremD`.

Sources: `daishu/paper/greedy_intersection.tex`, Theorem `thm:D` and its proof (Section 5);
Lemma `lem:doubling` and its Lean form `Rainbow/Doubling.lean` (P1x,
`notes/P1x-partition-doubling.md`); the truncation `Rainbow/Truncation.lean`
(`notes/Truncation.md`); the Boolean library `BoolAlg` (P6a, `notes/P6a-boolalg.md`); the rank
circuit of the dual `Classes/Dual.lean` (E4), a related construction; Theorem C,
`Rainbow/TheoremCFinal.lean` (`TheoremCFinal.theoremC_final`, P7 and P6c,
`notes/P7-theoremC.md`, `notes/P6c-observer.md`) with the real-vector gadgets of
`Rainbow/OneUpdate.lean` (`TheoremC.realsR`).

Build: no error, no warning, no `sorry`; the theorems depend on `propext`,
`Classical.choice` and `Quot.sound` only.  Imports: `TheoremDRank` imports `BoolAlg.Count`,
`Rainbow.Doubling`, `Rainbow.Truncation`; `TheoremD` imports `TheoremDRank` and
`Rainbow.TheoremCFinal`.

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

*Proof.*  Step 1, item 1 is Mathlib's `eRk_le_encard` read in `ℕ` (`coe_rk`, and the
cardinality of a finite set is its size).  Step 2, item 2: `r(S) ≤ |S| ≤ m < 2^W`
(`Nat.lt_size_self`).  Step 3, item 3: a base has `r(E)` elements (`card_base`), at most `m`.
Step 4, item 4: the map `ℕ → ℕ∞` is injective and `r(S)` read in `ℕ∞` is `M.eRk S`
(`coe_rk`).

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

### 1.4 Truncations and the padded matroid

**Definition 7.**  `truncB C j`: the rank query of Proposition 2, then the minimum with the
constant `j` (`numMinConstB`, a comparison with `j` and a selection).
`truncRankCircuit C j = circuitOf (truncB C j)`.  `loops m = loopyOn E`, the matroid whose
elements are all loops, with rank `0` (`rank_loops`) and the rank circuit `zeroCircuit m` (no
gates, no outputs, the number `0`; `zeroCircuit_rank`); its dual is free.
`pad M = truncate (double M (loops m)) m`, on `E × {1, 2}`: `M` on the first copies, every set of
second copies independent, truncated at `m`.  `padRankCircuit C =
truncRankCircuit (doubleRankCircuit C (zeroCircuit m) 0) m`.

**Theorem 8 (the truncation).**  `truncB_impl`, `truncRankCircuit_spec`,
`truncRankCircuit_size`, `truncRankCircuit_rank`.  `truncRankCircuit C j` has exactly
`s + 8 max(W, ⌈log₂(j+1)⌉) + 3` gates (`s + 8W + 3` for `j ≤ m`) and outputs
`min(bitsVal (C(x)) mod 2^W, j)`; for a rank circuit `C` of `M` this is the rank `min(r(S), j)`
of `S` in `truncate M j` (`Trunc.rk_truncate`).

**Theorem 9 (Theorem `thm:D`, Step 4, the padded matroid).**  `indep_double_loops`,
`rank_double_loops`, `isBase_pad_iff`, `padRankCircuit_rank`, `padRankCircuit_size`,
`padRankCircuit_size_le`.  Let `M` have ground set `E` and the rank circuit `C`.

1. `S ⊆ E × {1, 2}` is independent in `double M (loops m)` iff `fst S` is independent in `M`, and
   `double M (loops m)` has rank `r(E) + m`.
2. The bases of `pad M` are the sets `S` with `|S| = m` and `fst S` independent in `M`.
3. `padRankCircuit C` outputs in binary the rank of every `S` in `pad M`, which is
   `min(r(fst S) + |snd S|, m)`, with exactly `s + m + popCost m + 35W + 8⌈log₂(2m+1)⌉ + 18 ≤
   s + 74m + 18` gates.

*Proof.*  Step 1, item 1: `Matroid.mapEquiv_indep_iff`, `Matroid.sum_indep_iff`, and
`(loopyOn E)✶ = freeOn E`, in which every set is independent.  `rank_double` with
`rank (loops m) = 0` gives the rank.  Step 2, item 2: `isBase_truncate_iff`, as `m ≤ r(E) + m`.
Step 3, item 3: Theorem 6 for `M` and `loops m` (`r₂ = 0`, so `r_N(A × {1} ∪ B × {2}) =
r(A) + |B|`), then Theorem 8 at `j = m`; the sizes add.


### 1.5 Phase 2: the values

**Definition 10.**  For `w ∈ ℝ^E`: `commonBaseWeights M₁ M₂ w` is the set of the weights `w(X)`
of the common bases `X` of `M₁` and `M₂`, and `minCommonBaseWeight M₁ M₂ w` is its infimum;
`commonIndepWeights M₁ M₂ w` is the set of the weights of the common independent sets, and
`maxCommonIndepWeight M₁ M₂ w` is its supremum.

**Lemma 11.**  `commonBaseWeights_finite`, `commonIndepWeights_finite`: both sets are finite.
`isLeast_minCommonBaseWeight`: with a common base, `minCommonBaseWeight M₁ M₂ w` is the least
weight of a common base.  `isGreatest_maxCommonIndepWeight`: `maxCommonIndepWeight M₁ M₂ w` is
the greatest weight of a common independent set.

*Proof.*  Both sets lie in the image of the finite set of subsets of `E`; a finite nonempty set
of reals contains its infimum and its supremum (`csInf_mem`, `csSup_mem`); the second set
contains `w(∅) = 0`.

### 1.6 Steps 1 and 3: Theorem C on `N = M₁ ⊕ M₂✶`

**Proposition 12 (reading at `weight w`).**  `weightCircuit`, `weightCircuit_spec`.  For a signed
tropical circuit `C` on `E × {1, 2}`, `weightCircuit C` on `E` runs `C` with `(e, 1)` reading `w_e`
and `(e, 2)` the constant `0`; it has the size of `C` and outputs `C(weight w)`.

**Theorem 13 (Theorem `thm:D`, Steps 1 and 3).**  `exists_minCommonBase_circuit`.  Let `M₁`,
`M₂` have ground set `E` and a common base, and let `B` be a rank circuit of
`N = M₁ ⊕ M₂✶`.  Then a signed tropical circuit on `E` with at most
`1664 m³ (2m)⁵ (|B| + 2m) + 2` gates outputs the minimum weight of a common base at every `w`.

*Proof.*  `N` has ground set `E × {1, 2}`, rank `m` (`rank_double_eq`) and a rainbow base
(`exists_isRainbowBase_iff`); Theorem C (`TheoremCFinal.theoremC_final`, `2m` elements, `k = m`)
and Proposition 12, with `Opt_N(weight w) = minCommonBaseWeight M₁ M₂ w` (`Doubling.opt_eq`).

### 1.7 Part (1): the minimum weight of a common base

**Theorem 14 (Theorem `thm:D`, first part).**  `theoremD_commonBase`.  With rank circuits `C₁`,
`C₂` of sizes `s₁`, `s₂` and a common base, a signed tropical circuit of size at most
`1664 m³ (2m)⁵ (s₁ + s₂ + 60m + 15) + 2 ≤ 1664 · 2400 m⁸ (s₁ + s₂ + m) + 2` outputs the minimum
weight of a common base at every `w ∈ ℝ^E`.

*Proof.*  Theorem 13 with `B = doubleRankCircuit C₁ C₂ r₂(E)`, at most `s₁ + s₂ + 58m + 15` gates
(Theorem 5).  `size_commonBase_le`: `m³ (2m)⁵ = 32 m⁸` and `s + 60m + 15 ≤ 75(s + m)` for
`m ≥ 1`.

### 1.8 Step 4: common independent sets as common bases of the padded matroids

**Theorem 15 (Theorem `thm:D`, Step 4).**  `sum_weight_neg`, `exists_commonBase_pad`,
`minCommonBaseWeight_pad`.  Let `M₁`, `M₂` have ground set `E`.  The set `∅ × {1} ∪ E × {2}` is a
common base of `pad M₁` and `pad M₂`, the weight of `S` at `weight (−w)` is `−w(fst S)`, and

  `minCommonBaseWeight (pad M₁) (pad M₂) (weight (−w)) = −maxCommonIndepWeight M₁ M₂ w`.

*Proof.*  Step 1, by Theorem 9(2) a common base `S` of the padded matroids has `fst S` common
independent, so its weight `−w(fst S)` is at least `−max`.  Step 2, a common independent set `X`
of greatest weight, with `Y ⊆ E` of `m − |X|` elements (`exists_subset_card_eq`), gives the
common base `X × {1} ∪ Y × {2}` of weight `−w(X) = −max`.  Step 3, Lemma 11.

### 1.9 The circuit of Step 4

**Proposition 16.**  `negB_impl`, `negRunB_impl`, `negNegCircuit_spec`.  For a signed tropical
circuit `D` on `E`, `negNegCircuit D` computes `u = −w` (`m` gates `0 − w_e`), runs `D` on `u`
and negates its first output: exactly `m + |D| + 1` gates, output `−D(−w)₀`.

### 1.10 Part (2): the maximum weight of a common independent set

**Theorem 17 (Theorem `thm:D`, second part).**  `theoremD_commonIndep`, `size_commonIndep_le`.
With rank circuits `C₁`, `C₂` of sizes `s₁`, `s₂`, and no common base assumed, a signed tropical
circuit of size at most `1664 · 8192 m⁸ (s₁ + s₂ + 268m + 51) + m + 3 ≤
1664 · 2613249 m⁸ (s₁ + s₂ + m) + 3` outputs the maximum weight of a common independent set at
every `w ∈ ℝ^E`.

*Proof.*  Step 1, Theorem 13 for `pad M₁`, `pad M₂` on `2m` elements, with the common base of
Theorem 15 and the rank circuit `doubleRankCircuit (padRankCircuit C₁) (padRankCircuit C₂)
r(pad M₂)` of at most `(s₁ + 74m + 18) + (s₂ + 74m + 18) + 58 · 2m + 15` gates (Theorems 5 and
9), gives a circuit `D` with at most `1664 (2m)³ (4m)⁵ (s₁ + s₂ + 268m + 51) + 2` gates that
outputs the least weight of a common base of the padded matroids.  Step 2,
`negNegCircuit (weightCircuit D)` outputs `−D(weight(−w)) = maxCommonIndepWeight M₁ M₂ w`
(Theorem 15) with `m + |D| + 1` gates.  Step 3, for `m ≥ 1`, `s + 268m + 51 ≤ 319(s + m)` and
`m ≤ 1664 m⁸ (s + m)`, and `8192 · 319 + 1 = 2613249`.

### 1.11 Theorem D

**Theorem 18 (Theorem `thm:D`).**  `theoremD`.  With rank circuits of sizes `s₁`, `s₂` and a
common base, a signed tropical circuit of size at most `1664 · 2400 m⁸ (s₁ + s₂ + m) + 2` outputs
the minimum weight of a common base, and one of size at most `1664 · 2613249 m⁸ (s₁ + s₂ + m) + 3`
outputs the maximum weight of a common independent set, at every `w ∈ ℝ^E`.

*Proof.*  Theorems 14 and 17.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `thm:D` Step 2: `r_N(A × {1} ∪ B × {2}) = r₁(A) + \|B\| + r₂(E \ B) − r₂(E)`, size `s₁ + s₂ + O(m)` | `double_rankCircuit`, `doubleRankCircuit`, `doubleRankCircuit_rank`, `doubleRankCircuit_spec`, `doubleRankCircuit_size`, `doubleRankCircuit_size_le`, `dualB_impl`, `doubleB_impl`, `queryB_impl` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Steps 1 and 3: Theorem C on `N`, read at the weights `w_e` and `0` | `exists_minCommonBase_circuit`, `weightCircuit`, `weightCircuit_spec` | `Rainbow/TheoremD` | proved |
| `thm:D` (1), size `O(m⁸(s₁ + s₂ + m))` | `theoremD_commonBase`, `minCommonBaseWeight`, `isLeast_minCommonBaseWeight`, `size_commonBase_le` | `Rainbow/TheoremD` | proved |
| `thm:D` Step 4: the padded matroids `M_i'`, their bases, their rank circuits `min(r_i(S ∩ E) + \|S ∩ Z\|, m)` | `loops`, `pad`, `indep_double_loops`, `rank_double_loops`, `isBase_pad_iff`, `padRankCircuit`, `padRankCircuit_rank`, `padRankCircuit_size_le`, `truncRankCircuit_rank` | `Rainbow/TheoremDRank` | proved |
| `thm:D` Step 4: `max w(X) = −min w'(B)`, `Z` a common base | `minCommonBaseWeight_pad`, `exists_commonBase_pad`, `sum_weight_neg` | `Rainbow/TheoremD` | proved |
| `thm:D` Step 4: `m` negations for `−w` and one for the output | `negNegCircuit`, `negNegCircuit_spec`, `negB_impl`, `negRunB_impl` | `Rainbow/TheoremD` | proved |
| `thm:D` (2), size `O(m⁸(s₁ + s₂ + m))` | `theoremD_commonIndep`, `maxCommonIndepWeight`, `isGreatest_maxCommonIndepWeight`, `size_commonIndep_le` | `Rainbow/TheoremD` | proved |
| `thm:D` | `theoremD` | `Rainbow/TheoremD` | proved |
| `thm:D`, uniformity | none | | not formalized |


## 3. Differences from the paper

1. Size of Step 2.  The paper gives `s₁ + s₂ + O(m)`; the Lean circuit has exactly
   `s₁ + s₂ + m + popCost m + 35⌈log₂(m+1)⌉ + 15 ≤ s₁ + s₂ + 58m + 15` gates, including the `m`
   negations that feed `E \ B` to the second rank circuit and the subtraction of `r₂(E)`.
2. Output widths.  The given rank circuits may have any number of outputs; the construction
   keeps `⌈log₂(m+1)⌉` of them, which carry the rank since `r(S) ≤ m`.
3. The constant `r₂(E)` is a parameter of the construction, which the generator computes by one
   evaluation of `C₂`.
4. The padded matroids live on `E × {1, 2}`, the second copies playing the paper's `Z`; the
   direct sum with the free matroid on `Z` is `double M (loops m)`, as the dual of the matroid of
   loops is free.
5. Explicit sizes in Theorem D: `1664 · 2400 m⁸ (s₁ + s₂ + m) + 2` and
   `1664 · 2613249 m⁸ (s₁ + s₂ + m) + 3`, with the constant `1664` of Theorem C
   (`theoremC_final`: `1664 k³ m⁵ (s + m) + 2`).  The second part runs Theorem C on the doubled
   padded matroids, `4m` elements and `2m` blocks, hence the larger constant.
6. The second part of `thm:D` does not use the common base; `theoremD_commonIndep` states it
   without that hypothesis.
7. Uniformity is not formalized, as for Theorem C.


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/TheoremDRank.lean` | 322 |
| `SignedTropical/Rainbow/TheoremD.lean` | 362 |
