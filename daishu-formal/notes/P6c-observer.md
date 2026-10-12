# P6c: the observer (Lemma `lem:observer`) and Theorem C

Natural-language companion of three modules:

* `SignedTropical/Rainbow/ObserverOracle.lean` (phase 1), namespace
  `SignedTropical.Rainbow.Observer`: Lemma `lem:observer`, Steps 1, 2, 3 (the context of `G` and
  the independence oracle of `N_G`) and the fact used in Step 5;
* `SignedTropical/Rainbow/Observer.lean` (phase 2), same namespace: Steps 4 and 5 and the whole
  Lemma `lem:observer`, composing phase 1 with the matroid intersection circuit of agent P6b
  (`Rainbow/MICircuit.lean`), on the `m · m` input bits in the pair indexing of
  `Rainbow/GapUpdate.lean`;
* `SignedTropical/Rainbow/TheoremCFinal.lean` (phase 2), namespace
  `SignedTropical.Rainbow.TheoremCFinal`: the observers discharge the hypothesis
  `TheoremC.IsObserver` of agent P7, which gives Theorem `thm:C` unconditionally.

Source: `daishu/paper/greedy_intersection.tex`, Lemma `lem:observer` and Theorem `thm:C`.

Imports.  `ObserverOracle`: `Rainbow/POSLRank.lean` (P4: `POG`, `linkG`, `uG`, `NG`, `Gt`,
`clusterG`, `repsG`, `belowG`, `mem_POG_iff`, `uG_lt_uG_iff`, `rk_NG`, `NG_univ`),
`BoolAlg/Count.lean` and `BoolAlg/Rel.lean` (P6a: `Impl` and its combinators, `runB_set_fit`,
`numLtB_impl`, `numSubB_impl`, `numSumB_impl`, `numEqB_impl`, `vecPopcountB_impl`,
`vecFirstB_impl`, `warshallB_impl`, `warshallV_eq_true_iff`).  `Observer`: `ObserverOracle`,
`Rainbow/MICircuit.lean` (P6b: `avGuardB_impl`, `avGuardV_eq`, `miCost_add_le`) and
`Rainbow/GapUpdate.lean` (coordinator: `pairOf`).  `TheoremCFinal`: `Observer` and
`Rainbow/TheoremC.lean` (P7: `IsObserver`, `theoremC`, `theoremC_bigO`, `rank_le_card`).

Build status: `lake build SignedTropical.Rainbow.ObserverOracle`,
`lake build SignedTropical.Rainbow.Observer` and `lake build SignedTropical.Rainbow.TheoremCFinal`
succeed with no error and no warning.  No `sorry`, `admit`, `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe` or `opaque`.  `#print axioms` of the 26 main theorems of
phase 1 and of the 9 of phase 2 (`inputRel_pairOf`, `obsB_impl`, `obsCost_le`,
`obsCost_le_bigO`, `lem_observer`, `isObserver_observer`, `observer_size_le`, `theoremC_final`,
`theoremC_final_poly`): `propext`, `Classical.choice`, `Quot.sound` only.


## Notation

`E = Fin m`; `M` a matroid on `E` with ground set `E` (hypothesis `hE`); `r = rk M`.  `C` is a
Boolean circuit of size `s = C.size` that outputs the binary digits of the rank of `M`
(hypothesis `hB`, the hypothesis of Theorem `thm:A`:
`∀ S, (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk S`).  `W = ⌈log₂(m+1)⌉`
(`Nat.size m`).  A relation `G ⊆ E × E` is carried by its bits `R = relBits G`,
`R g f = [(g, f) ∈ G]` (`relR m`, `m²` operands).  From P4: `PO_G = {f : f ∉ cl{g : (g, f) ∉ G}}`,
the links (`x, y ∈ PO_G` in one component with `(x, y), (y, x) ∈ G`), the clusters
(`SameCluster M (POG M G) (linkG G)`, reflexive on `PO_G`), `cluster_G(x)`, the representatives
`repsG M G` (the least element of each cluster), `Below_G(x)` (`belowG`), `u_G`, `N_G = M^{u_G}`,
`G_t = {(e, f) : v_f - v_e ≤ t}`.


## 1. Results

### 1.1 The context of a relation

**Definition 1.**  `OrdP M G x y` (the order of Step 2): `x` and `y` lie in one component,
`x ∈ PO_G`, and `y ∉ PO_G` or (`x`, `y` lie in different clusters and `(x, y) ∉ G`).
`belowP M G x = {y : OrdP M G y x}`, the set `Below(x)`.  The context of `G` (`ctxOf M G`, a
structure `Ctx m`) has the fields

* `rel`: the bits of `G`;
* `po`: the bits of `PO_G`;
* `cl x y`: `x` and `y` lie in one cluster;
* `ord x y`: `OrdP M G x y`;
* `rep x`: `x ∈ repsG M G`;
* `lev x y`: `x ∈ repsG M G` and `y ∈ cluster_G(x)`;
* `rkb x`: `r(Below(x))`.

**Proposition 2 (Lemma `lem:observer`, Step 2, the order).**  `ordP_iff`, `mem_belowP_Gt`,
`belowP_eq_belowG`.

(a) At `G = G_t`, `t ≥ 0`: `OrdP M G x y` iff `x`, `y` lie in one component and
`u_G(x) < u_G(y)`.
(b) So at `G = G_t`, `t ≥ 0`, `Below(x)` is the set of elements of the component of `x` with
smaller `u_G`, the set `Below(x)` of Step 3.
(c) For every `G` and `x ∈ PO_G`, `Below(x) = Below_G(x)`, the set of the rank formula `rk_NG`.

*Proof.*  Step 1, (a): by `uG_lt_uG_iff` (P4), for `x`, `y` in one component, `u_G(x) < u_G(y)`
iff `x ∈ PO_G ∌ y`, or `x, y ∈ PO_G` lie in different clusters with `(x, y) ∉ G`; splitting on
`y ∈ PO_G`, this is the second and third conjuncts of `OrdP`.  Step 2, (b) from (a) and the
symmetry of `connRel`.  Step 3, (c): for `x ∈ PO_G` the alternative `x ∉ PO_G` of `OrdP M G y x`
is excluded, and `SameCluster` is symmetric since the links are; what remains is
`y ∈ PO_G`, `connRel x y`, `x`, `y` in different clusters, `(y, x) ∉ G`, the definition of
`belowG`.

### 1.2 The values computed by the circuits

**Definition 3.**  For bits `R` of a relation, `P` of a set and `Cl`, `Ord` of relations:

* `poV M R f = [r({g : ¬R g f}) < r({g : ¬R g f} ∪ {f})]`;
* `linkV M R P x y = [x, y in one component] ∧ (R x y ∧ R y x) ∧ (P x ∧ P y)`;
* `clV M R P x y = P x` if `x = y`, and `warshallV (linkV M R P) x y` otherwise;
* `ordV M R P Cl x y = [x, y in one component] ∧ P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))`;
* `repV Cl x = leadV (Cl x) x`: `Cl x x` and no `y < x` has `Cl x y`;
* `levV Cl x y = repV Cl x ∧ Cl x y`;
* `rkbV M Ord x = r({y : Ord y x})`;
* `ctxV M R`: the context with fields `R`, `P = poV M R`, `Cl = clV M R P`,
  `Ord = ordV M R P Cl`, `repV Cl`, `levV Cl`, `rkbV M Ord`;
* the rank query `rankNV M D A = Σ_{x ∈ E} (r({y : D.ord y x} ∪ (A ∩ {y : D.lev x y})) - D.rkb x)`,
  with the subtraction in `ℕ`;
* the oracle `oracleV M D A = [rankNV M D A = |A|]`.

**Theorem 4 (Lemma `lem:observer`, Steps 1 and 2).**  `poV_relBits`, `linkV_eq_true_iff`,
`clV_relBits`, `ordV_relBits`, `repV_eq`, `levV_eq`, `rkbV_eq`, `ctxV_relBits`.  For every relation `G`
(not only `G = G_t`), `ctxV M (relBits G) = ctxOf M G`: the context computed from the bits of `G`
is the context of `G`.

*Proof.*  Step 1, `PO`: `{g : ¬R g f} = X_f = {g : (g, f) ∉ G}` and the second set of `poV` is
`X_f ∪ {f}` (`filter_not_relBits`, `filter_ite_relBits`); `f ∈ PO_G` iff `r(X_f) < r(X_f ∪ {f})`
(`mem_POG_iff`, P4).  Step 2, links: `linkV` is true iff `x`, `y` are linked
(`linkV_eq_true_iff`).  Step 3, clusters: `x` lies in the cluster of `x` iff `x ∈ PO_G`; for
`x ≠ y`, `x` and `y` lie in one cluster iff the transitive closure of the links relates them,
since a nonempty chain of links starts in `PO_G` (`sameCluster_iff_transGen_of_ne`), and
Warshall's algorithm computes the transitive closure (`warshallV_eq_true_iff`, P6a).  Step 4,
order: `P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))` is `x ∈ PO_G ∧ (y ∉ PO_G ∨ (x, y in different clusters
∧ (x, y) ∉ G))`.  Step 5, representatives: `leadV (Cl x) x` holds iff `x ∈ PO_G` (the cluster
bit on the diagonal) and no element of the cluster of `x` is smaller than `x`, which is
`mem_repsG` (P4).  Step 6, `{y : [OrdP M G y x]} = Below(x)`.

### 1.3 Step 3: the rank of `N_G` and independence

**Theorem 5 (Lemma `lem:observer`, Step 3, the rank queries).**  `filter_term_ctxOf`,
`rankNV_ctxOf`, `rankNV_correct`, `rankNV_correct_indicator`.  Let `t ≥ 0`, `D = ctxOf M G_t`
and `A ⊆ E`.  Then `rankNV M D A`, that is
`Σ_{x ∈ E} (r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x)))` with `Below(x) = {y : D.ord y x}` and
`Lev(x) = {y : D.lev x y}` (the cluster of `x` if `x` is a representative, `∅` otherwise), is
`r_{N_{G_t}}(A)`.  The same holds at the context `ctxV M (relBits G_t)` computed from the bits of
`G_t`, and in particular `rankNV M (ctxV M (relBits G_t)) (indicator S) = r_{N_{G_t}}(S)` for every
`S ⊆ E`.

*Proof.*  Step 1, the set of the rank query of `x` is `Below(x) ∪ (A ∩ cluster_G(x))` if
`x ∈ repsG`, and `Below(x)` otherwise (`filter_term_ctxOf`).  Step 2, for `x ∉ repsG` the term
is `r(Below(x)) - r(Below(x)) = 0`.  Step 3, a representative lies in `PO_G`, so
`Below(x) = Below_G(x)` (Proposition 2(c)), and the term of `x` is the term of `rk_NG`.  Step 4,
the sum over the representatives is `r_{N_{G_t}}(A)` by `rk_NG` (P4, valid at `G = G_t`,
`t ≥ 0`).  Step 5, `ctxV M (relBits G_t) = ctxOf M G_t` (Theorem 4), and the set of entries of
`indicator S` is `S`.

**Theorem 6 (correctness of the oracle).**  `indep_iff_rk_eq_card`, `oracleV_ctxOf`,
`oracle_correct`.  For every `v : E → ℝ`, every `t ≥ 0` and every `A ⊆ E` (a vector of bits),
`oracleV M (ctxV M (relBits G_t)) A = [A is independent in N_{G_t}]`.

*Proof.*  Step 1, the rank query is `r_{N_{G_t}}(A)` (Theorem 5).  Step 2, a finite set is
independent iff its rank is its size (Mathlib, `indep_iff_eRk_eq_encard_of_finite`).

**Theorem 7 (Lemma `lem:observer`, Step 5).**  `Gt_eq_univ`, `Gt_eq_univ_of_le`, `oracle_univ`,
with `NG_univ` (P4).  (a) If `v_f - v_e ≤ t` for all `e`, `f`, in particular if
`t ≥ max v - min v` (written `(⨆ e, v e) - (⨅ e, v e) ≤ t`), then `G_t = E × E`.  (b) For every
`A`, `oracleV M (ctxV M (relBits (E × E))) A = [A is independent in M]`.

*Proof.*  Step 1, (a): `(e, f) ∈ G_t` iff `v_f - v_e ≤ t`; and `v_f ≤ ⨆ v`, `⨅ v ≤ v_e` since
the range of `v` is finite.  Step 2, (b): `E × E = G_0` for `v = 0`, so Theorem 6 applies at
`v = 0`, `t = 0`, and `N_{E × E} = M` (`NG_univ`, P4).

### 1.4 The circuits

**Theorem 8 (the circuits and their sizes).**  All counts are exact (`Impl` of P6a: the builder
appends exactly that many gates and its result carries the stated value).

| builder | from | value | gates | Lean |
| :-- | :-- | :-- | :-- | :-- |
| `rankB C` | vector `V` | `r({i : V i})` on `W` bits | `s` | `rankB_impl` |
| `poB C` | `R` | `poV M R` | `1 + m(m + 2s + 5W + 2)` | `poB_impl` |
| `linksB M` | `(R, P)` | `linkV M R P` | `3m²` | `linksB_impl` |
| `clB M` | `(R, P)` | `clV M R P` | `3m² + 2m³` | `clB_impl` |
| `ordB M` | `(R, P, Cl)` | `ordV M R P Cl` | `4m²` | `ordB_impl` |
| `repB` | `Cl` | `repV Cl` | `3m²` | `repB_impl` |
| `levB` | `(Rep, Cl)` | `Rep x ∧ Cl x y` | `m²` | `levB_impl` |
| `rkbB C` | `Ord` | `rkbV M Ord` | `ms` | `rkbB_impl` |
| `ctxB M C` | `R` | `ctxV M R` | `ctxCost m s` | `ctxB_impl` |
| `rankTermB C x` | `(D, A)` | term of `x` | `2m + s + 13W + 1` | `rankTermB_impl` |
| `rankNB C` | `(D, A)` | `rankNV M D A` on `2W` bits | `rankNCost m s` | `rankNB_impl` |
| `oracleB C` | `(D, A)` | `oracleV M D A` | `oracleCost m s` | `oracleB_impl` |

with `ctxCost m s = 2m³ + 12m² + m(3s + 5W + 2) + 1 ≤ 3ms + 21m³ + 1` (`ctxCost_le`),
`rankNCost m s = m(2m + s + 13W + 1) + 22mW ≤ ms + 38m²` (`rankNCost_le`) and
`oracleCost m s = rankNCost m s + popCost m + 10W + 1 ≤ ms + 70m² + 1` (`oracleCost_le`).
Contexts are carried by `ctxR m` (`CtxA`, `CtxRep`): bits for the relations and sets, `W` bits
for each rank `r(Below(x))`.

*Proof.*  Step 1, `rankB`: `runB_set_fit` (P6a) with `f = r`; `hB` gives
`bitsVal (C.eval (indicator S)) = r(S)`, and `r(S) ≤ |S| ≤ m < 2^W` (`rk_lt_two_pow`).
Step 2, `poB`: one gate `true`, shared; for each `f` the `m` negations of column `f`, a rank
query on `{g : ¬R g f}`, one on the same vector with entry `f` replaced by `true`, and
`numLtB` on `W` bits (`5W + 2`).  Step 3, `linksB`, `clB`: three `∧` gates per pair; the pairs
in different components are replaced by the constant `false`, a choice fixed by `M` that costs
no gate (`connMask_impl`); Warshall's algorithm (`2m³`, `warshallB_impl`); the diagonal is
replaced by the operands of `P` (free).  Step 4, `ordB`: four gates per pair
(`Cl x y ∨ R x y`, `P y ∧ ·`, `¬·`, `P x ∧ ·`) and the component choice; `repB`: least-index
selection in every row (`3m` each) and the diagonal; `levB`: one `∧` per entry; `rkbB`: one rank
query per `x`, on column `x` of `Ord`.  Step 5, `ctxB`: the stages in sequence, each reading the
results of earlier stages, which persist when gates are appended (`Rep.mono`); the counts add.
Step 6, `rankTermB`: the vector `{y : D.ord y x} ∪ (A ∩ {y : D.lev x y})` (`m` gates `∧`, `m` gates
`∨`), a rank query (`s`), and `numSubB` on `W` bits (`13W + 1`); `rankNB`: the `m` terms and
their sum on `2W` bits (`numSumB`, `22mW`); `oracleB`: the rank query, `|A|` (`vecPopcountB`,
`popCost m`) and `numEqB` on `2W` bits (`10W + 1`).  Step 7, the bounds: `W ≤ m`
(`size_le_self`), `popCost m ≤ 22m` (`popCost_le`).

**Theorem 9 (Lemma `lem:observer`, Steps 1 to 3, packaged).**  `lem_observer_oracle`.  Under
`hB` and `hE`: `Impl (relR m) (ctxR m) (ctxB M C) (ctxCost m s) (ctxV M)`;
`Impl ((ctxR m).prod (vecR m)) bitR (oracleB C) (oracleCost m s) (fun P => oracleV M P.1 P.2)`;
`ctxCost m s ≤ 3ms + 21m³ + 1`; `oracleCost m s ≤ ms + 70m² + 1`; for every `v`, `t ≥ 0`, `A`,
`oracleV M (ctxV M (relBits (Gt v t))) A = decide ((NG M (Gt v t)).Indep A)`; and for every `A`,
`oracleV M (ctxV M (relBits univ)) A = decide (M.Indep A)`.

*Proof.*  Theorems 6, 7 and 8.

### 1.5 Lemma `lem:observer` (`Observer.lean`)

**Theorem 10 (the input).**  `inputRel`, `inputRel_pairOf`.  The observer reads `m · m` input
bits; input `i` is the bit `[pairOf i ∈ G]`, where `pairOf = finProdFinEquiv.symm` indexes the
ordered pairs as in Lemma `lem:oneupdate` (`GapUpdate.pairOf`).  The bits of the relation are
read as `R g f = X(finProdFinEquiv (g, f))` (`inputRel X`), and on the input vector of `G` they
are the bits of `G`: `inputRel (i ↦ [pairOf i ∈ G]) = relBits G`.

*Proof.*  `pairOf (finProdFinEquiv (g, f)) = (g, f)`.

**Theorem 11 (the circuit).**  `obsV`, `obsB`, `obsB_impl`, `observer`, `obsCost`.  The builder
`obsB M C blk r₀` reads the relation (free), computes its context (`ctxB`, Steps 1 to 3), and runs
the matroid intersection circuit of P6b with the oracle `oracleB` (`avGuardB`, Step 4: `k`
rounds of the augmenting path algorithm, one more exchange graph for `Av`, the guard and the
`k` output gates).  It computes `obsV M blk r₀` with exactly
`obsCost m k s r₀ = ctxCost m s + miCost m k (oracleCost m s) r₀ + k` gates.  The circuit
`observer M C blk r₀ : Circuit BoolOp (m * m)` is this builder applied to the inputs
(`vecCircuit`).

*Proof.*  `Impl.free`, `ctxB_impl`, `oracleB_impl` and `avGuardB_impl` (P6b), composed with
`Impl.comp`; the counts add.

**Theorem 12 (the size).**  `obsCost_le`, `obsCost_le_bigO`.  (a) For all `m, k, s, r₀`:
`obsCost m k s r₀ ≤ (k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(r₀+1)⌉`.
(b) For `m ≥ 1` and `r₀ < k`: `obsCost m k s r₀ ≤ 800 k m³ (s + m)`.

*Proof.*  Step 1, (a): `miCost m k q r₀ + k ≤ (k+1)(m+1)²(q + 10(m+1)) + 5⌈log₂(r₀+1)⌉`
(`miCost_add_le`, P6b) with `q = oracleCost m s ≤ ms + 70m² + 1` (`oracleCost_le`), and
`ctxCost m s ≤ 3ms + 21m³ + 1` (`ctxCost_le`).  Step 2, (b): for `m ≥ 1` and `k ≥ 1`,
`(k+1)(m+1)² ≤ 8km²` and `ms + 70m² + 10m + 11 ≤ 91m(s + m)`, so the first term is at most
`728 k m³ (s + m)`; `3ms + 21m³ ≤ 24 k m³ (s + m)`; `5⌈log₂(r₀+1)⌉ ≤ 5r₀ ≤ 5k ≤ 5 k m³ (s + m)`;
and `1 ≤ k m³ (s + m)`.  Together `758 k m³ (s + m) ≤ 800 k m³ (s + m)`.

**Theorem 13 (Lemma `lem:observer`).**  `lem_observer`.  Let `M` be a matroid on `E = Fin m`
with ground set `E`, `blk : E → Fin k` the blocks, and `C` a Boolean circuit of size `s` that
outputs the binary digits of the rank of `M` (`hB`).  For every `r₀ ∈ ℕ`, the circuit
`observer M C blk r₀` on the `m · m` inputs `[pairOf i ∈ G]`:

1. has `obsCost m k s r₀` gates, at most
   `(k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(r₀+1)⌉`, which is at most
   `800 k m³ (s + m)` for `m ≥ 1` and `r₀ < k` (Theorem 12(b));
2. has `k` outputs;
3. for every `v : E → ℝ` and every `t ≥ 0`, at the input vector of `G_t` outputs the list
   `(F_b(G_t))_{b < k}`, `F_b(G) = [ν(N_G) ≤ r₀] ∧ [b ∈ Av(N_G)]`; in Lean,
   `(observer M C blk r₀).eval boolInterp (fun i => decide (GapUpdate.pairOf i ∈ Gt v t)) =
   List.ofFn fun b : Fin k => decide (nu (NG M (Gt v t)) blk ≤ r₀ ∧ b ∈ Av (NG M (Gt v t)) blk)`,
   which is the body of P7's `TheoremC.IsObserver M blk r₀`;
4. (Step 5) if `M` has a rainbow base, `rank M = k` and `r₀ < k`, then at `G = E × E` every
   output is `0`: the outputs at the input vector of `univ` are `List.replicate k false`.

*Proof.*  Step 1, `vecCircuit_spec` (P6a) turns `obsB_impl` into a circuit with `obsCost` gates,
`k` outputs and the outputs `List.ofFn (obsV M blk r₀ X)`.  Step 2, at the input vector of
`G_t`, the relation read is `relBits G_t` (Theorem 10), and at its context the oracle answers
independence in `N_{G_t}` (`oracle_correct`, Theorem 6); so `avGuardV_eq` (P6b) gives output `b`
equal to `[ν(N_{G_t}) ≤ r₀] && [b ∈ Av(N_{G_t})]`, which is `decide` of the conjunction
(`Bool.decide_and`).  Step 3, `E × E = G_0` for `v = 0` (`Gt_eq_univ`), `N_{E × E} = M`
(`NG_univ`), and `ν(M) = k` (`nu_eq_iff`, P0a: rank `k` and a rainbow base); since `r₀ < k`, the
guard `[k ≤ r₀]` is false at every `b`.

### 1.6 Theorem C (`TheoremCFinal.lean`)

**Theorem 14.**  `isObserver_observer`, `observer_size_le`, `theoremC_final`,
`theoremC_final_poly`.

(a) For every `r`, `observer M B blk r` satisfies `TheoremC.IsObserver M blk r` (P7).
(b) For `m ≥ 1` and `r < k`, its size is at most `800 k m³ (s + m)`, `s = B.size`.
(c) **Theorem `thm:C`.**  Let `M` be a matroid on `E = Fin m` with ground set `E`, `rank M = k`,
a rainbow base for `blk`, and let the Boolean circuit `B` of size `s` output the binary digits of
the rank of `M`.  Then there is a signed tropical circuit `C` on `m` inputs with
`|C| ≤ 2436 k⁴ m⁶ (s + m) + 2` and `C(w) = Opt(w)` for every `w ∈ ℝ^E`.
(d) The same with the explicit bound of P7's `theoremC`:
`|C| ≤ R(3m² s_O + km² + 6m⁴ + 2m² + m + k) +
(3ms + m⌈log₂(k+1)⌉ + 9m² + 5m + 4⌈log₂(k+1)⌉ + k + 2)` with
`s_O = (k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(k+1)⌉` and `R = rounds k m`
(`Schedule.rounds`, at most `(⌊m²/4⌋ + 1)⌊k(k-1)/2⌋` and at most `k³ m`).

*Proof.*  Step 1, (a) is Theorem 13(3), the definition of `IsObserver`.  Step 2, (b) is
Theorem 12(b) with Theorem 13(1).  Step 3, (c): P7's `theoremC_bigO` with the observers
`observer M B blk r` and `c = 800`; for `1 ≤ r < k`, `m ≥ rank M = k > 1`
(`rank_le_card`), so (b) applies; `3 · 800 + 36 = 2436`.  Step 4, (d): P7's
`theoremC` with `s_O`, since `⌈log₂(r+1)⌉ ≤ ⌈log₂(k+1)⌉` for `r < k` and Theorem 13(1).


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer` Step 1: `PO` by two rank runs per `f` and a comparison | `poV`, `poB`, `poB_impl`, `poV_relBits`, `rankB_impl` | `ObserverOracle` | proved |
| `lem:observer` Step 2: linkage bits within components | `linkV`, `linksB_impl`, `linkV_eq_true_iff`, `connMask_impl` | `ObserverOracle` | proved |
| `lem:observer` Step 2: Warshall's algorithm, `2m³` gates, clusters | `clV`, `clB_impl`, `clV_relBits`, `sameCluster_iff_transGen_of_ne` | `ObserverOracle` | proved |
| `lem:observer` Step 2: order bits `u(x) < u(y)` within components | `OrdP`, `ordV`, `ordB_impl`, `ordV_relBits`, `ordP_iff` | `ObserverOracle` | proved |
| `lem:observer` Step 2: representative of least index | `repV`, `repB_impl`, `repV_eq`, `levV`, `levB_impl`, `levV_eq` | `ObserverOracle` | proved |
| `lem:observer` Step 3: `Below(x)`, the elements of the component with smaller `u` | `belowP`, `mem_belowP_Gt`, `belowP_eq_belowG` | `ObserverOracle` | proved |
| `lem:observer` Step 3: `r_{N_G}(A)` as a sum of rank differences | `rankNV`, `rankNV_ctxOf`, `rankNV_correct`, `filter_term_ctxOf` (with `rk_NG` of P4) | `ObserverOracle` | proved |
| `lem:observer` Step 3: one rank query, `2ms + O(m²)` gates (here `ms + O(m²)`) | `rankTermB_impl`, `rankNB_impl`, `rankNCost_le`, `rkbB_impl` | `ObserverOracle` | proved |
| `lem:observer` Step 4: independence test, one rank query | `oracleV`, `oracleB_impl`, `oracleCost_le`, `oracleV_ctxOf`, `oracle_correct`, `indep_iff_rk_eq_card` | `ObserverOracle` | proved |
| `lem:observer` Steps 1 to 3 together, context computed once | `ctxOf`, `ctxV`, `ctxV_relBits`, `ctxB_impl`, `ctxCost_le`, `lem_observer_oracle` | `ObserverOracle` | proved |
| `lem:observer` Step 5: `E × E = G_t`, `N_{E × E} = M` | `Gt_eq_univ`, `Gt_eq_univ_of_le`, `oracle_univ`, `NG_univ` (P4) | `ObserverOracle`, `POSL` | proved |
| `lem:observer` Step 4: `k` rounds of the augmenting path algorithm, `Av`, the guard, with the oracle of Step 3 | `obsB`, `obsB_impl`, `obsV` (with P6b's `avGuardB_impl`, `avGuardV_eq`) | `Observer` | proved |
| `lem:observer`: "reads a relation `G ⊆ E × E`" (`m · m` input bits, pair indexing of `lem:oneupdate`) | `inputRel`, `inputRel_pairOf`, `observer` | `Observer` | proved |
| `lem:observer`: "a Boolean circuit of size `O(km³(s+m))`" | `obsCost`, `obsCost_le`, `obsCost_le_bigO` | `Observer` | proved |
| `lem:observer`: "the outputs are correct whenever `G = G_t`", Step 5 "`F_b(E × E) = 0`" | `lem_observer` | `Observer` | proved |
| proof of `thm:C`: the observers of `lem:observer` (hypothesis `IsObserver` of P7) | `isObserver_observer`, `observer_size_le` | `TheoremCFinal` | proved |
| `thm:C` | `theoremC_final` (`2436 k⁴m⁶(s+m) + 2`), `theoremC_final_poly` | `TheoremCFinal` | proved (uniformity: see P7's notes) |


## 3. Differences from the paper

1. **Step 1 needs `m²` negations.**  The set `{g : (g, f) ∉ G}` is the complement of column `f`
   of the input, so its indicator vector costs `m` negation gates for each `f`.  Step 1 costs
   `1 + m(m + 2s + 5⌈log₂(m+1)⌉ + 2)` gates, `m(2s + m + O(log m))`, not `m(2s + O(log m))`; the
   total of the lemma is unchanged.  Proposed wording: "\emph{Step 1, $\PO$.}  For each $f$,
   evaluate the rank circuit on $\{g:(g,f)\notin G\}$ ($m$ negations) with and without $f$ and
   compare: $m(2s+m+O(\log m))$ gates."
2. **Step 3, one rank run per query and representative.**  The ranks `r(Below(x))` do not
   depend on `A`; computing them once (`ms` gates, in the context) leaves one rank run per `x`
   in each query, `ms + O(m²)` gates instead of `2ms + O(m²)`.  The paper's count is a correct
   upper bound for its own procedure.  Optional wording: "One query costs $2ms+O(m^{2})$ gates,
   or $ms+O(m^{2})$ after the ranks $r(\mathrm{Below}(x))$, which do not depend on $A$, are
   computed once."
3. **Representatives without masking numbers.**  Instead of summing over the representatives,
   the rank query sums over all `x` with `Lev(x) = ∅` for `x` not a representative, whose term
   is `r(Below(x)) - r(Below(x)) = 0`.  No change to the paper.
4. **Clusters on the diagonal.**  Warshall's algorithm gives the transitive closure of the links;
   the clusters are reflexive on `PO_G`, so the diagonal is set to the bits of `PO_G` (free).  At
   `G = G_t`, `t ≥ 0`, the diagonal links are present anyway.  No change to the paper.
5. **Steps 1 and 2 hold for every relation.**  `ctxV_relBits` holds for every `G`; only Step 3
   (`rk_NG`) needs `G = G_t`, `t ≥ 0`, which is the case the lemma needs.  No change.
6. **Independence: the rank query, not a level-by-level test.**  The oracle compares the rank
   query of Step 3, `r_{N_G}(A)`, with `|A|`, as in the paper ("independence tests, one rank
   query each").  A level-by-level criterion, "`A` is independent iff
   `r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x)) = |A ∩ Lev(x)|` for every representative `x`", is
   false without the condition `A ⊆ PO_G`: elements outside `PO_G` are loops of `N_G`.  Example:
   `M = U_{1,2}` on `{0, 1}`, `v = (0, 2)`, `t = 1`; then `G_t = {(0,0), (1,1), (1,0)}`,
   `PO = {0}`, the only representative is `0` with `Below(0) = ∅`, and `A = {1}` passes the test,
   while `1` is a loop of `N_G` (`u_G = (1, 3)`).  The paper does not use this criterion.
7. **The input.**  The observer reads all `m · m` ordered pairs, the diagonal included, in the
   pair indexing `pairOf = finProdFinEquiv.symm` of the formalized Lemma `lem:oneupdate`
   (`GapUpdate`), where `D⁺_{ee} = 0` puts the diagonal in every sublevel set; the paper's
   Lemma `lem:oneupdate` uses the `m(m-1)` pairs `e ≠ f`.  Lemma `lem:observer` ("reads a relation
   `G ⊆ E × E`") needs no change.
8. **`r₀` arbitrary.**  The circuit and its outputs at `G_t` are formalized for every `r₀ ∈ ℕ`;
   `r₀ < k` is used only for `F_b(E × E) = 0` and for the bound `800 k m³ (s + m)`, and `r₀ ≥ 1`
   is never used.  No change.
9. **Step 5.**  `F_b(E × E) = 0` uses `ν(M) = k > r₀`, that is, rank `k`, a rainbow base and
   `r₀ ≤ k - 1` (the standing hypotheses of Section 4 and of the lemma).  Optional wording for
   Step 5: "At $G=E\times E$ the matroid is $M$, which has a rainbow base, so $\nu(M)=k>r_0$ and
   the guard is $0$."
10. **The size.**  The total of Step 4 is confirmed with explicit constants (Theorem 12):
   `(k+1)(m+1)²(q + 10(m+1)) + 5⌈log₂(r₀+1)⌉` for Step 4 with `q ≤ ms + 70m² + 1` gates per
   independence test, plus `3ms + 21m³ + 1` for Steps 1 to 3, at most `800 k m³ (s + m)`.  No
   change needed; agent P6b's optional wording for Step 4 (notes/P6b-micircuit.md, Section 3,
   item 3) applies, with `q = ms + O(m²)` (difference 2 above).
11. **Theorem C.**  The formal bound is `2436 k⁴ m⁶ (s + m) + 2`, which is
   `O(k⁴ m⁶ (s + m))` as stated.  Uniformity is not formalized (agent P7's notes).  No change.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/ObserverOracle.lean` | 832 |
| `SignedTropical/Rainbow/Observer.lean` | 191 |
| `SignedTropical/Rainbow/TheoremCFinal.lean` | 80 |


## 5. Not done

* Every item of both phases is proved: Steps 1 to 5 of Lemma `lem:observer`, the lemma itself in
  the form of P7's `TheoremC.IsObserver`, its size bounds, and Theorem `thm:C` unconditionally.
* Uniformity of the circuit family in Theorem `thm:C` is not formalized (agent P7, difference 5
  of notes/P7-theoremC.md).


## 6. API for later agents

### 6.1 Lemma `lem:observer` and Theorem C (phase 2)

* `observer M C blk r₀ : Circuit BoolOp (m * m)` (`Observer`), input `i` the bit
  `[GapUpdate.pairOf i ∈ G]`.
* `lem_observer hE hB blk r₀`: `(observer M C blk r₀).size = obsCost m k C.size r₀ ∧
  (observer M C blk r₀).size ≤ (k + 1) * (m + 1) ^ 2 * (m * C.size + 70 * m ^ 2 + 10 * m + 11) +
  3 * m * C.size + 21 * m ^ 3 + 1 + 5 * Nat.size r₀ ∧ (observer M C blk r₀).outs.length = k ∧
  (∀ v t, 0 ≤ t → (observer M C blk r₀).eval boolInterp (fun i => decide (GapUpdate.pairOf i ∈
  Gt v t)) = List.ofFn fun b : Fin k => decide (nu (NG M (Gt v t)) blk ≤ r₀ ∧
  b ∈ Av (NG M (Gt v t)) blk)) ∧ ((∃ B, IsRainbowBase M blk B) → rank M = k → r₀ < k →
  (observer M C blk r₀).eval boolInterp (fun i => decide (GapUpdate.pairOf i ∈
  (univ : Finset (Fin m × Fin m)))) = List.replicate k false)`.
* `obsCost m k s r₀ = ctxCost m s + (miCost m k (oracleCost m s) r₀ + k)`; `obsCost_le m k s r₀`
  (the polynomial above); `obsCost_le_bigO (hm : 1 ≤ m) (hr : r₀ < k) : obsCost m k s r₀ ≤
  800 * (k * m ^ 3 * (s + m))`.
* `obsB M C blk r₀`, `obsB_impl hB blk r₀ : Impl (vecR (m * m)) (vecR k) (obsB M C blk r₀)
  (obsCost m k C.size r₀) (obsV M blk r₀)`; `inputRel X g f = X (finProdFinEquiv (g, f))`,
  `inputRel_pairOf G : inputRel (fun i => decide (GapUpdate.pairOf i ∈ G)) = relBits G`.
* `TheoremCFinal.isObserver_observer hE B hB blk r : TheoremC.IsObserver M blk r
  (observer M B blk r)`; `TheoremCFinal.observer_size_le hE B hB blk (hm : 1 ≤ m) (hr : r < k) :
  (observer M B blk r).size ≤ 800 * (k * m ^ 3 * (B.size + m))`.
* `TheoremCFinal.theoremC_final hE hk hM B hB : ∃ C : Circuit STOp m, C.size ≤ 2436 * (k ^ 4 *
  m ^ 6 * (B.size + m)) + 2 ∧ ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w]`
  (`hE : M.E = Set.univ`, `hk : rank M = k`, `hM : ∃ B, IsRainbowBase M blk B`, `hB` the rank
  hypothesis of `theoremA` for `B`); `TheoremCFinal.theoremC_final_poly`: the same with the
  explicit polynomial of Theorem 14(d).

### 6.2 Steps 1 to 3 (phase 1)

Namespace `SignedTropical.Rainbow.Observer`; `open SignedTropical SignedTropical.BoolAlg
SignedTropical.Rainbow.POSL`.  `M : Matroid (Fin m)`, `C : Circuit BoolOp m`, `n` the number of
inputs of the circuit being built (implicit).  `hB` is the rank hypothesis of Theorem `thm:A`; in
the theorems that use it, it is the first explicit argument (before `hE`).

* `relBits G : Fin m → Fin m → Bool`, `relBits G g f = decide ((g, f) ∈ G)` (named apart from
  `GapUpdate.relOf`, which reads a relation from a set of pair indices in `Fin (m * m)`; in
  phase 2 the bits of `GapUpdate.relOf S` are the input bits of `S`, rearranged).
* `Ctx m` (values; fields `rel po cl ord rep lev rkb`), `CtxA m n` (operands, same fields),
  `ctxR m : Rep BoolOp Bool n (CtxA m n) (Ctx m)` (the context representation `R_D`; a context
  carried in `gs` is a `CtxRep gs s T`, with one field per component).
* `ctxB M C : (Fin m → Fin m → Arg n) → Bld BoolOp n (CtxA m n)`;
  `ctxB_impl hB : Impl (relR m) (ctxR m) (ctxB M C) (ctxCost m C.size) (ctxV M)`.
* `oracleB C : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (Arg n)`;
  `oracleB_impl hB : Impl ((ctxR m).prod (vecR m)) bitR (oracleB C) (oracleCost m C.size)
  (fun P => oracleV M P.1 P.2)`.
* `rankNB C : CtxA m n × (Fin m → Arg n) → Bld BoolOp n (List (Arg n))`;
  `rankNB_impl hB : Impl ((ctxR m).prod (vecR m)) (numR (Nat.size m + Nat.size m)) (rankNB C)
  (rankNCost m C.size) (fun P => rankNV M P.1 P.2)`.
* `ctxCost m s = 2 * m ^ 3 + 12 * m ^ 2 + m * (3 * s + 5 * Nat.size m + 2) + 1`,
  `ctxCost_le m s : ctxCost m s ≤ 3 * m * s + 21 * m ^ 3 + 1`;
  `rankNCost m s = m * (2 * m + s + 13 * Nat.size m + 1) + 22 * m * Nat.size m`,
  `rankNCost_le m s : rankNCost m s ≤ m * s + 38 * m ^ 2`;
  `oracleCost m s = rankNCost m s + popCost m + 10 * Nat.size m + 1`,
  `oracleCost_le m s : oracleCost m s ≤ m * s + 70 * m ^ 2 + 1`.
* `oracle_correct hE ht A : oracleV M (ctxV M (relBits (Gt v t))) A = decide ((NG M (Gt v t)).Indep
  ↑(univ.filter fun i => A i = true))` for `ht : 0 ≤ t` (classical `decide`).
* `rankNV_correct hE ht A : rankNV M (ctxV M (relBits (Gt v t))) A = rk (NG M (Gt v t))
  (univ.filter fun y => A y = true)`; `rankNV_correct_indicator hE ht S : rankNV M
  (ctxV M (relBits (Gt v t))) (indicator S) = rk (NG M (Gt v t)) S`.
* `oracle_univ hE A : oracleV M (ctxV M (relBits univ)) A = decide (M.Indep ↑(univ.filter fun i =>
  A i = true))`.
* `Gt_eq_univ (h : ∀ e f, v f - v e ≤ t) : Gt v t = univ`;
  `Gt_eq_univ_of_le (ht : (⨆ e, v e) - (⨅ e, v e) ≤ t) : Gt v t = univ`; `NG_univ hE` (P4).
* `ctxV_relBits G hE : ctxV M (relBits G) = ctxOf M G` (every `G`); `oracleV_ctxOf hE ht A`,
  `rankNV_ctxOf hE ht A` (at the context `ctxOf M (Gt v t)`).
* `lem_observer_oracle hB hE`: the conjunction of `ctxB_impl`, `oracleB_impl`, `ctxCost_le`,
  `oracleCost_le`, `oracle_correct` (for all `v`, `t ≥ 0`, `A`) and `oracle_univ`.
* Step 2 facts: `ordP_iff ht : OrdP M (Gt v t) x y ↔ connRel M x y ∧ uG M (Gt v t) x <
  uG M (Gt v t) y`; `mem_belowP_Gt ht : y ∈ belowP M (Gt v t) x ↔ connRel M x y ∧
  uG M (Gt v t) y < uG M (Gt v t) x`; `belowP_eq_belowG (hx : x ∈ POG M G)`.
* Smaller pieces: `rankB C`, `rankB_impl hB` (a rank query on `W` bits, `s` gates),
  `indep_iff_rk_eq_card N S`, `connMask_impl M` (component choice, free),
  the stage gadgets `poB_impl`, `clB_impl`, `ordB_impl`, `repB_impl`, `levB_impl`, `rkbB_impl`,
  `rankTermB_impl`.
* Composition from the bits of `G` to the oracle bit, checked in a scratch file:
  `(((ctxB_impl hB).pre (R := (relR m).prod (vecR m)) (g := Prod.fst) (G := Prod.fst)
  fun _ _ _ hs => hs.1).pair Impl.snd).comp (oracleB_impl hB)`, value
  `fun P => oracleV M (ctxV M P.1) P.2`, `ctxCost m s + 0 + oracleCost m s` gates.
