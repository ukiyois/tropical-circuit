# P6c: the observer (Lemma `lem:observer`) and Theorem C

Natural-language companion of three modules:

* `SignedTropical/Rainbow/ObserverOracle.lean`, namespace `SignedTropical.Rainbow.Observer`:
  Lemma `lem:observer`, Steps 1 to 3 (the context of `G` and the exchange tests of `N_G`) and
  the fact used in Step 5;
* `SignedTropical/Rainbow/Observer.lean`, same namespace: Steps 4 and 5 and the whole lemma,
  composing Steps 1 to 3 with the matroid intersection circuit (`Rainbow/MICircuit.lean`), on
  the `m · m` input bits in the pair indexing of `Rainbow/GapUpdate.lean`;
* `SignedTropical/Rainbow/TheoremCFinal.lean`: the observers discharge the hypothesis
  `TheoremC.IsObserver`, which gives Theorem `thm:C` unconditionally.

Source: `paper/greedy_intersection.tex`, Lemma `lem:observer` and Theorem `thm:C`.  The modules
use `Rainbow/POSLRank.lean` (`POG`, `linkG`, `uG`, `NG`, `Gt`, `clusterG`, `repsG`, `belowG`,
`mem_POG_iff`, `uG_lt_uG_iff`, `rk_NG`, `NG_univ`) and `POSL.lean` (`u_eq_uG`, `PO_eq_POG`,
`near_eq_linkG`, `clusterRank_eq_of_sameCluster`).

Build: no error, no warning, no `sorry`; the theorems depend on `propext`, `Classical.choice`
and `Quot.sound` only.

Notation.  `E = Fin m`; `M` a matroid on `E` with ground set `E` (`hE`); `r = rk M`.  `C` is a
Boolean circuit of size `s` that outputs the binary digits of the rank of `M` (`hB`, the
hypothesis of Theorem `thm:A`).  `W = ⌈log₂(m+1)⌉`.  A relation `G ⊆ E × E` is carried by its
bits `relBits G`, `R g f = [(g, f) ∈ G]`.  From `POSLRank`: `PO_G`, the links (`x, y ∈ PO_G` in
one component with `(x, y), (y, x) ∈ G`), the clusters `clusterG M G x`, the representatives
`repsG M G` (least element of each cluster), `Below_G(x)` (`belowG`), `u_G`, `N_G = M^{u_G}`,
`G_t = {(e, f) : v_f - v_e ≤ t}`, and the rank formula `rk_NG`: at `G = G_t`, `t ≥ 0`,
`r_{N_G}(A) = Σ_{x ∈ repsG} (r(Below_G(x) ∪ (A ∩ cluster(x))) - r(Below_G(x)))`.


## 1. Results

### 1.1 The context of a relation

**Definition 1.**  `OrdP M G x y` (the order of Step 2): `x`, `y` lie in one component,
`x ∈ PO_G`, and `y ∉ PO_G` or (`x`, `y` in different clusters and `(x, y) ∉ G`).
`belowP M G x = {y : OrdP M G y x}`.  The context `ctxOf M G : Ctx m` has the fields `po`
(the bits of `PO_G`), `cl x y` (one cluster), `ord x y` (`OrdP M G x y`) and `rkb x`
(`r(belowP M G x)`).

**Proposition 2 (Step 2, the order).**  `ordP_iff`, `mem_belowP_Gt`, `belowP_eq_belowG`.  At
`G = G_t`, `t ≥ 0`, `OrdP M G x y` iff `x`, `y` lie in one component and `u_G(x) < u_G(y)`; so
`belowP M G x` is the set of elements of the component of `x` with smaller `u_G`.  For every `G`
and `x ∈ PO_G`, `belowP M G x = belowG M G x`.

*Proof.*  `uG_lt_uG_iff`, the symmetry of `connRel` and of the clusters.

**Definition 3 (the values of the circuits).**  `poV M R f = [r({g : ¬R g f}) < r({g : ¬R g f}
∪ {f})]`; `linkV M R P x y = [one component] ∧ R x y ∧ R y x ∧ P x ∧ P y`; `clV M R P x y = P x`
for `x = y` and `warshallV (linkV M R P) x y` otherwise; `ordV M R P Cl x y = [one component] ∧
P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))`; `rkbV M Ord x = r({y : Ord y x})`; `ctxV M R` the context with
these fields.  The exchange test of `y` at a context `D` and bits `A`:

  `locV M y (D, A) = D.po y ∧ [(r({z : D.ord z y} ∪ A') - D.rkb y) mod 2^W = |A'|]`,
  `A' = A ∩ {z : D.cl y z}`,

the comparison being `indepOfRankV` of `BoolAlg/Count.lean` for the rank query
`locRankV M y (D, A') = r({z : D.ord z y} ∪ A') - D.rkb y`.

**Theorem 4 (Steps 1 and 2).**  `poV_relBits`, `linkV_eq_true_iff`, `clV_relBits`,
`ordV_relBits`, `rkbV_eq`, `ctxV_relBits`: for every relation `G`, `ctxV M (relBits G) =
ctxOf M G`.

*Proof.*  `PO`: `mem_POG_iff`.  Clusters: a nonempty chain of links starts in `PO_G`
(`sameCluster_iff_transGen_of_ne`), and Warshall's algorithm computes the transitive closure.
Order: `P x ∧ ¬(P y ∧ (Cl x y ∨ R x y))` is the second and third conjuncts of `OrdP`.

### 1.2 Step 3: the exchange tests

**Lemma 5 (the clusters partition `PO_G`).**  `clusterG_eq`: two clusters that share an element
are equal.  `eq_of_mem_clusterG`: representatives whose clusters share an element are equal.
`exists_repsG`: every `y ∈ PO_G` lies in the cluster of a representative (the least element of
its cluster).  `sum_card_inter_clusterG_le`: `Σ_{x ∈ repsG} |A ∩ cluster(x)| ≤ |A|`
(`card_biUnion` over disjoint clusters).  `inter_clusterG_erase`: `A ∩ cluster(x) =
(A - y) ∩ cluster(x)` for `y ∉ cluster(x)`.

**Lemma 6.**  `rk_union_le_add_card`: `r(S ∪ B) ≤ r(S) + |B|`.  `belowP_eq_of_mem_clusterG`: at
`G = G_t`, `t ≥ 0`, the elements of one cluster have the same `belowP` (one component, and `u_G`
is constant on clusters: `u_eq_uG`, `clusterRank_eq_of_sameCluster`).  `locV_ctxOf`: at the
context of `G`, `locV M y (ctxOf M G, 1_A) = [y ∈ PO_G] ∧ [r(belowP(y) ∪ (A ∩ cluster(y))) -
r(belowP(y)) = |A ∩ cluster(y)|]` (the rank is below `2^W`, `rk_lt_two_pow`).

**Theorem 7 (Step 3, the exchange tests are correct).**  `locV_exchOracle`, `locV_correct`:
for every `v` and `t ≥ 0`, `ExchOracle (fun y => locV M y) N_{G_t} (ctxV M (relBits G_t))`: for
`y ∈ A` with `A - y` independent in `N_{G_t}`, `locV M y (·, 1_A) = [A independent in
N_{G_t}]`.

*Proof.*  Write `T_x(B) = r(Below_G(x) ∪ (B ∩ cluster(x))) - r(Below_G(x))` and
`c_x(B) = |B ∩ cluster(x)|` for `x ∈ repsG`.  Step 1, `T_x(B) ≤ c_x(B)` (Lemma 6), and
`Σ_x c_x(B) ≤ |B|` (Lemma 5); with `rk_NG`, `B` is independent (`rk = |B|`,
`indep_iff_rk_eq_card`) iff `Σ_x T_x(B) = |B|`, which forces `T_x(B) = c_x(B)` for every `x`
(`sum_eq_sum_iff_of_le`) and `Σ_x c_x(B) = |B|`.  Step 2, apply Step 1 to `A - y`.  Step 3, if
`y ∉ PO_G`, then `y` lies in no cluster, `c_x(A) = c_x(A - y)`, and `Σ_x c_x(A) = |A - y| < |A|`,
so `A` is dependent; the test is `0`.  Step 4, if `y ∈ PO_G`, let `y ∈ cluster(x₀)`
(`exists_repsG`); then `cluster(y) = cluster(x₀)` and `belowP(y) = Below_G(x₀)`, so the test is
`[T_{x₀}(A) = c_{x₀}(A)]`.  If `A` is independent, Step 1 gives it.  Conversely, for `x ≠ x₀`,
`y ∉ cluster(x)` and `T_x(A) = T_x(A - y) = c_x(A - y) = c_x(A)`, while
`c_{x₀}(A) = c_{x₀}(A - y) + 1`; so `Σ_x T_x(A) = c_{x₀}(A) + Σ_{x ≠ x₀} c_x(A - y) =
Σ_x c_x(A - y) + 1 = |A|`.

**Theorem 8 (Step 5).**  `Gt_eq_univ`, `Gt_eq_univ_of_le`: `G_t = E × E` once
`t ≥ max v - min v`.

### 1.3 The circuits

**Theorem 9.**  All counts are exact.

| builder | from | value | gates | Lean |
| :-- | :-- | :-- | :-- | :-- |
| `rankB C` | vector `V` | `r({i : V i})` on `W` bits | `s` | `rankB_impl` |
| `poB C` | `R` | `poV M R` | `1 + m(m + 2s + 5W + 2)` | `poB_impl` |
| `linksB M` | `(R, P)` | `linkV M R P` | `3m²` | `linksB_impl` |
| `clB M` | `(R, P)` | `clV M R P` | `3m² + 2m³` | `clB_impl` |
| `ordB M` | `(R, P, Cl)` | `ordV M R P Cl` | `4m²` | `ordB_impl` |
| `rkbB C` | `Ord` | `rkbV M Ord` | `ms` | `rkbB_impl` |
| `ctxB M C` | `R` | `ctxV M R` | `ctxCost m s` | `ctxB_impl` |
| `locRankB C y` | `(D, A')` | `locRankV M y (D, A')` | `m + s + 13W + 1` | `locRankB_impl` |
| `locB C y` | `(D, A)` | `locV M y (D, A)` | `locCost m s` | `locB_impl` |

with `ctxCost m s = 2m³ + 8m² + m(3s + 5W + 2) + 1 ≤ 3ms + 17m³ + 1` (`ctxCost_le`) and
`locCost m s = s + 2m + 18W + popCost m + 3 ≤ s + 42(m + 1)` (`locCost_le`).  Contexts are
carried by `ctxR m` (`CtxA`, `CtxRep`).  The components are fixed data of `M`, so restricting the
link and order bits to one component costs no gate (`connMask_impl`).  `lem_observer_oracle`
collects `ctxB_impl`, `locB_impl`, the two bounds and `locV_correct`.

### 1.4 Lemma `lem:observer` (`Observer.lean`)

**Theorem 10.**  `inputRel`, `inputRel_pairOf`, `obsV`, `obsB`, `obsB_impl`, `observer`,
`obsCost`, `obsCost_le`, `obsCost_le_bigO`, `lem_observer`.  The circuit `observer M C blk r₀`
reads the relation from the `m · m` inputs (`inputRel`, free), computes its context, and runs
the matroid intersection circuit with `r₀ + 1` rounds and the exchange tests `locB C`
(`avGuardB`).  It has exactly `obsCost m k s r₀ = ctxCost m s + miCost m k (r₀ + 1) (locCost m s)
r₀ + k` gates, at most `(r₀+2)(m+1)²(s + 52(m+1)) + 3ms + 17m³ + 3k(m+1) + 1 + 5⌈log₂(r₀+1)⌉`,
which is at most `440 (r₀ + 2) m² (s + m)` for `1 ≤ m`, `k ≤ m`, `r₀ < k`.  It has `k` outputs;
for every `v` and `t ≥ 0`, at the input of `G_t` they are
`[ν(N_{G_t}) ≤ r₀] ∧ [b ∈ Av(N_{G_t})]` (`avGuardV_eq` with `locV_correct` and
`r₀ < r₀ + 1`); and (Step 5) at `G = E × E` they are `0` when `M` has a rainbow base,
`rank M = k` and `r₀ < k` (`NG_univ`, `ν(M) = k`).

*Proof of the bound `440 (r₀ + 2) m² (s + m)`.*  `(m+1)² ≤ 4m²` and `s + 52(m+1) ≤ 104(s + m)`
bound the first term by `416 (r₀ + 2) m² (s + m)`; each of `3ms`, `17m³`, `3k(m+1) ≤ 6m²`, `1`,
`5⌈log₂(r₀+1)⌉ ≤ 5m` is a multiple of at most `m²(s + m)`, `32 m²(s + m)` in all, and
`32 ≤ 16(r₀ + 2)`.

### 1.5 Theorem C (`TheoremCFinal.lean`)

**Theorem 11.**  `isObserver_observer`: `observer M B blk r` satisfies
`TheoremC.IsObserver M blk r`.  `observer_size_le`: its size is at most
`440 (r + 2) m² (s + m)` for `1 ≤ m`, `k ≤ m`, `r < k`.  **Theorem `thm:C`**
(`theoremC_final`): under `hE`, `rank M = k`, a rainbow base and `hB`, a signed tropical circuit
of size at most `1664 k³ m⁵ (s + m) + 2` computes `Opt(w)` at every `w`.  `theoremC_final_poly`:
the same with the explicit polynomial `Σ_{r<k} stageLength k m r · (3m² s_O(r) + km² + 6m⁴ +
2m² + m + k) + (output part)`, `s_O(r)` the bound of Theorem 10.  `theoremC_final_rankOne`:
when every component of `M` has rank at most one, `696 k³ m⁴ (s + m) + 2`.

*Proof.*  `TheoremC.theoremC_bigO` with `c = 440`: `40 |C| ≤ (147 · 440 + 1880) k³m⁵(s + m) +
80 = 40 · 1664 k³m⁵(s + m) + 80`; `TheoremC.theoremC_bigO_rankOne`: `2 |C| ≤
(3 · 440 + 72) k³m⁴(s + m) + 4 = 2 · 696 k³m⁴(s + m) + 4`.


## 2. Correspondence table

| paper | Lean | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer` Step 1 | `poV`, `poB_impl`, `poV_relBits`, `rankB_impl` | `ObserverOracle` | proved |
| Step 2: links, Warshall, clusters, the order of `u` | `linkV`, `clV`, `ordV`, `linksB_impl`, `clB_impl`, `ordB_impl`, `clV_relBits`, `ordV_relBits`, `ordP_iff` | `ObserverOracle` | proved |
| Step 3: `Below(y)`, `Lev(y)`, the terms `T_x`, the partition into clusters | `belowP`, `mem_belowP_Gt`, `belowP_eq_belowG`, `belowP_eq_of_mem_clusterG`, `clusterG_eq`, `eq_of_mem_clusterG`, `exists_repsG`, `sum_card_inter_clusterG_le`, `rk_union_le_add_card` (with `rk_NG`) | `ObserverOracle` | proved |
| Step 3: the exchange test and its correctness, `q = s + O(m)` | `locV`, `locV_ctxOf`, `locV_exchOracle`, `locV_correct`, `locB_impl`, `locCost_le` | `ObserverOracle` | proved |
| Steps 1 to 3, data computed once, `O(ms + m³)` | `ctxOf`, `ctxV_relBits`, `ctxB_impl`, `ctxCost_le`, `rkbB_impl`, `lem_observer_oracle` | `ObserverOracle` | proved |
| Step 4: `r₀ + 1` rounds with the tests of Step 3 | `obsB`, `obsB_impl`, `obsV` (with `avGuardB_impl`, `avGuardV_eq`) | `Observer` | proved |
| Step 5 | `Gt_eq_univ`, `Gt_eq_univ_of_le`, `NG_univ` | `ObserverOracle`, `POSL` | proved |
| the size `O(r₀ m² (s + m))` | `obsCost`, `obsCost_le`, `obsCost_le_bigO` | `Observer` | proved |
| the lemma | `lem_observer` | `Observer` | proved |
| proof of `thm:C`: the observers | `isObserver_observer`, `observer_size_le` | `TheoremCFinal` | proved |
| `thm:C` | `theoremC_final` (`1664 k³m⁵(s+m) + 2`), `theoremC_final_poly`, `theoremC_final_rankOne` (`696 k³m⁴(s+m) + 2`) | `TheoremCFinal` | proved (uniformity: notes/P7-theoremC.md) |


## 3. Differences from the paper

1. **Step 1 needs `m²` negations**, `m` per column of `G`; the paper's count
   `m(2s + m + O(log m))` includes them.
2. **Clusters on the diagonal.**  Warshall's algorithm gives the transitive closure of the links;
   the diagonal is set to the bits of `PO_G` (free).
3. **Steps 1 and 2 hold for every relation** (`ctxV_relBits`); only Step 3 (`rk_NG`) needs
   `G = G_t`, `t ≥ 0`.
4. **The condition `y ∈ PO` in the test is needed.**  Elements outside `PO_G` are loops of `N_G`
   in no cluster.  Example: `M = U_{1,2}` on `{0, 1}`, `v = (0, 2)`, `t = 1`; then `PO = {0}`,
   and `A = {1}` has no term that fails while `1` is a loop.  The paper's test includes
   `y ∈ PO`.
5. **The input.**  The observer reads all `m · m` ordered pairs in the indexing
   `pairOf = finProdFinEquiv.symm` of the formalized Lemma `lem:oneupdate`.
6. **`r₀` arbitrary.**  The circuit and its outputs at `G_t` hold for every `r₀`; `r₀ < k` is
   used only for Step 5 and for the bound `440 (r₀ + 2) m² (s + m)` (with `k ≤ m`).


## 4. Line counts

| module | lines |
| :-- | :-- |
| `ObserverOracle.lean` | 798 |
| `Observer.lean` | 191 |
| `TheoremCFinal.lean` | 101 |
