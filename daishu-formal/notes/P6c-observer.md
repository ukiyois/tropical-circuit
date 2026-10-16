# P6c: the observer (Lemma `lem:observer`) and Theorem C

Natural-language companion of three modules:

* `SignedTropical/Rainbow/ObserverOracle.lean`, namespace `SignedTropical.Rainbow.Observer`:
  Lemma `lem:observer`, Steps 1 and 2 (the context read from the event bits, and the exchange
  tests of `N(t)`);
* `SignedTropical/Rainbow/Observer.lean`, same namespace: Step 3 and the whole lemma, composing
  Steps 1 and 2 with the matroid intersection circuit (`Rainbow/MICircuit.lean`), on the
  `qn m = m + 2m²` event bits of `Rainbow/Events.lean`;
* `SignedTropical/Rainbow/TheoremCFinal.lean`: the observers discharge the hypothesis
  `TheoremC.IsObserver`, which gives Theorem `thm:C` unconditionally.

Source: `paper/greedy_intersection.tex`, Lemma `lem:observer` and Theorem `thm:C`.  The modules
use `Rainbow/Events.lean` (`Qv`, `qT`, `qB`, `qU`, `Kr`, `mem_PO_iff`, `sameCluster_iff`,
`ord_iff`), `Rainbow/POSLRank.lean` (`POG`, `linkG`, `uG`, `NG`, `Gt`, `clusterG`, `repsG`,
`belowG`, `uG_lt_uG_iff`, `rk_NG`) and `POSL.lean` (`u_eq_uG`, `PO_eq_POG`, `near_eq_linkG`,
`N_eq_NG`, `clusterRank_eq_of_sameCluster`).

Build: no error, no warning, no `sorry`; the theorems depend on `propext`, `Classical.choice`
and `Quot.sound` only.

Notation.  `E = Fin m`; `M` a matroid on `E` with ground set `E` (`hE`); `r = rk M`.  `C` is a
Boolean circuit of size `s` that outputs the binary digits of the rank of `M` (`hB`, the
hypothesis of Theorem `thm:A`).  `W = ⌈log₂(m+1)⌉`.  The event bits at `t` are `[Q_j ≤ t]`,
`Q = Qv M v` (entry times, merge values, order values; notes/P6d-events.md).  `G_t =
{(e, f) : v_f - v_e ≤ t}`; at `G = G_t`, `PO_G = PO_t`, the links of `G` are those at scale `t`,
and `N_G = N(t)` (Proposition `prop:posl`).


## 1. Results

### 1.1 The context

**Definition 1.**  `OrdP M G x y` (the order): `x`, `y` lie in one component, `x ∈ PO_G`, and
`y ∉ PO_G` or (`x`, `y` in different clusters and `(x, y) ∉ G`).
`belowP M G x = {y : OrdP M G y x}`.  The context `ctxOf M G : Ctx m` has the fields `po` (the
bits of `PO_G`), `cl x y` (one cluster), `ord x y` (`OrdP M G x y`) and `rkb x`
(`r(belowP M G x)`).

**Definition 2 (the context read from the event bits).**  `evCtxV M X`: `po x = false` at a loop
and `X(qT x)` otherwise; `cl x x = po x`, `cl x y = X(qB x y)` for `x ≠ y` joined (`Kr M x y`),
`false` otherwise; `ord x y = po x ∧ ¬X(qU x y)` for `Kr M x y`, `false` otherwise;
`rkb x = r({y : ord y x})` (`rkbV`).

**Theorem 3 (Step 1).**  `evPO_eq`, `evOrd_eq`, `evCtxV_eq`: for `t ≥ 0`,
`evCtxV M [Q ≤ t] = ctxOf M G_t`.

*Proof.*  `po`: `PO_t = PO_{G_t}`, loops lie in no `PO_t`, and `x ∈ PO_t ⟺ t_x ≤ t` for a nonloop
(`mem_PO_iff`).  `cl`: on the diagonal, one cluster iff `x ∈ PO_t`; off the diagonal,
`sameCluster_iff` (one cluster iff joined and `T_xy ≤ t`).  `ord`: for joined `x`, `y`,
`ord_iff`; otherwise `OrdP` fails, as `x ∈ PO_t` makes `x` a nonloop and `connRel x y` with
`x ≠ y` makes both nonloops (`kr_of_connRel`).  `rkb`: from `ord`.

### 1.2 Step 2: the exchange tests

**Lemma 4 (the clusters partition `PO_G`).**  `clusterG_eq`, `eq_of_mem_clusterG`,
`exists_repsG`, `sum_card_inter_clusterG_le`, `inter_clusterG_erase`.

**Lemma 5.**  `rk_union_le_add_card`, `belowP_eq_of_mem_clusterG` (at `G = G_t` the elements of
one cluster have the same `belowP`), `locV_ctxOf` (at the context of `G`,
`locV M y (ctxOf M G, 1_A) = [y ∈ PO_G] ∧ [r(belowP(y) ∪ (A ∩ cluster(y))) - r(belowP(y)) =
|A ∩ cluster(y)|]`).

**Theorem 6 (Step 2, the exchange tests are correct).**  `locV_exchOracle`: for every `v` and
`t ≥ 0`, `ExchOracle (fun y => locV M y) N_{G_t} (ctxOf M G_t)`.

*Proof.*  By `rk_NG`, `r_{N_G}(B) = Σ_{x ∈ repsG} κ_x(B)` with
`κ_x(B) = r(Below_G(x) ∪ (B ∩ cluster(x))) - r(Below_G(x)) ≤ |B ∩ cluster(x)|`, and the clusters
are disjoint, so `B` is independent iff every term is tight and `Σ_x |B ∩ cluster(x)| = |B|`.
If `y ∉ PO_G`, `y` lies in no cluster and the parts of `A` add to `|A - y| < |A|`.  If
`y ∈ cluster(x₀)`, the terms of `A` and `A - y` agree at every `x ≠ x₀`, and the test is the
tightness of the term of `x₀`.

### 1.3 The circuits

**Theorem 7.**  All counts are exact.

| builder | from | value | gates | Lean |
| :-- | :-- | :-- | :-- | :-- |
| `rankB C` | vector `V` | `r({i : V i})` on `W` bits | `s` | `rankB_impl` |
| `andNotB` | `(P, u)` | `P ∧ ¬u` | `2` | `andNotB_impl` |
| `ordsB M` | event bits `X` | the order bits of `evCtxV M X` | `2m²` | `ordsB_impl` |
| `rkbB C` | `Ord` | `rkbV M Ord` | `ms` | `rkbB_impl` |
| `evCtxB M C` | event bits `X` | `evCtxV M X` | `m(2m + s)` | `evCtxB_impl` |
| `locRankB C y` | `(D, A')` | `locRankV M y (D, A')` | `m + s + 13W + 1` | `locRankB_impl` |
| `locB C y` | `(D, A)` | `locV M y (D, A)` | `locCost m s` | `locB_impl` |

with `locCost m s = s + 2m + 18W + popCost m + 3 ≤ s + 42(m + 1)` (`locCost_le`).  The bits of
`PO` and of the clusters are chosen from the event bits by the fixed loops and components, at no
gate (`poArg`, `poArg_rep`, `clArg_rep`).  `lem_observer_oracle` collects `evCtxB_impl`,
`locB_impl`, `locCost_le` and the correctness at the event bits (`evCtxV_eq` with
`locV_exchOracle`).

### 1.4 Lemma `lem:observer` (`Observer.lean`)

**Theorem 8.**  `obsV`, `obsB`, `obsB_impl`, `observer`, `obsCost`, `obsCost_le`,
`obsCost_le_bigO`, `lem_observer`.  The circuit `observer M C blk r₀` reads the `qn m` event
bits, computes the context (`evCtxB`), and runs the matroid intersection circuit with `r₀ + 1`
rounds and the exchange tests `locB C` (`avGuardB`).  It has exactly
`obsCost m k s r₀ = m(2m) + ms + miCost m k (r₀ + 1) (locCost m s) r₀ + k` gates, at most
`(r₀+2)(m+1)²(s + 52(m+1)) + ms + 2m² + 3k(m+1) + 5⌈log₂(r₀+1)⌉`, which is at most
`424 (r₀ + 2) m² (s + m)` for `1 ≤ m`, `k ≤ m`, `r₀ < k`.  It has `k` outputs, and for every
`v` and `t ≥ 0`, at the event bits `[Q ≤ t]` they are `[ν(N(t)) ≤ r₀] ∧ [b ∈ Av(N(t))]`
(`evCtxV_eq`, `avGuardV_eq` with `locV_exchOracle` and `r₀ < r₀ + 1`, `POSL.N_eq_NG`).

*Proof of the bound `424 (r₀ + 2) m² (s + m)`.*  `(m+1)² ≤ 4m²` and `s + 52(m+1) ≤ 104(s + m)`
bound the first term by `416 (r₀ + 2) m² (s + m)`; `ms`, `2m²`, `3k(m+1) ≤ 6m²` and
`5⌈log₂(r₀+1)⌉ ≤ 5m` add to at most `16 m²(s + m) ≤ 8 (r₀ + 2) m² (s + m)`.

### 1.5 Theorem C (`TheoremCFinal.lean`)

**Theorem 9.**  `isObserver_observer`: `observer M B blk r` satisfies
`TheoremC.IsObserver M blk r`.  `observer_size_le`: its size is at most
`424 (r + 2) m² (s + m)` for `1 ≤ m`, `k ≤ m`, `r < k`.  **Theorem `thm:C`**
(`theoremC_final`): under `hE`, `rank M = k`, a rainbow base and `hB`, a signed tropical circuit
of size at most `3328 k³ m⁴ (s + m) + 2` computes `Opt(w)` at every `w`.  `theoremC_final_poly`:
the same with the explicit polynomial `Σ_{r<k} stageLength k m r · (6m s_O(r) + updOver m k s)
+ (output part)`, `s_O(r)` the bound of Theorem 8.  `theoremC_final_rankOne`: when every
component of `M` has rank at most one, `1390 k³ m³ (s + m) + 2`.

*Proof.*  `TheoremC.theoremC_bigO` with `c = 424`: `40 |C| ≤ (294 · 424 + 8440) k³m⁴(s + m) +
80 ≤ 40 · 3328 k³m⁴(s + m) + 80`; `TheoremC.theoremC_bigO_rankOne`: `2 |C| ≤
(6 · 424 + 236) k³m³(s + m) + 4 = 2 · 1390 k³m³(s + m) + 4`.


## 2. Correspondence table

| paper | Lean | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer`, the query values `𝒬(v)` | `Events.Qv`, `qT`, `qB`, `qU` | `Events` | definition |
| Step 1: the context from the event bits | `evCtxV`, `evPO_eq`, `evOrd_eq`, `evCtxV_eq`, `ordsB_impl`, `evCtxB_impl`, `rkbB_impl` | `ObserverOracle` | proved |
| Step 2: `Below(y)`, `Lev(y)`, the terms `κ_x`, the partition into clusters | `belowP`, `mem_belowP_Gt`, `belowP_eq_belowG`, `belowP_eq_of_mem_clusterG`, `clusterG_eq`, `eq_of_mem_clusterG`, `exists_repsG`, `sum_card_inter_clusterG_le`, `rk_union_le_add_card` (with `rk_NG`) | `ObserverOracle` | proved |
| Step 2: the exchange test and its correctness, `q = s + O(m)` | `locV`, `locV_ctxOf`, `locV_exchOracle`, `locB_impl`, `locCost_le` | `ObserverOracle` | proved |
| Step 3: `r₀ + 1` rounds with the tests of Step 2 | `obsB`, `obsB_impl`, `obsV` (with `avGuardB_impl`, `avGuardV_eq`) | `Observer` | proved |
| the size `O(r₀ m² (s + m))` | `obsCost`, `obsCost_le`, `obsCost_le_bigO` | `Observer` | proved |
| the lemma | `lem_observer` | `Observer` | proved |
| proof of `thm:C`: the observers | `isObserver_observer`, `observer_size_le` | `TheoremCFinal` | proved |
| `thm:C` | `theoremC_final` (`3328 k³m⁴(s+m) + 2`), `theoremC_final_poly`, `theoremC_final_rankOne` (`1390 k³m³(s+m) + 2`) | `TheoremCFinal` | proved (uniformity: notes/P7-theoremC.md) |


## 3. Differences from the paper

1. **The condition `y ∈ PO` in the test is needed.**  Elements outside `PO` are loops of `N(t)`
   in no cluster.  Example: `M = U_{1,2}` on `{0, 1}`, `v = (0, 2)`, `t = 1`; then `PO = {0}`,
   and `A = {1}` has no term that fails while `1` is a loop.  The paper's test includes
   `y ∈ PO`.
2. **Pairs that are not joined.**  The event bits of such pairs are read from the query value
   `0` and masked by the fixed components; the paper states the same convention.
3. **`r₀` arbitrary.**  The circuit and its outputs at the event bits hold for every `r₀`;
   `r₀ < k` is used only for the bound `424 (r₀ + 2) m² (s + m)` (with `k ≤ m`).


## 4. Line counts

| module | lines |
| :-- | :-- |
| `ObserverOracle.lean` | 631 |
| `Observer.lean` | 152 |
| `TheoremCFinal.lean` | 99 |
