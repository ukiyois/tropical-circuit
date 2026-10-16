# P6d: event levels and the compiler at given levels

Natural-language companion of two modules:

* `SignedTropical/Rainbow/Events.lean`, namespace `SignedTropical.Rainbow.Events`: Lemma
  `lem:events` (the event levels of PO-SL) and the query values read by the observer;
* `SignedTropical/LevelCompiler.lean`, namespace `SignedTropical`: Corollary `cor:levels` (the
  compiler of Theorem `thm:compiler` run at levels computed inside the circuit).

Source: `paper/greedy_intersection.tex`, Lemma `lem:events` (end of Section 4.5) and Corollary
`cor:levels` (Section 2).  `Compiler.lean` states the one-gap specification `gapB_spec` and its
iteration `gapsB_spec` for query values `Q` and levels `Λ` carried by different operands; the
compiler of Theorem `thm:compiler` is the case `Q = Λ = D`.

Build: no error, no warning, no `sorry`; `bott_inLev`, `uval_inLev`, `levVal_eq` and the theorems
that use them depend on `propext`, `Classical.choice` and `Quot.sound` only.

Notation.  `E = Fin m`, `M` a matroid on `E`, `v : E → ℝ`, `t ≥ 0`.  `PO_t`, the links
`near v t` and the clusters `SameCluster M (PO M v t) (near v t)` are those of Definition
`def:posl` (`Rainbow/POSL.lean`).  `Kr M a b`: `a` and `b` are nonloops of one component (the
paper's *joined*).


## 1. Results

### 1.1 The gap sum of an antitone threshold (`gapSum_antitone`)

Statement.  Let `D ≥ 0` and let `φ` be antitone on the subsets of `E` with `¬φ(E)`.  Then the gap
sum of `[φ]` at `D` is a sorted value `s_j`, and for every `t ≥ 0`, `φ(G_t(D))` holds iff
`t < s_j`.

Proof.  Step 1, `j` is the least index with `¬φ(G_{s_j}(D))`; it exists as `G_{s_m}(D) = E`.
Step 2, the sets `G_{s_i}(D)` increase with `i` (`threshSet_mono`), so `φ(G_{s_i}(D))` holds iff
`i < j`, and the gap sum telescopes to `s_j - s_0 = s_j` (`sum_range_sub`).  Step 3, for
`s_j ≤ t`, `G_{s_j}(D) ⊆ G_t(D)`, so `¬φ(G_t(D))`; for `t < s_j`, `j ≥ 1` and every entry
`D_e ≤ t` is some `s_i` with `i ≤ j - 1` (`exists_sortedVal_eq`), so
`G_t(D) ⊆ G_{s_{j-1}}(D)` and `φ(G_t(D))`.

### 1.2 Entry times (`entry`, `entry_spec`, `mem_PO_iff`)

Statement.  For a nonloop `x`, with `D^x_g = max(v_x - v_g, 0)` (`dx`) and
`φ_x(S) = [x ∈ cl(E - S)]`, the entry time `t_x = C_{φ_x}(D^x)` satisfies `0 ≤ t_x` and
`x ∈ PO_t ⟺ t_x ≤ t` for `t ≥ 0`.  A loop lies in no `PO_t` (`notMem_PO_of_loop`).

Proof.  For `t ≥ 0`, `E - G_t(D^x) = {g : v_g < v_x - t}` (`coe_compl_sublevel_dx`), and
`φ_x` is antitone with `¬φ_x(E)` as `x` is not a loop; 1.1 applies.

### 1.3 Merge times (`fwV`, `thr_fwV`, `fwV_le_iff`, `bott`, `sameCluster_iff`)

The weights: `W_aa = t_a`, `W_ab = max(t_a, t_b, |v_a - v_b|)` for `a ≠ b` (`wgt`).  The
Floyd–Warshall algorithm over `(min, max)` restricted to a transitive relation `K` (`fwStep`,
`fwV`) replaces `T_ab` by `min(T_ab, max(T_ac, T_cb))` for the pivots `c` with `K a c`, `K c b`.

* `thr_fwStep`, `thr_fwV`: at every `t`, the bits `[K a b ∧ T_ab ≤ t]` after a round are one
  round of Warshall's algorithm (`BoolAlg.warshallStep`) on the bits before it; so the bits of
  `fwV K W` are `warshallV` of the bits of `W`.
* `fwV_le_iff`: for `K a b`, `fwV K W a b ≤ t` iff a chain of entries `K` with `W ≤ t` joins `a`
  and `b` (`warshallV_eq_true_iff`).
* `fwV_congr`, `fwV_of_not`: the algorithm reads only the entries `K`, and leaves the other
  entries unchanged.
* `link_iff`: the links at scale `t ≥ 0` are the entries `Kr` with `W ≤ t` (by 1.2).
* `sameCluster_iff`: `x`, `y` lie in one cluster at `t ≥ 0` iff `Kr M x y` and `T_xy ≤ t`, where
  `T = bott M v = fwV (Kr M) W`.
* `bott_comm`, `bott_le_max`, `entry_le_bott`, `entry_le_bott_right`, `bott_self`,
  `bott_le_wgt`: `T` is symmetric and ultrametric, `max(t_x, t_y) ≤ T_xy`, `T_xx = t_x`,
  `T_xy ≤ W_xy`.

### 1.4 The levels and the covering lemma (`lev`, `rho`, `bott_inLev`)

`ρ_x` is the least `T_xy` over the `y < x` with `Kr M x y` (`lower`, `listMin`), and `0` if
there is none.  The levels `lev M v : Fin (m + m) → ℝ` are `t_x` (`0` at a loop, `tz`) and `ρ_x`.
`InLev Λ q`: `q = 0` or `q` is an entry of `Λ`.

Statement (`bott_inLev`).  Every `T_xy`, `Kr M x y`, is a level or `0`.

Proof.  Let `h = T_xy` and `C = {z : Kr M x z, T_xz ≤ h}`.  If some `z ∈ C` has `t_z = h`, done.
Otherwise every `z ∈ C` has `t_z < h`.  Let `z₀ = min C`.  One of `x`, `y`, say `w`, has
`T_{z₀w} ≥ h` (else `T_xy < h` by the ultrametric inequality).  The class
`P = {z ∈ C : T_wz < h}` contains `w` (`T_ww = t_w < h`) and not `z₀`; let `z = min P`, so
`z₀ < z`.  Every `y' < z` joined to `z` has `T_{zy'} ≥ h` (else `y' ∈ P`), and
`T_{z z₀} = h` (`≤ h` by the ultrametric inequality, `≥ h` as `z₀ ∉ P`).  So `ρ_z = h`
(`listMin_eq`).

### 1.5 The order values (`uval`, `uval_inLev`, `ord_iff`)

`U_xy = max(t_x, t_y, min(T_xy, v_y - v_x))` (the paper's `ω_xy`).

* `uval_inLev`: `U_xy` is a level or `0`, for `Kr M x y`: if `min(T_xy, v_y - v_x) ≤ max(t_x, t_y)`
  it is `t_x` or `t_y`; if `T_xy ≤ v_y - v_x` it is `T_xy`; and `max(t_x, t_y) < v_y - v_x < T_xy`
  is impossible, as then `T_xy ≤ W_xy = v_y - v_x`.
* `ord_iff`: for `Kr M x y` and `t ≥ 0`, `x ∈ PO_t ∧ (y ∉ PO_t ∨ (x, y in different clusters ∧
  v_y - v_x > t))` iff `t_x ≤ t < U_xy`.

### 1.6 The query values (`qn`, `qT`, `qB`, `qU`, `bq`, `uq`, `Qv`, `Qv_inLev`)

`Qv M v : Fin (qn m) → ℝ`, `qn m = m + (m·m + m·m)`: the entry times `tz`, the merge values `bq`
(`T_xy` for `Kr M x y`, `0` otherwise) and the order values `uq` (`U_xy` for `Kr M x y`, `0`
otherwise), at the indices `qT x`, `qB x y`, `qU x y`.  `Qv_inLev`: every query value is a level
or `0`.  `lev_nonneg`: the levels are nonnegative.

### 1.7 The compiler at given levels (`levB`, `levB_spec`, `levCost_le`, `levVal_eq`)

Statement.  `levB B d lam` sorts the levels `Λ` carried by `lam` (`isortB`) and runs `gapB` for
each of the `L` gaps with the query values `Q` carried by `d`: exactly
`levCost B L = 3 L(L-1)/2 + L(1 + 4q + Σ liftCost + N)` gates, at most
`3L²/2 + L(1 + 4q + 3s + N)` (`levCost_le`).  For `Λ ≥ 0` and every `Q_j` among
`s_0 = 0, s_1, …, s_L`, output `u` is `Σ_{k<L} Δ_k F_u([Q ≤ s_k])` (`levVal_eq`).

Proof.  The membership value of `Q_j` at gap `k` is `Δ_k [Q_j ≤ s_k]` (`bitQ_eq`): if
`Q_j ≤ s_k` it is `Δ_k`; otherwise `Q_j ≥ s_{k+1}` (`le_or_succ_le_of_eq`) and it is `0`.  The
lifted circuit then carries `Δ_k` times its Boolean outputs (`eval_liftInterp`), and the running
sums add up (`gapOutQ_eq`, `foldl_zipWith_ofFn`).


## 2. Correspondence table

| paper | Lean | module | status |
| :-- | :-- | :-- | :-- |
| `lem:events` (1), entry levels | `gapSum_antitone`, `entry`, `entry_spec`, `mem_PO_iff`, `notMem_PO_of_loop` | `Events` | proved |
| `lem:events` (2), merge levels | `wgt`, `fwStep`, `fwV`, `thr_fwV`, `fwV_le_iff`, `bott`, `link_iff`, `sameCluster_iff` | `Events` | proved |
| `lem:events` (3), covering | `lower`, `rho`, `lev`, `bott_inLev` | `Events` | proved |
| `lem:events` (4), order levels | `uval`, `uval_inLev`, `ord_iff` | `Events` | proved |
| `lem:oneupdate`, Step 2 (Floyd–Warshall computes `T`) | `fwV_congr`, `fwV_of_not` (with `OneUpdate.fw_eq_bq`) | `Events` | proved |
| the query values `𝒬(v)` of `lem:observer` | `Qv`, `Qv_inLev`, `lev_nonneg` | `Events` | proved |
| `cor:levels` | `levB`, `levB_spec`, `levCost_le`, `bitQ_eq`, `gapOutQ_eq`, `levVal_eq` | `LevelCompiler` | proved |


## 3. Differences from the paper

1. **The merge values.**  The paper defines `T_xy` as the least bottleneck over chains; Lean
   defines it as the output of the Floyd–Warshall algorithm (`bott`) and proves the threshold
   characterization `fwV_le_iff`, from which the chain reading follows.
2. **Pairs that are not joined.**  The query values of such pairs are `0` in Lean (`bq`, `uq`),
   and the observer masks them by the fixed components; the paper states the same convention in
   Lemma `lem:observer`.
3. **The size of `cor:levels`.**  The paper states `3L²/2 + L(1 + 4q + 3s + N)`, which is
   `levCost_le`; the exact count is `levCost`.


## 4. Line counts

| module | lines |
| :-- | :-- |
| `Rainbow/Events.lean` | 673 |
| `LevelCompiler.lean` | 173 |
