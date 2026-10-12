# Phase 2f: a bound on the last-stage iteration uniform in the weights (2026-10-12)

Question (phase 2c note, Section 9, item 1): bound `T_LS(w)`, the number of
last-stage (LS) blocks from `p = 0` until `nu0 = k`, by a function of `k` and `m`
alone, for all real `w`; or show that no such bound exists. Setting and labels:
`paper/greedy_intersection.tex`, Section 4; notes
`docs/phase2b-stage-length-2026-10-12.md` (B0), `docs/phase2c-laststage-2026-10-12.md`
(2c), `docs/phase2d-epoch-2026-10-12.md` (2d). This note does not touch `paper/`,
`daishu-formal/` or the other notes.

## Status log (for a relaunched agent)

- 2026-10-12 21:00, coordinator. Stopped at the user's direction: open conjecture,
  no proof. Nothing from this note goes into the paper or Lean.
- 19:14 start. Read 2c completely, paper Section 4, B0, 2d. Scripts go to
  `experiments/lsu_*.py`, logs to `experiments/lsu_logs/`. At most 4 workers.
- 19:40 exploration done (scripts `lsu_core.py`, `lsu_trace.py`, `lsu_search.py`,
  `lsu_overshoot.py`, `lsu_blockconst.py`, `lsu_bc_ties.py`; throwaway probes
  `lsu_tmp_*.py`, whose numbers are copied into Section 7). Refuted as potentials:
  no overshoot of the least dual optimum; order of the remaining offsets; ties of
  offsets persist; "a pair once in its final order stays so"; others (Section 7).
- 20:05 proved and checked: Theorem 2.1 (`k = 3`: `T_LS <= m`), Lemmas 3.1 to 3.3
  (offset decomposition `v_j = v* + (x_j)_blk` with `0 <= x_j <= G_j`, freezing,
  Lipschitz block), Proposition 4.1 (the local regime is a block-constant run on
  `M^{v*}` with linkage classes `K cap {v* = l}`), Corollary 4.2 (termination for
  real `w` reduces to block-constant runs), Proposition 5.1 (lower bound
  `T_LS = m + 6` at `k = 7`, refuting `T_LS <= m + 2`). Logs `lsu_logs/local_1.txt`,
  `bc_local_1.txt`, `lower_1.txt`, `search_low_*.txt`. No process left running.
- 20:20 checks logged: `k3_1.txt` (Theorem 2.1), `observe_1.txt` (Section 7),
  `fewvalues_1.txt`, `o2_instance.txt` (Instance LSU-1: every block raised in some
  step), `bc_local_1.txt`.
- 20:55 searches at 64 bits done (Section 7.3, no growth); Section 9 data
  (`finalgaps_1.txt`, `rankone_1.txt`, `rankone_ce.txt`: Instance LSU-2 refutes
  `T_LS <= k - 1` for rank-one components). Sections 0 to 10 written; no process left
  running.
- Open: a uniform bound for `k >= 4` (Section 8 has the precise gap).

## 0. Summary

1. **`k = 3` (Theorem 2.1).** `T_LS(w) <= m` for every real `w`, and `<= m - 1` when
   `nu(M^w) >= 2`; `m - 1` is attained. (2c, Corollary 3.3, with 2d, Corollary A.3.)
2. **Offset decomposition (Lemmas 3.1, 3.2).** Every LS run converges to a dual
   optimum `p*`, and with `v* = w - p*_blk`, `x_j = p* - p_j`, `G_j = Opt - Psi(p_j)`:
   `v_j = v* + (x_j)_blk` and `0 <= x_{j,b} <= G_j`. A pair whose final difference
   exceeds `G_j` keeps its order from step `j` on.
3. **The block is Lipschitz (Lemma 3.3):** `|a_b(v) - a_b(v')| <= 2m(m-1) ||v - v'||_inf`;
   the LS map is a continuous piecewise linear map.
4. **Local regime (Proposition 4.1).** Once `2 G_j < gamma`, the least nonzero final
   gap inside a component, the LS run is exactly the run of the block-constant
   problem `(M^{v*}, x_j)` with the PO-SL family whose linkage classes are
   `K cap {v* = l}`. So an LS run that does not terminate (Euclid-type cycle) would
   have to be a block-constant run (Corollary 4.2). On 171,721 block-constant runs of
   exactly this form, `T' <= min(k, #values of x)` (Section 6).
5. **Lower bound (Proposition 5.1).** `T_LS` can be `m + 6` (`k = 7`, `m = 14`), so
   the observation `T_LS <= m + 2` of 2c does not extend to larger `k`; in general
   `sup_w T_LS(w)` is at least the longest regular last stage.
6. **Refuted candidate potentials and observations** (Section 7.1: no overshoot of the
   least dual optimum, order of the offsets, pairs keep their final order, "some block
   is never raised" (Instance LSU-1), `T_LS <= V + 1`), and **searches** (Section 7.3):
   no growth with the bit length (10, 24, 40, 64 bits); at `k = 5`, `m = 10`, an LS run
   with 11 steps at `nu0 = 3`, 10 of them with a mismatch (a ladder).
7. **Components of rank one** (Section 9): `T_LS <= k - 1` holds on 6,333 runs but fails
   (Instance LSU-2: `k = 4`, `T_LS = 4`), so the LS gives no gain for the rank-one clause.
8. **Theorem `thm:C`:** the exact count stays `R(k, m)` for `k >= 4`; for `k = 3` the
   LS circuit needs `m` blocks (the same count as 2d's schedule). Section 8.

## 1. Setting

`M` has rank `k` on `E`, `|E| = m`, blocks `R_1, ..., R_k`, a rainbow base exists. The
LS iteration: `p_0 = 0`, `p_{j+1} = p_j + a(p_j)`, where `a(p)` is the stage-`(k-1)`
PO-SL block at the state `v = w - p_blk` (2c, Section 1):

```
a_b = int_0^inf [nu(N_v(t)) <= k - 1] [b in Av(N_v(t))] dt ,   tau = min{ t : nu(N_v(t)) = k } .
```

`T_LS(w)` is the least `j` with `nu(M^{v_j}) = k` (`infinity` if none). At
`nu(M^v) = k` the block is `0` (`nu(N_v(0)) = k` by (F1), so `tau = 0`), so the
sequence `p_j` is defined for all `j` and is constant from `T_LS(w)` on. Write
`v_j = w - (p_j)_blk`, `tau_j`, `a_j = a(p_j)`, and `G_j = Opt(w) - Psi(p_j) >= 0`
(Lemma `lem:duality`).

## 2. The case k = 3

**Theorem 2.1.** Let `k = 3`. For every `w in R^E`, `T_LS(w) <= m`, and
`T_LS(w) <= m - 1` if `nu(M^w) >= 2`. The value `m - 1` is attained.

*Proof.* Step 1, the first step. If `nu(M^{v_0}) = 1`, then `nu(M^{v_1}) >= 2` (2c,
Corollary 3.3). Let `j0 = [nu(M^w) = 1]`, so `nu(M^{v_{j0}}) >= 2` and `j0 <= 1`.

Step 2, the last stage. At a state with `nu0 = 2 = k - 1` the integrand of the LS
block is `[nu(N_v(t)) <= 2][b in Av(N_v(t))]`, which is the integrand of the regular
stage-2 update (eq. `eq:update-integral` with `r = nu0 = 2`), and `nu0` does not
decrease (Theorem `thm:validity`(2)). So the steps `j0, j0 + 1, ...` are the regular
stage-2 updates from `v_{j0}` until `nu0 = 3`.

Step 3, counting. Stage 2 takes at most `m - 1` updates from every state with
`nu0 = 2` (2d, Corollary A.3). Hence

```
T_LS(w)  <=  j0 + (m - 1)  <=  1 + (m - 1)  =  m ,
```

and `j0 = 0` when `nu(M^w) >= 2`.

Step 4, attained. The three instances of 2d, Corollary A.3 (`m = 8, 9, 11`) have
`nu(M^w) = 2` and a stage 2 of `m - 1` updates; Step 2 makes `T_LS(w) = m - 1`
(checked below).

*Hypotheses used:* PO-SL ((F1) to (F5)); 2c, Corollary 3.3 (from B0, Theorem 2.1, and
2c, Theorem 3.2); Theorem `thm:validity`(2); 2d, Corollary A.3 (from B0, Theorem 2.1,
2d, Theorem A in sharp form, and Theorem `thm:potential`(1)). No integrality.

*Checked* (`lsu_k3.py 2 120`, log `lsu_logs/k3_1.txt`): the three tight instances give
`T_LS = 7, 8, 10` (`m = 8, 9, 11`); on 215,734 random rank-3 instances (graphic on 4
vertices, binary, uniform, sums; `m <= 11`; small, spread, exponential and ladder
weights) `T_LS <= m` (and `<= m - 1` when `nu(M^w) = 2`), the step from `nu0 = 1`
reaches `nu0 >= 2`, every step at `nu0 = 2` equals the regular update
(`stage_core.update`), and `Psi = Opt` at the end: no failure. Discrimination: the
false bounds `T_LS <= m - 2` and `T_LS <= 3` fail 3 and 158 times.

**Formal statement (for Lean).** Data: a matroid `M` of rank `3` on `Fin m` with a
rainbow base, `blk : Fin m -> Fin 3`, `w : Fin m -> R`; `lsIter w j : Fin 3 -> R` the
LS iteration (`lsIter w 0 = 0`, `lsIter w (j+1) = lsIter w j + blockV M blk 2 (w - (lsIter w j)_blk)`
with `blockV` of `LastStage.lean`). Conclusion:
`exists j <= m, nu(M^{w - (lsIter w j)_blk}) = 3`, and `exists j <= m - 1` of the same
kind when `nu(M^w) >= 2`. Lemmas needed: 2c, Corollary 3.3 (needs 2c, Theorem 3.2 and
B0, Theorem 2.1) and 2d, Corollary A.3 (needs 2d, Theorem A and Lemma B.2).

## 3. The offset decomposition

**Lemma 3.1 (offsets).** For every `w in R^E`:
1. `0 <= a_{j,b} <= tau_j <= G_j - G_{j+1}` for all `j` and `b`;
2. `p* = lim_j p_j` exists, `Psi(p*) = Opt(w)` and `nu(M^{v*}) = k` with
   `v* = w - p*_blk`; if `T_LS(w) < infinity`, then `p* = p_{T_LS(w)}`;
3. `x_j = p* - p_j` satisfies `0 <= x_{j,b} <= G_j` and `v_j = v* + (x_j)_blk`.

*Proof.* Step 1, item 1. The integrand of `a_b` takes values in `{0, 1}` and vanishes
for `t >= tau_j` (by (F2), `nu(N(t)) = k` there), so `0 <= a_{j,b} <= tau_j`. By 2c,
Proposition 2.1, `Psi(p_{j+1}) - Psi(p_j) >= tau_j`, that is

```
tau_j  <=  Psi(p_{j+1}) - Psi(p_j)  =  G_j - G_{j+1} .
```

At `nu0 = k` both sides are `0`.

Step 2, increments. For `i <= j` and every `b`, by Step 1,

```
0  <=  p_{j,b} - p_{i,b}  =  sum_{l=i}^{j-1} a_{l,b}  <=  sum_{l=i}^{j-1} (G_l - G_{l+1})  =  G_i - G_j  <=  G_i .   (3.1)
```

So `p_j` is nondecreasing and bounded by `G_0` in each coordinate, and `p*` exists.

Step 3, the limit is a dual optimum. If `T_LS(w) < infinity`, `p* = p_T` and
`nu(M^{v*}) = k`, so `Psi(p*) = Opt(w)` (Lemma `lem:duality`). Otherwise 2c,
Theorem 5.1(3) gives `G_j <= (1 - 1/(k(2k-1)))^j G_0 -> 0`, and `Psi`, a minimum of
finitely many affine functions of `p`, is continuous, so `Psi(p*) = Opt(w)`. If
`nu(M^{v*}) < k`, the directional derivative of the concave `Psi` at `p*` in the
direction `1_{S0}`, `S0 = Av(M^{v*})`, is

```
|S0| - r_{M^{v*}}(E_{S0})  =  k - nu(M^{v*})  >  0
```

(2c, Proposition 2.1, Step 2, and Lemma `lem:avoidable`(2)), so `Psi(p* + h 1_{S0}) > Opt(w)`
for small `h > 0`, against Lemma `lem:duality`. So `nu(M^{v*}) = k`.

Step 4, item 3. Letting `j -> infinity` in (3.1) with `i` fixed:

```
0  <=  x_{i,b}  =  p*_b - p_{i,b}  <=  G_i - lim_j G_j  =  G_i ,
v_i  =  w - (p_i)_blk  =  (w - p*_blk) + (p* - p_i)_blk  =  v* + (x_i)_blk .
```

*Hypotheses used:* PO-SL ((F2), (F5)); 2c, Proposition 2.1; 2c, Theorem 5.1(3) (only
when `T_LS(w) = infinity`); Lemmas `lem:duality`, `lem:avoidable`(2).

**Lemma 3.2 (freezing).** For `j <= i` and `e, f in E`,

```
| (v_{i,e} - v_{i,f}) - (v*_e - v*_f) |  <=  G_i  <=  G_j .
```

So if `|v*_e - v*_f| > G_j`, then `v_{i,e} - v_{i,f}` has the sign of `v*_e - v*_f` for
every `i >= j`; with 2c, Theorem 5.1, this holds for every
`j > k(2k-1) ln(G_0 / |v*_e - v*_f|)`.

*Proof.* Step 1. By Lemma 3.1(3),
`(v_{i,e} - v_{i,f}) - (v*_e - v*_f) = x_{i,blk(e)} - x_{i,blk(f)}`, a difference of
two numbers in `[0, G_i]`. Step 2. `G` is nonincreasing (Lemma 3.1(1)). Step 3.
`G_j <= (1 - 1/(k(2k-1)))^j G_0 < G_0 e^{-j/(k(2k-1))}`.

*Hypotheses used:* Lemma 3.1; 2c, Theorem 5.1 (last sentence only).

**Lemma 3.3 (the block is Lipschitz).** For every `r` and states `v, v' in R^E`, the
stage-`r` PO-SL blocks satisfy

```
| a_b(v) - a_b(v') |  <=  2 m (m - 1) || v - v' ||_inf      (b in [k]).
```

In particular the LS map `v -> v - a(v)_blk` is continuous.

*Proof.* Step 1, one function of the relation. By Lemma `lem:observer` there are
functions `F_b` of relations `G subseteq E x E` with
`F_b(G_t(v)) = [nu(N_v(t)) <= r][b in Av(N_v(t))]` for all `v` and `t >= 0`, and
`F_b(E x E) = 0`. So `a_b(v) = int_0^inf F_b(G_t(v)) dt`, and the integrand vanishes
for `t >= max v - min v` (there `G_t(v) = E x E`).

Step 2, where the relations differ. Let `eps = ||v - v'||_inf`. For an ordered pair
`(e, f)`, `e != f`, put `d = v_f - v_e`, `d' = v'_f - v'_e`, so `|d - d'| <= 2 eps`. The pair
lies in exactly one of `G_t(v)`, `G_t(v')` only for `t` in `[min(d, d'), max(d, d'))`,
an interval of length at most `2 eps`; pairs `(e, e)` lie in both. So

```
| { t >= 0 : G_t(v) != G_t(v') } |  <=  m (m - 1) * 2 eps .
```

Step 3. With Step 1,

```
| a_b(v) - a_b(v') |  <=  int_0^inf | F_b(G_t(v)) - F_b(G_t(v')) | dt  <=  2 m (m - 1) eps .
```

*Hypotheses used:* Proposition `prop:posl` (the family is a function of `G_t`) and
Lemma `lem:observer`.

So the LS map is a continuous piecewise linear map of `R^E` that fixes the closed set
`{v : nu(M^v) = k}` pointwise; `T_LS` is the hitting time of that set.

**Formal statement (for Lean), Lemmas 3.1 and 3.2.** Data as in 2c's `LastStage.lean`:
`hE : M.E = univ`, `rank M = k`, `1 <= k`, `w`, the iteration `p : N -> (Fin k -> R)`
with `p 0 = 0`, `p (j+1) = p j + blockV M blk (k-1) (w - (p j)_blk)`. Conclusions:
(1) `0 <= blockV ... b <= G j - G (j+1)` with `G j = opt w - psi (p j)`;
(2) `Tendsto p atTop (nhds pstar)` and `psi pstar = opt w`;
(3) `forall j b, 0 <= pstar b - p j b <= G j`;
(4) `forall j <= i, forall e f, |((v i e - v i f) - (vstar e - vstar f))| <= G j`.
Ingredients present in `LastStage.lean`: `psi_add_le_psi_blockV` (Psi-ascent),
`opt_sub_psi_blockV_le` (Theorem 5.1), `continuous_psi`. New: the telescoping (3.1) and
the limit argument; item `nu(M^{v*}) = k` needs the directional-derivative step.

## 4. The local regime is a block-constant run

Fix `w`, and let `p*`, `v*`, `x_j`, `G_j` be as in Lemma 3.1. Put

```
gamma  =  min { |v*_e - v*_f| : e, f in one component of M, v*_e != v*_f }   (infinity if empty),
```

let `Lambda` be the partition of `E` into the classes `K cap {v* = l}` (`K` a component
of `M`, `l in R`), and `M' = M^{v*}`. For `x in R^k` let `N'_x(t) = M'^{u'_t}`, where
`u'_t` is built from the values `x_blk(e)` as in Definition `def:posl` with two changes:
the possibly optimal set is

```
PO'_t  =  { f : f notin cl_{M'} { g : x_blk(g) < x_blk(f) - t } } ,
```

and the clusters are formed by single linkage at scale `t` inside each class of
`Lambda` (in place of each component of `M`), `u'_t(e)` being the position of the
cluster of `e` in its class and `m + 1` off `PO'_t`. The **block-constant block** is

```
a'_b(x)  =  int_0^{tau'} [ b in Av(N'_x(t)) ] dt ,    tau'  =  min { t : nu(N'_x(t)) = k } .
```

**Proposition 4.1 (local regime).** Let `J` satisfy `2 G_J < gamma`. Then for every
`j >= J`:
1. `M^{v_j} = M'^{(x_j)_blk}`; in particular `nu(M^{v_j}) = nu(M'^{(x_j)_blk})`;
2. `N_{v_j}(t) = N'_{x_j}(t)` for `0 <= t <= G_j`;
3. `a(p_j) = a'(x_j)`, so `x_{j+1} = x_j - a'(x_j)`.

Hence `T_LS(w) = J + T'(x_J)`, where `T'(x)` is the number of steps of
`x -> x - a'(x)` from `x` until `nu(M'^{x_blk}) = k`. Such a `J` exists, and
`J <= 1 + floor(k(2k-1) ln(2 G_0 / gamma))` when `gamma < infinity` and `G_0 > 0`.

*Proof.* Fix `j >= J` and `0 <= t <= G_j`; write `x = x_j`, `v = v_j`; by Lemma 3.1,
`0 <= x_b <= G_j <= G_J < gamma / 2`.

Step 1, separation. For `e, f` in one component with `v*_e < v*_f`, Lemma 3.1(3) gives

```
v_f - v_e  =  (v*_f - v*_e) + x_blk(f) - x_blk(e)  >=  gamma - G_j  >  G_j  >=  t ,
```

so `v_e < v_f - t`; and for `v*_e = v*_f`, `v_f - v_e = x_blk(f) - x_blk(e)`.

Step 2, item 1. `M' = M^{v*}` is the direct sum, over the components `K` and the values
`l`, of `M_{K,l} = (M | K cap {v* <= l}) / (K cap {v* < l})` on `K cap {v* = l}` (the
description of `M^u` after Lemma `lem:minbases`, with Lemma `lem:minbases`(4)). By
Step 1 at `t = 0`, inside `K` the values of `v` are ordered first by `v*`, then by `x`.
Equation `eq:rank-mu` for `v` on `K` therefore has one term per pair `(l, c)`, `c` a
value of `x_blk` on `K cap {v* = l}`; with `W = (K cap {v* < l}) cup {e in K : v*_e = l, x_blk(e) < c}`
and `L = {e in K : v*_e = l, x_blk(e) = c}`, the term is

```
r(W cup (A cap L)) - r(W)  =  r_{M_{K,l}}(W' cup (A cap L)) - r_{M_{K,l}}(W') ,   W' = W - (K cap {v* < l}),
```

which is the term of `eq:rank-mu` for the weight `x_blk` on `M_{K,l}`. Summing,
`r_{M^v} = r_{M'^{x_blk}}`.

Step 3, the possibly optimal sets. Let `f in K`, `v*_f = l`. By Step 1,

```
{ g in K : v_g < v_f - t }  =  (K cap {v* < l})  cup  X ,   X = { g in K : v*_g = l, x_blk(g) < x_blk(f) - t } .
```

Closure in a contraction and in a direct sum, and Lemma `lem:minbases`(4), give

```
f in cl_M{ g : v_g < v_f - t }  <=>  f in cl_M((K cap {v* < l}) cup X)  <=>  f in cl_{M_{K,l}}(X)
                                <=>  f in cl_{M'}{ g : x_blk(g) < x_blk(f) - t } ,
```

so `PO_t(v) = PO'_t(x)`.

Step 4, the clusters. By Step 1, elements of `K` in different classes of `Lambda` are
more than `t` apart, every value of a lower class lies below every value of a higher
class, and inside a class the differences are those of `x_blk`. So the clusters of `K`
at scale `t` for `v` are the clusters of the classes `K cap {v* = l}` for `x`, ordered
by `l` and then by position.

Step 5, the lower classes are spanned. For `l in R`,
`K cap {v* < l} subseteq cl_M(PO_t(v) cap K cap {v* < l})`: by induction on `v_g`, an
element `g in K cap {v* < l}` outside `PO_t(v)` lies in `cl{h in K : v_h < v_g - t}`,
and by Step 1 these `h` have `v*_h <= v*_g < l` and `v_h < v_g`. In the same way each
`g in K cap {v* = l}` outside `PO'_t(x)` lies in `cl_{M_{K,l}}` of the elements of
`PO'_t(x) cap K cap {v* = l}` (induction on `x_blk(g)`).

Step 6, item 2. By Lemma `lem:minbases`(4) it suffices to compare the two rank
functions on each component `K` (on the right side, `M'^{u'_t}` is the direct sum of
the `(M_{K,l})^{u'_t}`, the summands being unions of components of `M'`). Order the
clusters of `K` as in Step 4, `C_1, C_2, ...` (the level sets of `u_t` on `K`), and let
`C_i` lie in the class of value `l`, `D_i` the union of the earlier clusters of that
class, `U_{i-1}` the union of all earlier clusters. By Step 5,
`cl(U_{i-1}) = cl((K cap {v* < l}) cup D_i)`, so the term of `eq:rank-mu` for `M|K`,
`u_t` and `C_i` is

```
r(U_{i-1} cup (A cap C_i)) - r(U_{i-1})  =  r_{M_{K,l}}(D_i cup (A cap C_i)) - r_{M_{K,l}}(D_i) ,
```

the term of `eq:rank-mu` for `u'_t` on `M_{K,l}` and `C_i`. The top levels contribute
`0` on both sides, as `PO_t(v) cap K` spans `K` and `PO'_t(x) cap K cap {v* = l}` spans
`K cap {v* = l}` in `M_{K,l}` (Step 5). Summing over `i`, `l` and `K`,
`r_{N_v(t)} = r_{N'_x(t)}`.

Step 7, item 3. By Lemma 3.1(1), `tau_j <= G_j - G_{j+1} <= G_j`. By item 2,
`nu(N'_x(t)) = nu(N_v(t)) <= k - 1` for `t < tau_j` and `nu(N'_x(tau_j)) = k`, so
`tau' = tau_j`, and

```
a'_b(x)  =  int_0^{tau_j} [b in Av(N'_x(t))] dt  =  int_0^{tau_j} [b in Av(N_v(t))] dt  =  a_b(p_j) .
```

Step 8, the count. By items 1 and 3 the two iterations agree from step `J` on and stop
together. `G_j < G_0 e^{-j/(k(2k-1))}` (2c, Theorem 5.1) gives `2 G_j < gamma` for
`j > k(2k-1) ln(2 G_0 / gamma)`.

*Hypotheses used:* Lemma 3.1; Proposition `prop:posl` and Definition `def:posl`;
Lemma `lem:minbases` (items 2 and 4) and `eq:rank-mu`; 2c, Theorem 5.1 (bound on `J`
only). Nothing about `k` or about monotonicity of `nu0`.

*Checked* (`lsu_local.py 4 150`, log `lsu_logs/local_1.txt`; random graphic, binary,
uniform, paving and sum instances, `k <= 6`, `m <= 10`; 160,908 runs, 427,677
states): Lemma 3.1 (items 1 and 3) at every state, Lemma 3.2 for every pair and every
later state, and Proposition 4.1 (block and `nu`) at all 22,913 states with
`2 G_j < gamma`: no failure. Discrimination: Lemma 3.2 with threshold `G_j / 4` fails
404,874 times; the comparison of item 3 at the 243,856 states with `2 G_j >= gamma`
fails 39,095 times; with the linkage classes replaced by the components of `M'` (the
standard PO-SL of `M'`) item 3 fails once (graphic, edges
`13,23,52,15,40,50,20,40,35,02`, blocks `[1,3,1,0,4,4,3,1,2,0]`,
`w = [0,14114,0,12952,5038,2,16,1,16,8867]`, step 1: true block `[14,0,14,14,2]`,
standard PO-SL of `M'` `[16,0,16,16,2]`), so the classes `K cap {v* = l}` are needed.
Item 2 directly (`lsu_local2.py 4 120`, log `lsu_logs/local2_1.txt`, 76,186 runs): at all
32,201 pairs (local state, level `t <= G_j`) the two matroids have the same `nu`, the same
`Av` and the same rank on 16 random subsets; the same comparison at the 1,122,868 pairs
of non-local states fails 722,928 times.

**Corollary 4.2 (where a non-terminating run must live).** For every `w`,
`T_LS(w) = infinity` if and only if the block-constant iteration of Proposition 4.1
from `x_J` does not terminate. Consequently, if for every `u in R^E` with
`nu(M^u) = k` (with `M' = M^u`, `Lambda = {K cap {u = l}}`) and every `x in R^k` the
block-constant iteration terminates after at most `B` steps, then for every real `w`

```
T_LS(w)  <=  1 + floor( k(2k-1) ln(2 G_0 / gamma) ) + B  <  infinity .
```

*Proof.* Proposition 4.1 with `J = 1 + floor(k(2k-1) ln(2 G_0/gamma))` (or `J = 0` if
`gamma = infinity` or `G_0 = 0`), and `M^{v*}` is of the stated form by Lemma 3.1(2).

So a Euclid-type infinite run (2c, Section 6) is a block-constant run: a run of a
homogeneous continuous piecewise linear map on `x in R^k_{>=0}` (Lemma 3.3 applied to
`M'`). The bound of Corollary 4.2 is not uniform in `w`, through `G_0 / gamma`.

**Formal statement (for Lean), Proposition 4.1 item 2.** Data: `M`, `vstar`,
`x : Fin k -> R`, reals `G` and `t` with `forall b, 0 <= x b <= G`, `2 * G < gamma`
(`gamma` the least nonzero difference of `vstar` inside a component) and
`0 <= t <= G`; `v = vstar + x_blk`. Conclusion:
`N_posl M v t = N_posl' (M^vstar) Lambda (x_blk) t` as matroids (equal rank functions),
where `N_posl'` is `N_posl` with the components replaced by a partition coarser than
the components of `M^vstar`. Lemmas: `eq:rank-mu` (`POSLRank.lean`), closure in
contractions and direct sums.

## 5. A lower bound: T_LS can exceed m + 2

**Proposition 5.1.** At a state `v` with `nu(M^v) = k - 1`, `T_LS(v)` (the LS run
started at `w = v`) equals the number of regular stage-`(k-1)` updates from `v`. So
`sup_w T_LS(w)` is at least the longest regular last stage, and there is an instance
with `k = 7`, `m = 14` and `T_LS(w) = 20 = m + 6`.

*Proof.* Step 1. As in Theorem 2.1, Step 2: at `nu0 = k - 1` the LS integrand is the
stage-`(k-1)` integrand, and `nu0` does not decrease (Theorem `thm:validity`(2)).
Step 2. 2d, Section 6: the graphic instance with edges
`75,24,64,36,53,14,64,46,65,13,21,47,70,04`, blocks `[6,5,0,3,1,4,1,4,1,4,2,1,6,3]` and
weights `[430261,4251475,2240075,19124,153712,3840,2342092,1171454,102834,307393,16777218,46321,200643,256338]`
has regular stage lengths `[0,0,0,0,1,20]`. Its state at the entry of stage 6 is

```
w' = [430261,4251475,307393,19124,153712,3840,2342092,1171454,102834,307393,14844536,46321,200643,256338],
```

with `nu(M^{w'}) = 6 = k - 1`, and the LS run from `w'` takes 20 blocks and ends at
`Psi = Opt` (`lsu_lower.py`, log `lsu_logs/lower_1.txt`; the referee implementation
`referee_phase2a/core.py`, `posl_update`, also takes 20 updates and reaches the same
final state).

So the observation `T_LS <= m + 2` of 2c (searches with `k <= 6`) is not a bound for
larger `k`, and every uniform bound on `T_LS` is also a bound on the regular last
stage, whose order is open: at most `(m - 1) + (k - 3) min(km, floor(m^2/4) + 1)`
(2d, Section 6), at most about `(k - 2) m` under 2d's Conjecture P, and at least
`m + 6` at `k = 7`.

*Hypotheses used:* Theorem `thm:validity`(2); the instance (exact arithmetic, two
implementations).

## 6. Block-constant runs: data and a conjecture

By Corollary 4.2, every question about termination for real `w` is a question about
block-constant runs of the local form (`M' = M^u`, linkage classes `K cap {u = l}`).

**Conjecture 6.1 (BC).** For every `u in R^E` with `nu(M^u) = k`, with `M' = M^u` and
`Lambda = {K cap {u = l}}`, and every `x in R^k`, the block-constant iteration of
Section 4 reaches `nu(M'^{x_blk}) = k` after at most `min(k, #{x_b : b in [k]})` steps.

Under Conjecture 6.1, Corollary 4.2 gives `T_LS(w) <= 1 + floor(k(2k-1) ln(2 G_0/gamma)) + k`
for every real `w`: the LS iteration terminates for irrational `w` (2c, Section 9,
open), and no Euclid-type infinite run exists.

*Evidence.*

| script, log | instances | runs | failures of the bound | false variant fails |
|---|---|---|---|---|
| `lsu_bc_local.py 4 120`, `lsu_logs/bc_local_1.txt` | local form: `M' = M^u`, `u` random with ties, `Lambda = K cap {u = l}`; `k <= 7`, `m <= 12` | 171,721 | `T' > k`: 0; `T' > #values`: 0 (max `T'` = 5) | `T' <= k - 2`: 2,395; `T' <= #values - 2`: 14,457 |
| `lsu_blockconst.py 4 60` (console) | `M' = M`, standard PO-SL, `x` of 2 to 20 bits | 191,186 | `T > k`: 0 (`T` up to `k` at `k = 4, 5, 6`) | |
| `lsu_bc_ties.py 4 40` (console) | as above | 106,083 | `T > #values`: 0 | ties persist: 7,184 failures; classes merge at every non-final step: 1,207 failures |

*What a proof must handle* (`lsu_bc_ties.py`, probe `lsu_tmp_vals.py`,
`lsu_tmp_bcconst.py`): the block-constant map creates new values (in 7,097 of 47,233
steps some new `x_b` is not an old value; example below), ties `x_b = x_c` can break
(7,184 of 169,245 steps), and the number of distinct values can stay the same at a
non-final step, also when the final state is constant (12 of 15,160 steps), so the
number of value classes is not a potential. Example (paving, `k = 5`): `x = [742018,
594325, 411106, 178801, 74346]` goes to `[509713, 509713, 362020, 178801, 74346]`;
block 2 joins the raised set at `t = 183219 = x_1 - x_2`, a level of the starting state,
while blocks 0 and 1 are already lower. Example with a constant final state (binary,
`k = 6`): `[96950, 0, 106890, 210208, 110165, 19609]` (offsets above the final value),
then `[32824, 0, 106890, 106890, 32824, 19609]`, `[13215, 0, 32824, 32824, 13215, 19609]`,
`[0, 0, 19609, 19609, 0, 19609]`, `0`: 4 steps for 5 distinct nonzero values; the
groups move down like a conveyor and merge.

Also on block-constant weights (probe `lsu_tmp_bcep.py`, 48,848 instances): every
regular stage `r` took at most `r` updates (70,248 stages), while 307 epochs took two
updates.

## 7. Refuted statements and observations

### 7.1 Candidate potentials (all refuted)

`lsu_observe.py 4 180` (log `lsu_logs/observe_1.txt`): 231,746 LS runs (`k = 3..7`,
`m <= 12`; graphic, binary, uniform, paving, sums; small, spread, exponential and
ladder weights), 390,391 steps, 4,133,738 pairs `(e, f)` in one component, different
blocks, `v*_e != v*_f`.

| statement | failures | instance |
|---|---|---|
| P1: `p_j <= p0`, the least element of `P* cap {p >= 0}` (no overshoot; `P*` is the set of dual optima, a lattice given by difference constraints) | 2,500 runs | graphic on 6 vertices, edges `41,24,13,53,13,10,43,02,42,51,35`, blocks `[4,1,1,3,1,2,0,2,2,1,3]`, `w = [3,3,4,1,3,5,0,3,0,2,1]`: `p_1 = [2,2,0,2,3]`, `p0 = [1,3,0,2,4]`, `p_T = [2,3,0,2,4]` (probe `lsu_tmp_ov2.py`) |
| P2: the order of the remaining offsets `x_j = p* - p_j` is preserved | 10,077 steps | graphic, edges `24,51,13,45,25,03,42,02,21`, blocks `[4,3,2,0,0,3,0,1,0]`, `w = [3699,0,3488,0,0,0,12331,3989,4]`: `x_0 = [0,3989,3488,0,3699]`, `x_1 = [0,505,505,0,0]` (block 4 passes blocks 1 and 2) |
| P3: a pair once in its final strict order stays so | 5,146 pairs (some only through a tie) | the instance of P5: the pair is in its final order at states 0, 2, 3 and strictly reversed at state 1 |
| P4: every step but the last puts some such pair into its final order | 49,156 steps | graphic, edges `15,10,32,15,43,45,12,32`, blocks `[1,1,2,1,0,3,4,1]`, `w = [1,0,3,2,2,5,8,4]`, step 0 of 5 |
| P5: a pair reverses its strict order at most once | 2,092 pairs (up to 4 reversals) | graphic, edges `35,42,34,12,30,03,40,40,20,41,54,51`, blocks `[2,0,0,2,0,1,4,0,3,4,3,0]`, `w = [4194,7358,3348,6542,3996,9295,3982,6300,4454,3680,606,2679]`, pair `(0,9)`: `(4194,3680), (3348,3680), (2740,2438), (2106,1804)` |
| O2: some block is never raised along the run (`min_b p*_b = 0`) | 1 run | **Instance LSU-1** below |
| "the block of a least element of `v_j` gets `a = 0`" | 28,230 steps | |

**Instance LSU-1** (`lsu_o2_instance.py`, log `lsu_logs/o2_instance.txt`). Graphic on
8 vertices, the disjoint union of `12,32,13,31,31,12` (vertices 0 to 3) and
`46,67,56,47,54,76` (vertices 4 to 7); `k = 5`, `m = 12`; blocks
`[3,2,4,2,1,3,2,0,3,4,0,1]`, `w = [32,129,22,128,66,129,74,64,0,0,128,2]`. The LS run
takes 3 steps with `a = [87,25,97,0,25]`, `[41,41,0,0,0]`, `[2,2,2,2,0]` (`nu0`: `3, 4, 4, 5`,
a mismatch at the first step), so `p* = [130,68,99,2,25]` and every block is raised in
some step; `Psi = Opt`, and the referee implementation gives the same `nu0` at all four
states. Each single block vector still has a zero entry (O1 below).

### 7.2 Observations without failure

Same run (`lsu_observe.py`), with false variants:

| observation | failures | false variant | its failures |
|---|---|---|---|
| O1: every block vector has a zero entry (`a_{j,b} = 0` for some `b`) | 0 of 390,391 steps | the block of a least element of `v_j` has `a = 0` | 28,230 steps |
| O3: every block vector has an entry `a_{j,b} = tau_j` | 0 of 390,391 steps | one block has `a_{j,b} = tau_j` at every step of the run | 6,156 of 106,146 runs with `T >= 2` |

With few distinct values (`lsu_fewvalues.py 2 120`, log `lsu_logs/fewvalues_1.txt`,
131,397 runs, `V` the number of distinct values of `w`, `V <= 6`): `T_LS <= V + 2`
always, `T_LS <= V + 1` fails once (graphic on 7 vertices, edges
`36,03,60,52,43,64,42,43,10,10,20,12`, blocks `[0,3,4,5,0,1,1,2,5,5,2,2]`,
`w` with values `654984, 882058, 1025592`, `T_LS = 5`), and the false variant
`T_LS <= V` fails 65 times.

### 7.3 Searches for growth with the bit length (target 3)

Hill climbing (`lsu_search.py`: graphic, midpoint, doubling, block moves; every best
instance re-run with `Psi = Opt` checked). Objective `low` = number of LS steps at
states with `nu0 <= k - 2` (the steps not covered by a regular stage bound).

| `n`, `m`, `k` | bits | workers x s | best `low` (with `T_LS`) | log |
|---|---|---|---|---|
| 5, 9, 4 | 24 | 2 x 150 | 7 (`T = 7`), `nu0` `2^7, 4` | `search_low_g5_9_b24.txt` |
| 5, 9, 4 (objective: mismatch steps) | 24 | 2 x 150 | 6 mismatch steps (`T = 8`) | `search_mis_g5_9_b24.txt` |
| 5, 10, 4 | 10 | 1 x 600 | 8 (`T = 8`) | `search_low_g5_10_b10.txt` |
| 5, 10, 4 | 40 | 1 x 600 | 8 (`T = 10`) | `search_low_g5_10_b40.txt` |
| 6, 10, 5 | 10 | 1 x 600 | 8 (`T = 8`) | `search_low_g6_10_b10.txt` |
| 6, 10, 5 | 40 | 1 x 600 | 11 (`T = 11 = m + 1`, all at `nu0 = 3`, 10 mismatch steps) | `search_low_g6_10_b40.txt` |
| 6, 10, 5 | 64 | 2 x 600 | 9 (`T = 9`, all at `nu0 = 3`, 7 mismatch steps) | `search_low_g6_10_b64.txt` |
| 6, 12, 5 | 64 | 2 x 600 | 10 (`T = 10 = m - 2`; one run at `nu0 = 2` with 9 mismatch steps, one at `nu0 = 3` with none) | `search_low_g6_12_b64.txt` |

The 11-step run at `k = 5` (40 bits) is a ladder: block 3 has one element (edge `04`,
weight `2^40 - 1`), receives the full `tau` at every step and descends through the other
values, one or two per step; every step has a mismatch at the jump `3 -> 4`, and
`nu0` stays 3 until the last step. At `k = 4` the counts do not change from 10 to 40
bits; at `k = 5` the 10-bit search is limited by the bit length (a ladder needs about
one bit per step), and 64 bits give no more than 40 bits (9 against 11 at `m = 10`). No
growth with the bit length was found: the best counts stay at most `m + 1`.

## 8. Consequences for Theorem `thm:C`, and the precise gap

**Exact circuits for all real `w`.**
- `k = 3`: by Theorem 2.1, `m` copies of the last-stage block (Lemma `lem:oneupdate`
  with `r = 2`, which computes the block at every state, 2c, Section 7) followed by
  `Psi` compute `Opt(w)` exactly for every real `w`. This is the count of 2d's regular
  schedule for `k = 3` (`ell_1 + ell_2 = 1 + (m - 1)`), so the size order does not change.
- `k >= 4`: no uniform bound on `T_LS` is proved, so the LS circuit is not justified,
  and the exact count stays `R(k, m) = sum_{r<k} min(r(floor(m^2/4) + 1), 1 + (r-1)km)`
  (or 2d's `1 + (k-2)(m-1) + km(k-2)(k-3)/2`). Theorem `thm:C` stays
  `O(k^4 m^6 (s + m))`.
- Every uniform LS count `T(k, m)` is at least the longest regular last stage
  (Proposition 5.1), for example `T(7, 14) >= 20`. If `T_LS <= T(k, m)` were proved with
  `T = O(k m)` (the order of the last stage under 2d's Conjecture P), Theorem `thm:C`
  would become `O(k^2 m^6 (s + m))`; with `T = m + O(k)`, `O(k m^6 (s + m))`.

**What is proved about all real `w`, without a uniform count.** The LS run converges
to a dual optimum (Lemma 3.1), every pair with final gap above `G_j` is frozen
(Lemma 3.2), and from the first `J` with `2 G_J < gamma` on it is a block-constant run on
`M^{v*}` (Proposition 4.1). With Theorem 5.1 of 2c this gives
`T_LS(w) <= 1 + k(2k-1) ln(2 G_0/gamma) + T'(x_J)`.

**The precise gap.**
1. *Block-constant runs* (Conjecture 6.1): a bound `T' <= B(k)` for the iteration of
   Section 4 on `M' = M^u` with linkage classes `K cap {u = l}`. This alone gives
   termination for every real `w` (Corollary 4.2), but not a uniform count.
2. *Before the local regime*: a bound on `J(w)`, the number of steps with
   `2 G_j >= gamma`, uniform in `w`. The freezing lemma says that when `G_j` lies
   between two consecutive final gaps `d_i < d_{i+1}` (inside components), all pairs
   with final gap `>= d_{i+1}` are frozen and the dynamics at the scale `G_j` sees the
   final structure only up to the small gaps `<= d_i`. A uniform bound would follow
   from: (a) each such scale window costs at most `B'(k)` steps whatever
   `d_{i+1}/d_i` is (a block-constant problem perturbed by the small gaps, Lemma 3.3
   controls the perturbation), and (b) at most `m` windows. Neither (a) nor (b) is
   proved; the data fit `T_LS <= (number of final gaps) + O(1)` (Section 9 below).
3. *`k = 4`*: the LS steps at `nu0 = 2` (`nu0` is monotone, 2c, Corollary 4.4; steps at
   `nu0 = 1` take one step, steps at `nu0 = 3` are the regular stage 3, at most
   `1 + (m - 2) + min(4m, floor(m^2/4) + 1)` by 2d). The steps at `nu0 = 2` combine a
   regular stage-2 update with a continuation at `nu = 3` that can undo its crossings
   (Section 7.1, P3 to P5); the searches give at most `m - 2` of them (Section 7.3).

## 9. T_LS against the structure of the instance (data)

**Distinct values and final gaps** (`lsu_finalgaps.py 2 120`, log
`lsu_logs/finalgaps_1.txt`, 110,032 random runs, `k = 3..7`, `m <= 12`; `V` the number
of distinct values of `w`, `D*` the number of consecutive gaps of `v*` inside components):
`T_LS - V <= 2` and `T_LS - D* <= 4` on all runs; the candidate `T_LS <= D* + 2` fails 375
times (binary, columns `[26,11,63,13,47,3,59,31]`, blocks `[1,4,2,3,4,0,2,5]`,
`w = [9,0,0,6,9,4,3,8]`: `T_LS = 5`, `D* = 1`), and `T_LS <= D*` fails 6,963 times. With
the instance of Proposition 5.1 (`V = 13`, `T_LS = 20`) the additive term has to grow
with `k`. These data fit the picture of Section 8 (one or two steps per scale of the
instance, plus a block-constant tail), not a proof.

**Components of rank one** (the assignment problem in rainbow form, where PO-SL is the
exact family `P_t`, B0, Proposition 1.3 with `q = 1`). `lsu_rankone.py 4 240` (log
`lsu_logs/rankone_1.txt`; partition matroids of `k <= 7` columns with a planted perfect
matching and up to 4 extra edges per column; small, spread and exponential weights) and
a first version with rejection sampling: `T_LS <= k - 1` on all 6,333 runs, `Psi = Opt`
at the end, `nu0` never decreases (first version); `T_LS <= k - 2` fails 215 times and
`T_LS <= k - nu(M^w)` 422 times. Most runs take one step. The guess `T_LS <= k - 1` is
nevertheless **false**: on 44,839 further runs (probe `lsu_tmp_inv.py`) 5 runs have
`T_LS >= k`, for example

**Instance LSU-2** (`lsu_rankone_ce.py`, log `lsu_logs/rankone_ce.txt`). Partition
matroid with 4 columns (rank one each), `k = 4`, `m = 15`: columns
`[0,0,0,0,0,1,1,1,1,2,2,3,3,3,3]`, rows (blocks) `[3,3,2,1,0,0,0,3,0,2,3,1,0,0,3]`,
`w = [25966355,0,0,8388608,16384,1073741824,4194304,0,134217728,1048576,0,577198333,1041479850,342059139,1024]`.
`T_LS = 4 = k` (`nu0`: `2, 2, 3, 3, 4`; a mismatch at the first step), the regular
schedule also takes 4 updates (stages `[0, 2, 2]`); `Psi = Opt`, and the referee
implementation gives the same `nu0` at all five states.

The pairs `(Delta nu0, Delta |S0|)` over 11,142 non-final rank-one steps (probe
`lsu_tmp_delta.py`, 38,888 runs) include `(0, 0)` (19 steps) and `(1, -4)` (5 steps), so
neither `(nu0, |S0|)` lexicographically nor any `alpha nu0 + |S0|` is a potential, and
the invariant `|S0_j| >= j + 1` fails 368 times (probe `lsu_tmp_inv.py`). The rank-one
clause of Theorem `thm:C` (Corollary `cor:rankone`, `k(k-1)/2` updates) is therefore not
improved here.

## 10. Scripts and logs (all in `experiments/`, exact arithmetic)

| script | what it does | log |
|---|---|---|
| `lsu_core.py` | LS run recording `p_j`, `v_j`, `nu0`, `S0`; optimal rainbow base; difference constraints of `P*` and its least element `p0`; random instances | |
| `lsu_trace.py` | step-by-step trace: pieces, jumps of `nu(N)`, `nu(L)` at the jumps (mismatch), outcome | |
| `lsu_k3.py` | Theorem 2.1 with false variants | `lsu_logs/k3_1.txt` |
| `lsu_local.py` | Lemmas 3.1, 3.2, Proposition 4.1 (block-constant family `N'` with linkage classes), false variants | `lsu_logs/local_1.txt` |
| `lsu_bc_local.py` | Conjecture 6.1 on block-constant runs of the local form, false variants | `lsu_logs/bc_local_1.txt` |
| `lsu_blockconst.py`, `lsu_bc_ties.py` | block-constant runs with `M' = M`: `T` against `k` and the number of values; ties and class merges | (console, Section 6) |
| `lsu_lower.py` | Proposition 5.1 (`T_LS = m + 6` at `k = 7`), with the referee implementation | `lsu_logs/lower_1.txt` |
| `lsu_observe.py` | Section 7.1 and 7.2: P1 to P5, O1 to O3 and their false variants | `lsu_logs/observe_1.txt` |
| `lsu_o2_instance.py`, `lsu_o2_search.py` | Instance LSU-1 (trace, referee `nu0`), and a targeted search (170,223 runs, none found) | `lsu_logs/o2_instance.txt`, `lsu_logs/o2_search_1.txt` |
| `lsu_examples.py` | recomputes the graphic instances quoted in Section 7.1 | `lsu_logs/examples_1.txt` |
| `lsu_fewvalues.py` | `T_LS` against the number of distinct values of `w` | `lsu_logs/fewvalues_1.txt` |
| `lsu_search.py` | hill climbing for many steps below `k - 1` (or mismatches), by bit length | `lsu_logs/search_*.txt` |
| `lsu_overshoot.py` | first version of P1 (no overshoot of `p0`) | (console: 560 of 77,560 runs) |
| `lsu_tmp_*.py` | throwaway probes; their numbers are reproduced by the scripts above except where stated in Sections 6, 7 | |
