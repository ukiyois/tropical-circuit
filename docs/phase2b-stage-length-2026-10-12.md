# Phase 2b: stage length of the rainbow schedule (2026-10-12)

Problem B0 of the research direction: the length of a stage (updates at
`nu0 = r` until `nu0 >= r + 1`) for PO-SL and for other admissible families.
Setting: `paper/greedy_intersection.tex`, Sections 4.4 to 4.7;
`docs/phase2a-rainbow-2026-10-11.md`, Sections 2 to 4.

## Status log (for a relaunched agent)

- 2026-10-12, 12:20 to 15:00. Work finished; no searches left running.
  Implementation `experiments/stage_core.py`, cross-checked against the
  referee's `core.py`. Proved (with checks): Lemma 1.2, Proposition 1.3,
  Theorems 2.1, 2.2, 2.4, 2.5, 2.6, Corollaries 2.3, 2.9, 2.10, Lemma 2.8,
  Proposition 3.1, Proposition 4.1, Theorem 4.2. Refuted: Conjecture 2.7
  (epoch at most `|U| + rho`) and the guess "epoch at most
  `max(|U|, |R|) + 1`", with exact instances in Section 2.6. Open: the order
  of the PO-SL stage length (`r m` or `r k m`); an admissible family read from
  `G_t` with `O(r)` stages; Conjecture 4.3 (warm start, B1), the main open
  step for B1.
- The coordinator is formalizing Theorems 2.1 and 2.4 in Lean and putting the
  halving ladder (Theorem 2.5) into the paper; this note does not touch
  `paper/` or `daishu-formal/`.
- Logs in `experiments/stage_logs/`: `hill_*` (weights in [0,12]), `exp_*`
  (exponential weights, objective stage minus m), `epoch_*`, `epochmax_*`,
  `epochm_*` (objectives epoch minus `|U|`, minus `max(|U|,|R|)`, minus `m`),
  `verify_epoch_L3.txt`, `admissible_xlink_L4.txt`.
- Every script is listed in Section 5 with what it checks.

## 0. Summary of results

Notation: stage `r`, `R = E_{S0}` the raised elements, `U = E - R`,
`rho = |S0| - (k - r)`; an **epoch** is a run of updates with fixed `S0` (at most
`r` per stage); `B*` a minimum base meeting `r` blocks, fixed in the epoch;
`D = min { v_y - v_g : y in R - B*, g in C(B*, y) - R }`, the distance to the end
of the epoch.

**Proved (Sections 1 to 4).**
1. *Window lemma and scale sandwich* (Lemma 1.2, Proposition 1.3): a PO-SL
   cluster at scale `t` spans at most `(2q - 1) t`, `q <= k` the number of
   values of a minimum base in its component; hence
   `P_t subseteq Bases N(t) subseteq P_{(2q-1)t}`.
2. *One-update epochs* (Theorem 2.1, Corollary 2.10): an epoch with `rho = 0`
   takes exactly one PO-SL update, so **stage 1 always takes exactly one
   update**; when every component of `M` has rank one (assignment), every epoch
   takes one update and every stage at most `r`.
3. *Geometric decrease* (Theorem 2.2): `D` is positive inside an epoch, zero
   right after it, and each update gives `D' <= D - delta <= (1 - 1/(2q-1)) D`.
   With integral weights of range `W`, an epoch has at most
   `1 + (2k-1) ln(kW)` updates and a stage at most
   `1 + (r-1)(1 + (2k-1) ln(kW))` (Corollary 2.3).
4. *Anchor crossings* (Theorem 2.4): every update makes a raised element pass
   an unraised one, one of the two in `B*`; an epoch has at most
   `sum_K (rho_K |U cap K| + (k_K - rho_K) |R cap K|) <= k m` updates and
   **stage `r` at most `1 + (r - 1) k m`**, against `r (floor(m^2/4) + 1)` in
   Theorem `thm:potential`. For Theorem `thm:C` the schedule shrinks from
   `k^2 m^2 / 4` to `k^3 m / 2` updates and the size bound from
   `O(k^3 m^7 (s + m))` to `O(k^4 m^6 (s + m))`; for Theorem `thm:D`
   (`k = m/2`) nothing changes.
5. *Halving ladder* (Theorem 2.5): at `k = 3` there are instances on `m`
   elements whose stage 2 takes exactly `m - 3` PO-SL updates (weights with
   `m - 4` bits), while the exact family `P_t` takes one. **So the PO-SL stage
   length is not bounded by any function of `r` or `k`.**
6. *Koenig property* (Theorem 2.6): every base with more than `rho` raised
   elements has `theta >= D`. So the exact family `P_t` first sees a change
   exactly at the end of the epoch, and any admissible family whose first
   event is never before `D` takes at most `r` updates per stage. The only loss
   of PO-SL is the factor `2q - 1` of item 1.
7. *Order-preserving families* (Proposition 3.1): every family `M^{u_t}` with
   `u_t` read from `G_t` and order-preserving takes two updates on a ladder
   epoch where `P_t` takes one (`G_t`-twins force a merge).
8. *Capacities* (Proposition 4.1, Theorem 4.2): for the capacitated
   transportation problem in rainbow form, the PO-SL potentials stay symmetric
   on the slots of a source and every stage takes at most
   `p (floor(m0^2/4) + 1)` updates (`p` sources, `m0` edges), independent of the
   capacities.

**Refuted, with exact instances.** `r + 1` updates per stage (known; now:
linear growth in `m` at `r = 2`, Theorem 2.5); "an epoch takes at most `|U|`
updates" (eleven searched epochs take `|U| + 1`); Conjecture 2.7, "at most
`|U| + rho`" (an epoch of 6 updates with `|U| = 2`, `rho = 2`: an unraised
anchor passed by the raised elements one per update); "at most
`max(|U|, |R|) + 1`" (an epoch of 7 with `|U| = |R| = 5`, `m = 10`); any bound
`m + c` on the stage length (stages of `m + 4` at `k = 5` and `m + 5` at
`k = 6`); admissibility of the forced-linkage families `xlink`, `xlink2`, `xh`
((F2) fails on MK4, W3, K4minus+par, C4+chord par at `v in {0..4}^E`). All in
Sections 2.6 and 3.

**Answer to Question 1, as far as it goes.** The PO-SL stage length is not
bounded by a function of `r` (or `k`) alone; it is at most `1 + (r - 1) k m`
(Theorem 2.4) and at least `m - 3` on explicit instances with `r = 2`
(Theorem 2.5). The longest stages found by search are `m - 1`, `m`, `m + 4`,
`m + 5` at `k = 3, 4, 5, 6`, with several long epochs in one stage, and both
kinds of pairs counted in Theorem 2.4 are used one per update. Every epoch
found has at most `m - 2` updates (observation, Section 2.6), which would give
`O(r m)`; whether the order is `r m` or `r k m` is open. With integral weights
the stage length is `O(r k log(kW))` (Corollary 2.3), and the ladder shows the
logarithm is needed.

**Conjectured, with evidence.** Conjecture 4.3 (warm start for capacity
scaling, B1): the restart deficit is at most `p + q + 2 m0`; observed at most
6.

**Question 2.** Polynomial refinements of PO-SL that are admissible on the zoo
exist (`clsl`, `clheight`, circuit-certified linkage) and shorten stages by up
to a factor 2, but they stay linear on ladders. Families that link only what
`P_t` forces reach the exact family's stage lengths but violate (F2) and are
computed by base enumeration. No admissible family read from `G_t` with stages
of `O(r)` updates was found; Theorem 2.6 locates the obstruction in the matroid
requirement and in monotonicity, not in `P_t`.

**B1.** The pseudo-polynomial factor is the number of stages (rank values `F`),
not their length (item 8), and the dynamics is short (at most 6 updates in
total with `F` up to 676). A capacity-scaling schedule that keeps the
potentials between halvings of the capacities runs only `O(m0 + p + q)` stages
per phase; it returned `Opt` on all 504 test instances (`F` up to 2,658) and
gives `poly(m0, log U)` updates if Conjecture 4.3 holds.

## 1. Notation and the window lemma

Throughout, `M` has rank `k` on `E`, `|E| = m`, blocks `R_1..R_k`; a state is
`v = w - p_blk`; `M^v` is the matroid of minimum bases; `nu0`, `S0` as in the
paper. Fix a stage `r` and a state with `nu0 = r`. Write

- `S = S0`, `R = E_S` (raised elements), `U = E - R`;
- `rho = |S| - (k - r)`; by Lemma `lem:avoidable`(2), `rho = r_{M^v}(R)`;
- `delta` the first event of Step 3 of Theorem `thm:potential`: the least `t`
  with `Av(N(t)) != S` or `nu(N(t)) > r`; every block outside `S` has
  `lambda_b >= delta`, so it moves down by at most `tau - delta`, while every
  block of `S` moves down by exactly `tau`.

An **epoch** is a maximal run of consecutive updates of the stage that start
from states with the same `S0`. By Theorem `thm:potential`(1), `S0` only grows
within a stage, and `k - r <= |S0| <= k - 1`, so a stage has at most `r` epochs,
indexed by `rho = 0, 1, ..., r - 1`.

For `x in E` and a minimum base `B` of `v`, the **anchors** of the component `K`
of `x` are the elements of `B cap K`; `q_K` is the number of distinct values
`v_b`, `b in B cap K` (the multiset of values of a minimum base is the same for
all minimum bases, so `q_K` does not depend on `B`), and `q = max_K q_K <= k`.

**Lemma 1.1 (windows).** Let `B` be a minimum base of `v`, `t >= 0` and
`f in PO_t`. If `f notin B`, some `b in C(B, f) - f` satisfies
`v_f - t <= v_b <= v_f`. In every case some anchor `b` of the component of `f`
has `v_b in [v_f - t, v_f]`.

*Proof.* Step 1. If `f in B`, take `b = f`.
Step 2. Let `f notin B`. By Lemma `lem:minbases`(1), every `b in C(B, f)` has
`v_b <= v_f`. If every `b in C(B, f) - f` had `v_b < v_f - t`, then
`f in cl{g : v_g < v_f - t}`, against `f in PO_t`. So some `b in C(B,f) - f`
has `v_b >= v_f - t`.
Step 3. `b` and `f` lie on the circuit `C(B, f)`, hence in one component.

**Lemma 1.2 (cluster range).** Every PO-SL cluster of a component `K` at scale
`t` has range (largest minus least value) at most `(2 q_K - 1) t`.

*Proof.* Step 1. For a cluster element `x` let `alpha(x)` be the largest anchor
value of `K` that is at most `v_x`. By Lemma 1.1, `v_x - alpha(x) <= t`.
Step 2. List the cluster elements by value, `x_1, ..., x_p`; `alpha` is
non-decreasing along the list, and consecutive values differ by at most `t`
(Definition `def:posl`). If `alpha(x_{j+1}) > alpha(x_j)`, then
`alpha(x_{j+1}) <= v_{x_{j+1}} <= v_{x_j} + t <= alpha(x_j) + 2t`.
Step 3. So the distinct values `a_1 < ... < a_s` of `alpha` on the cluster,
`s <= q_K`, have consecutive differences at most `2t`, and the range is at most
`(a_s + t) - a_1 <= 2t (s - 1) + t <= (2 q_K - 1) t`.

**Proposition 1.3 (scale sandwich).** For PO-SL,
`P_t subseteq Bases N(t) subseteq P_{(2q-1) t}` for every `t >= 0`.

*Proof.* Step 1. The first inclusion is (F3).
Step 2. Let `B'` be a base of `N(t)`, `e notin B'` and `f in C(B', e)`, both in
a component `K`. If `e in PO_t`, then `u_t(f) <= u_t(e)` (Lemma
`lem:minbases`(1) for `u_t`); either the clusters are equal and
`v_f - v_e <= (2 q_K - 1) t` by Lemma 1.2, or the cluster of `f` lies below that
of `e` and `v_f < v_e`.
Step 3. If `e notin PO_t`, Step 3 of the proof of Proposition `prop:posl`
gives `x* in PO_t cap K` with `v_{x*} < v_e - t` and `C(B', e)` inside
`{h : u_t(h) <= u_t(x*)}`; so `f` lies in the cluster of `x*` or below it, and
`v_f <= v_{x*} + (2 q_K - 1) t < v_e + (2 q_K - 2) t`.
Step 4. Hence `theta(B') <= (2q - 1) t`.

Checked: `experiments/stage_verify_lemmas.py` (Lemma 1.2 at every cluster and
Proposition 1.3 at every base of every `N(t)`, all block assignments and
`v in {0,1,2}^E`): U24 1,379 clusters / 4,746 bases, MK4 213,750 / 1,713,240,
no failure.

So single linkage approximates the exact family within a factor `2q - 1` of
the scale, and the factor is attained: the clusters of Section 2.6 have range
`(2q-1) t`. This factor is the source of every long stage below.

## 2. PO-SL: stage length

### 2.1 Epochs with rho = 0 take one update

**Theorem 2.1.** Let `v` be a state of stage `r` with `rho = 0`, that is
`|S0| = k - r`. Then one PO-SL update ends the epoch: at `v' = v - a_blk`,
`nu0 > r` or `S0` grows. In particular **stage 1 always takes exactly one
update**, and the first epoch of every stage that starts with `|S0| = k - r`
takes one update.

*Proof.* Step 1. By Step 4 of Theorem `thm:potential`,
`r_{N(delta)}(R) > rho = 0`, so some `y in R` is a non-loop of `N(delta)`.
Bases of `N(delta)` lie in `PO_delta` (Step 3 of Proposition `prop:posl`), so
`y in PO_delta`: `y notin cl{g : v_g < v_y - delta}`.
Step 2. Suppose no element of `R` lies in a minimum base of `v'`. Then every
`x in R` lies in `cl{g : v'_g < v'_x}`: otherwise the greedy algorithm that
takes the elements of `{v' < v'_x}` first and then `x` returns a minimum base
containing `x`.
Step 3. By induction on `v'_x`, every `x in R` lies in
`cl{g in U : v'_g < v'_x}`: the elements of `R` in `{v' < v'_x}` are spanned by
elements of `U` below them.
Step 4. For `g in U`, `v'_g >= v_g - (tau - delta)`; for `x in R`,
`v'_x = v_x - tau`. So `v'_g < v'_x` implies `v_g < v_x - delta`, and Step 3
gives `y in cl{g : v_g < v_y - delta}`, against Step 1.
Step 5. So `r_{M^{v'}}(R) >= 1 > rho`. If `nu0(v') = r` and `S0(v') = S`, Lemma
`lem:avoidable`(2) would give `r_{M^{v'}}(R) = rho`. Hence the epoch ends.
Stage 1 has `|S0| = k - 1 = k - r`.

Checked: stage 1 took one update on 331 random instances (graphic, binary,
uniform, `m <= 12`), and on all states with `nu0 = 1` of U24 and MK4 (`L = 2`).

### 2.2 Geometric decrease inside an epoch

Fix an epoch and a base `B*` of `M^v` meeting `r` blocks at its first state.
By Theorem `thm:validity`(2) and induction, `B*` is a minimum base meeting `r`
blocks at every state of the epoch, so it can be fixed. Put

```
D(v) = min { v_y - v_g : y in R - B*, g in C(B*, y) - R }.
```

The set is nonempty: otherwise `B* cap R` spans `R` in `M`, so
`r_M(R) <= rho < |S|`, and `M` has no rainbow base.

**Theorem 2.2.** Inside an epoch:
1. `D(v) > 0` at every state of the epoch, and `D(v') = 0` at the state that
   follows its last update;
2. `D(v') <= D(v) - delta` and `D(v') >= D(v) - tau`;
3. `delta >= D(v) / (2q - 1)`, so `D(v') <= (1 - 1/(2q-1)) D(v)`.

*Proof.* Step 1, item 1. For a minimum base `B*` with `|B* cap R| = rho`:
`r_{M^v}(R) > rho` iff `D(v) = 0`. If `D(v) = 0`, `B* - g + y` is a minimum base
(Lemma `lem:minbases`(3)) with `rho + 1` elements in `R`. Conversely, if
`r_{M^v}(R) > rho`, then `B* cap R` does not span `R` in `M^v`, so some
`y in R - B*` has an `M^v`-circuit in `B* + y` meeting `B* - R`, and by Lemma
`lem:minbases`(3) that circuit is `{y} cup {f in C(B*,y) : v_f = v_y}`; so
`D(v) = 0`. At a state of the epoch, Lemma `lem:avoidable`(2) gives
`r_{M^v}(R) = rho`. At the next state `v'`: if `nu0(v') > r`, Lemma
`lem:avoidable`(1) gives `r_{M^{v'}}(R) > rho`; if `nu0(v') = r` and
`S0(v') != S`, then `S0(v') supsetneq S` (Theorem `thm:potential`(1)), and by
Lemma `lem:avoidable`(3) `S` does not attain the maximum `k - r`, so again
`r_{M^{v'}}(R) > rho`.
Step 2, item 2. Let `(y, g)` attain `D(v)`. `y` moves down by `tau`, `g` by
`a_{blk g} <= tau - delta`; the pair is still an exchange pair of `B*`. So
`D(v') <= D(v) - delta`. For every pair, `v'_y - v'_g >= v_y - v_g - tau`.
Step 3, item 3. Steps 4 and 5 of Theorem `thm:potential`, with `B = B*` (it
attains `|B cap R| = r_{M^v}(R)`), give `y in R - B*` and `g in B* - R` with
`g in C(B*, y)` in one cluster at scale `delta`. By Lemma 1.2,
`D(v) <= v_y - v_g <= (2q - 1) delta`.

**Corollary 2.3 (integer weights).** If `w` is integral, every epoch has at
most `1 + (2q - 1) ln D_0` updates, where `D_0 <= (Opt(w) - beta(w)) / (k - r)
<= k (max w - min w) / (k - r)` is `D` at its first state. Stage `r` has at
most `1 + (r - 1)(1 + (2k - 1) ln(k W))` updates, `W = max w - min w`.

*Proof.* Step 1. Levels are differences of values, so with integral `w` every
`tau`, `lambda_b`, `a_b` and every later `v` is integral; inside the epoch
`D >= 1`.
Step 2. After `j` updates `D <= D_0 (1 - 1/(2q-1))^j`, so the epoch has at most
`1 + ln D_0 / ln((2q-1)/(2q-2)) <= 1 + (2q-1) ln D_0` states.
Step 3. By item 2, `sum tau >= D_0` over the epoch, and each update gains
`(k - r) tau` (Theorem `thm:validity`); the total gain of the schedule is at
most `Opt(w) - Psi(0) = Opt(w) - beta(w) <= k W`.
Step 4. The epoch with `rho = 0` takes one update (Theorem 2.1).

**Corollary 2.10 (rank-one components).** If every connected component of
`M` has rank at most one (a partition matroid with unit capacities; the
assignment problem in Lagrangian form), every PO-SL epoch takes exactly one
update and every stage at most `r` updates.

*Proof.* A component of rank one contains one element of a minimum base, so
`q = 1` and Theorem 2.2(3) gives `delta >= D`; item 2 gives `D' <= 0`, so the
epoch ends after one update; a stage has at most `r` epochs.

Checked: 300 random assignment instances (`n <= 5`, weights of 3 to 20 bits),
305 stages: every epoch one update, every stage at most `r`, `Psi = Opt`.
This is the companion paper's regime; the general loss comes only from
components whose minimum bases take several values.

### 2.3 Anchor crossings: a combinatorial bound

**Theorem 2.4.** Every update of an epoch makes some pair `(x, z)`,
`x in R`, `z in U`, in one component, with `x in B*` or `z in B*`, pass from
`v_x > v_z` to `v'_x <= v'_z`. Consequently an epoch has at most

```
sum_K ( rho_K |U cap K| + (k_K - rho_K) |R cap K| )  <=  k m
```

updates (`k_K = |B* cap K|`, `rho_K = |B* cap R cap K|`), and stage `r` has at
most `1 + (r - 1) k m` updates. This improves the bound `r (floor(m^2/4) + 1)`
of Theorem `thm:potential` whenever `k < m/4`.

*Proof.* Step 1, the cluster. Steps 4 and 5 of Theorem `thm:potential` give
`g in B* cap U`, `y in R - B*`, `g in C(B*, y)`, in one cluster `C` at scale
`delta`, `v_g < v_y`. Let `z2` be an element of `R cap C` with `v_{z2} > v_g`
and `v_{z2}` least (`y` qualifies), and `z1` an element of `U cap C` with the
largest value below `v_{z2}` (`g` qualifies). No element of `C` has a value
strictly between `v_{z1}` and `v_{z2}` (it would contradict the choice of `z1`
or of `z2`), so `v_{z2} - v_{z1} <= delta`.
Step 2, motion. An element of `R` moves down by `tau`, an element of `U` by at
most `tau - delta`. So a pair `x in R`, `z in U` with
`0 < v_x - v_z <= delta` ends with `v'_x <= v'_z`; and `v_x - v_z` strictly
decreases at every update of the epoch, so each pair passes at most once.
Step 3, `z2 in B*`: the pair `(z2, z1)` qualifies.
Step 4, `z2 notin B*`. Since `z2 in PO_delta`, Lemma 1.1 gives
`b in C(B*, z2) - z2` with `v_{z2} - delta <= v_b <= v_{z2}`; `b in PO_0
subseteq PO_delta` lies in the component of `z2` within `delta` of it, so
`b in C`.
- `b in U`, `v_b < v_{z2}`: the pair `(z2, b)` qualifies.
- `b in U`, `v_b = v_{z2}`: then `B* - b + z2` is a minimum base with
  `rho + 1` elements of `R`, against `D(v) > 0`. Impossible.
- `b in R`, `v_b = v_{z2}`: the pair `(b, z1)` qualifies.
- `b in R`, `v_b < v_{z2}`: by the choice of `z2`, `v_b <= v_g`, so
  `0 < v_{z2} - v_g <= delta` and the pair `(z2, g)` qualifies.
Step 5, counting. The qualifying pairs lie in one component, and their number
is at most the bound displayed. The epoch with `rho = 0` takes one update
(Theorem 2.1), and the stage has at most `r - 1` further epochs.

Checked: `experiments/stage_epoch_check.py` on 412 updates of random stages
and on the 81 updates of the long stages (ladders `L <= 8`, the two paper
examples, two referee instances with stages of 8): items of Theorem 2.2 and
the anchor crossing of Theorem 2.4 at every update, no failure.
Exhaustively, `experiments/stage_verify_epoch.py 3` (log
`stage_logs/verify_epoch_L3.txt`): the 13 matroids U24, U25, U35, U36, MK4, W3,
P6dbl, K4minus+par, C4+chord par, sumU12U23, sumU12U12, gf3_U24,
U23+loop+coloop of the referee zoo, every block assignment, every
`v in {0..3}^E` with `min v = 0` and `nu0 < k` (1,052,214 states; per matroid
the referee's counts), and every base `B*` of `M^v` meeting `r` blocks
(1,509,003 choices):
all items of Theorems 2.1, 2.2 and 2.4 hold. The harness is discriminating:
the false bound `delta >= D` fails on 1,188 of the MK4 states.

### 2.4 The halving ladder: stages of length m - 3 at r = 2

**Theorem 2.5.** For `L >= 0` let `A = 2^L` and take the multigraph on
vertices `{0,1,2,3}` with blocks `0,1,2` and

| element | edge | block | weight |
|---|---|---|---|
| `g'` | 30 | 1 | 0 |
| `g` | 20 | 1 | 0 |
| `h` | 10 | 0 | `A` |
| `h'` | 10 | 2 | `A` |
| `y` | 21 | 0 | `A + 1` |
| `b_i`, `i = 1..L` | 20 | 1 | `A / 2^i` |

(`m = L + 5`, `k = 3`). The PO-SL schedule has stage 2 of exactly `L + 2 = m - 3`
updates; the exact family `P_t` takes one update. So **the PO-SL stage length is
not bounded by any function of `r` or of `k`.**

*Proof.* Step 1, the start. `g'` is a coloop (the only edge at vertex 3), so
block 1 is never avoidable. The minimum trees are `{g', g, h}` and
`{g', g, h'}`; `nu0 = 2`, `S0 = {0, 2}`, `R = {h, h', y}`. The only rainbow tree
is `{g', y, h'}`.
Step 2, state `j` (`0 <= j <= L - 1`): `h, h'` at `A_j = 2^{L-j} >= 2`, `y` at
`A_j + 1`, the rest at the input values. `PO_t` contains `g', g, h, h'`, the
bridges of value at most `t` (a bridge is parallel to `g`), and `y` iff
`t >= 1`. For `t < A_j / 2` the largest bridge in `PO_t` is below `A_j / 2`, so
the gap to `h` exceeds `t`: the clusters of the triangle are
`{g, bridges <= t}` and `{h, h', y}`, every base of `N(t)` is `g'`, one edge 20
and one of `h, h', y`, `nu = 2` and `Av = {0, 2}`. At `t = A_j / 2` the bridge
`b_{j+1}` links `g` to `h`, one cluster contains `y` and `h'`, and
`{g', y, h'}` is a base of `N(t)`: `tau = A_j / 2`, `lambda = (0, inf, 0)`,
`a = (A_j/2, 0, A_j/2)`. The new state is state `j + 1`.
Step 3, state `L` (`h, h'` at 1, `y` at 2): `PO_0 = {g', g, h, h'}`; at `t = 1`,
`b_L` (value 1) and `y` enter `PO_1` and the triangle is one cluster:
`tau = 1`. State `L + 1` has `h, h'` at 0 and `y` at 1, still `nu0 = 2` and
`S0 = {0, 2}`; at `t = 1`, `y` joins the cluster of `g, h, h'`: `tau = 1`, after
which `{g', y, h'}` is a minimum tree and `nu0 = 3`.
Step 4. The stage takes `L + 2` updates. For `P_t`: `theta({g', y, h'}) =
v_y - v_g = A + 1` is the least `theta` of a rainbow tree, and one update of
size `A + 1` makes it minimum.

Verified exactly for `L = 0..12` (`experiments/stage_ladder.py`): stage
lengths `[0, L + 2]`, `Psi = Opt` at the end, `P_t` stage length 1; and with
the referee's independent implementation (`referee_phase2a/core.py`,
`posl_update`) for `L = 0..6`: stage 2 takes `L + 2` updates, `Psi = Opt`.

The weights have `L + 1` bits, so the ladder matches Corollary 2.3 up to the
constant: `log2 W + 2` updates. With weights in `[0, 12]` hill climbing found at
most 7 updates at `k = 3` and 10 at `k = 4` (`m <= 13`), against the paper's
`r (floor(m^2/4) + 1)`.

### 2.5 The exact family sees the end of an epoch exactly

**Theorem 2.6 (Koenig property at the raised set).** At a state of stage `r`
with `S = S0`, `R = E_S`, `rho = |S| - (k - r)`, and `B*` a minimum base meeting
`r` blocks: every base `B` of `M` with `|B cap R| > rho` has `theta(B) >= D`.
Consequently, for every `t < D`, every base in `P_t` has at most `rho`
elements in `R` and meets at most `r` blocks: `tau_P >= D`, where `tau_P` is the
`tau` of the exact family.

*Proof.* Step 1, the minor. Put `J = B cap B*`, `P = B* - B`, `Q = B - B*`;
`|Q| = |P|` and `|Q cap R| > |P cap R|`, since `|B* cap R| = rho`.
Step 2, the digraph. On the vertex set `(P cap U) cup (Q cap R)` draw an arc
`p -> q` when `B - q + p` is a base (that is `q in C(B, p)`) and an arc
`q -> p` when `B* - p + q` is a base (`p in C(B*, q)`).
Step 3, a directed cycle exists. Suppose not, and list the vertices so that
every arc points to an earlier vertex. Let `Z = J cup (Q cap U) cup (P cap R)`.
By induction along the list every vertex lies in `cl(Z)`: a vertex `p in P cap U`
lies in the closure of `C(B, p) - p subseteq J cup Q`, whose elements of
`Q cap R` are its out-neighbours, listed earlier; a vertex `q in Q cap R` lies
in the closure of `C(B*, q) - q subseteq J cup P`, whose elements of `P cap U`
are its out-neighbours. Then `B* = J cup (P cap U) cup (P cap R)` lies in
`cl(Z)`, so `r(Z) = k`, while `|Z| = |J| + |Q cap U| + |P cap R| <
|J| + |Q| = k`. A contradiction.
Step 4, summing. Take a cycle `p_1 -> q_1 -> p_2 -> ... -> q_l -> p_1`. Each
`(p_i, q_i)` is an exchange pair of `B` (`p_i notin B`, `q_i in C(B, p_i)`), so
`v_{q_i} - v_{p_i} <= theta(B)`. Each `(q_i, p_{i+1})` is an exchange pair of
`B*` with `q_i in R - B*` and `p_{i+1} in U`, so `v_{q_i} - v_{p_{i+1}} >= D`.
The two sums over `i` are equal, so `l theta(B) >= l D`.
Step 5, blocks. A rainbow independent set of size `r + 1` has at most
`k - |S|` elements outside `R`, so at least `rho + 1` in `R`.

The single symmetric exchange does not suffice: for `M(K_4)` with
`P = {12, 23, 34}`, `Q = {13, 14, 24}` and `R = {23, 13, 24}` no pair
`p in P cap U`, `q in Q cap R` is a symmetric exchange, and the cycle
`12 -> 24 -> 34 -> 13 -> 12` of Step 3 is needed.

Checked (`experiments/stage_konig.py`): the cycle lemma of Step 3 for all pairs
of bases (up to 400 sampled pairs) and all colourings of the symmetric
difference with `|Q cap R| > |P cap R|` on MK4, U24, U36, U37, F7, F7*, K5-e,
W4 (18,692 cases, no failure; the symmetric-exchange version fails in 181 of
them); the theorem on 93,764 bases at 2,115 random states. Also
`stage_forced.py` (1,052,214 zoo states) and `stage_forced_random.py` (26,120
random states, `m <= 10`): `tau_P >= D` and the least `theta` of a base with
more than `rho` raised elements is at least `D`, everywhere.

**What Theorem 2.6 says about families.** Put together with Theorem 2.2:
for an admissible family whose first event is at `delta >= D` at every state,
item 2 of Theorem 2.2 gives `D(v') <= 0`, so **every update ends an epoch and
every stage takes at most `r` updates** (one per epoch). Theorem 2.6 says the
exact family `P_t` has this property, which explains the observed `<= r + 1`
for `P_t` (phase 2a). PO-SL has its first event at `delta >= D / (2q - 1)`
(Theorem 2.2(3)); the factor `2q - 1` of the cluster range (Lemma 1.2) is the
whole loss. Any lower bound for all admissible families therefore has to come
from the matroid requirement (`P_t` is not a matroid) together with the
requirement of being read from `G_t`, not from `P_t` itself.

**Corollary 2.9 (one state never obstructs).** At a state of stage `r` and for
`t < D`, the truncation `T = T_k(U_{rho, R} (+) F_U)` (independent sets: at most
`k` elements, at most `rho` of them in `R`) is a matroid with
`P_t subseteq Bases T`, `nu(T) = r` and `Av(T) = S0` when every block outside
`S0` is nonempty.

*Proof.* Step 1. A base of `P_t` has `k` elements and, by Theorem 2.6, at most
`rho` in `R`, so it is a base of `T`.
Step 2. A rainbow independent set of `T` has at most `rho` elements in the
blocks of `S0` and at most one in each of the other `k - |S0|` blocks, so
`nu(T) <= rho + k - |S0| = r`; a base of `M^v` meeting `r` blocks attains it,
and a largest one must meet every block outside `S0`, so `Av(T) = S0`.

So the ideal hull exists state by state; what no family read from `G_t` can do
in general is choose it, since `R = E_{S0}` and `D` are not functions of `G_t`
for `t > 0` (they depend on `G_0`, which a continuous update cannot read).

### 2.6 How long is an epoch? Data and two refuted conjectures

Hill climbing over graphic and binary instances with integer weights below
`2^20` to `2^22`, using midpoint and doubling moves (the moves that build
ladders), objective "longest stage minus `m`" (`experiments/stage_search_exp.py`,
logs `stage_logs/exp_*.txt`, 28 to 30 workers, 500 to 600 s each):

| matroids | k | m | longest stage found | longest minus m |
|---|---|---|---|---|
| graphic, 4 vertices | 3 | 8 | 7 | -1 |
| graphic, 4 vertices | 3 | 11 | 10 | -1 |
| binary, rank 3 | 3 | 9 | 8 | -1 |
| graphic, 5 vertices | 4 | 9 | 9 | 0 |
| graphic, 5 vertices | 4 | 12 | 12 | 0 |
| binary, rank 4 | 4 | 11 | 11 | 0 |
| graphic, 6 vertices | 5 | 10 | 13 | +3 |
| graphic, 6 vertices | 5 | 13 | 17 (epochs 1, 11, 1, 4) | +4 |
| graphic, 7 vertices | 6 | 12 | 17 | +5 |

With weights in `[0, 12]` the same searches stop at 7 (`k = 3`) and 10
(`k = 4`), as Corollary 2.3 predicts. The `k = 5` instance (edges
`24,51,52,35,01,32,02,30,54,05`, blocks `[4,2,2,1,1,0,0,0,3,2]`, weights
`[2912652,46033,8,83449,35368,28514,9178,18843,366376,208616]`) has stage 4 of
13 updates in epochs of 1, 8, 1 and 3 updates, so several epochs of one stage
can be long. Traces (`experiments/stage_trace.py`) show the mechanism of
Theorem 2.5 in every long epoch: the raised anchor passes the unraised
elements one per update.

**Epochs against `|U|`** (`experiments/stage_epoch_U.py`,
`stage_epoch_U_random.py`): every state of the zoo with `nu0 < k`, `v in
{0..3}^E`, taken as the start of an epoch (1,052,214 epochs): no epoch longer
than `|U|`, and `|U|` is attained (epochs of 3 updates with `|U| = 3` on MK4, W3,
K4minus+par, C4+chord par). 949 epochs of random instances: none longer than
`|U|`. The 176 epochs of the 67 searched long instances: 11 take `|U| + 1`
updates, none more; for example the graphic instance with edges
`31,02,13,23,21,02,30,31`, blocks `[0,2,0,0,0,1,2,0]`, weights
`[15297,55943,29735,4085,5372,202496,58208,7390]`, whose second epoch
(`S0 = {1,2}`, `U = {0,2,3,4,7}`) takes 6 updates: the raised anchor passes the
five unraised elements in five updates, and a raised non-anchor then passes an
unraised anchor.

**Conjecture 2.7 (refuted).** "An epoch takes at most `|U| + rho` updates."
It holds on all the data above, but the targeted search
`experiments/stage_search_epoch.py graphic 5 10` (objective: epoch length minus
`|U|`) found a counterexample: the graphic instance on 5 vertices with edges
`20,34,23,10,14,02,32,20,20,04`, blocks `[1,0,3,0,2,3,2,1,2,3]`, weights
`[36271,3354,34766,7768,72064,32455,22426,34002,17040,35133]` (`k = 4`). Its
stage 3 has 7 updates; the second epoch (`S0 = {1,2,3}`, `rho = 2`,
`U = {1, 3}`, both unraised anchors) takes 6. The trace: the raised anchor 7
passes 3 and then 1; then the raised elements 0, 5, 2 and 9 pass the unraised
anchor 1, one per update. So the pairs (raised element, unraised anchor) of
Theorem 2.4 are used one at a time, and an epoch can be as long as about `|R|`
with `|U|` tiny. The same search on binary matroids of rank 4 (`m = 10`) found
epochs of 5 updates with `|U| = 2`, `rho = 2` (log `stage_logs/epoch_*.txt`).

The next guess, "an epoch takes at most `max(|U|, |R|) + 1` updates", which
covers both mechanisms and holds on the 247 epochs of the 87 instances found
before, also fails: the search with that objective
(`stage_search_epoch.py graphic 5 10 480 28 maxUR`, log
`stage_logs/epochmax_graphic_5_10.txt`) found an epoch of 7 updates with
`|U| = |R| = 5` (`m = 10`, `k = 4`, `rho = 2`): edges `13,31,20,20,03,13,42,21,42,04`,
blocks `[0,1,2,2,1,1,2,3,2,2]`, weights
`[335362,233742,26,3789,313619,273680,811,1048576,83842,120224]`. At `k = 5`
(`m = 11`) the same objective reached epochs of 8 updates with `|U| = 6`,
`|R| = 5` (log `stage_logs/epochmax_graphic_6_11.txt`).

**Epoch against `m`.** A last targeted search with objective "epoch length
minus `m`" (`stage_search_epoch.py graphic 5 9 420 28 m` and
`graphic 6 10 420 28 m`, logs `stage_logs/epochm_*.txt`) reached at most
`m - 2` (epochs of 7 updates at `k = 4`, `m = 9`) and `m - 2` again at `k = 5` (epochs of 8 updates at `m = 10`, with `|U| = 8`,
`rho = 1`).
Every epoch found in this work has at most `m - 2` updates, so "an epoch takes
at most `m` updates" (which would give stages of `O(r m)`) survives all
searches, but after two refuted guesses it is recorded here as an observation,
not as a conjecture.

**Lemma 2.8.** In the case analysis of the proof of Theorem 2.4, an update in
the case `z2 notin B*`, `b in U` (the pair `(z2, b)`), or in the case
`z2 notin B*`, `b in R`, `v_b < v_{z2}` with `g in C(B*, z2)`, is the last
update of its epoch.

*Proof.* In the first case `b in C(B*, z2)`, `z2 in R - B*`, `b in U`, so
`(z2, b)` is one of the pairs that define `D`, and `D <= v_{z2} - v_b <= delta`.
In the second case `(z2, g)` is such a pair and `D <= v_{z2} - v_g <= delta`.
Theorem 2.2(2) gives `D' <= 0`.

Instrumentation (`experiments/stage_epoch_cases.py`, the 196 epochs and 694
updates of the searched instances): a raised anchor passes the next unraised
element in 541 updates (538 in the case `z2 in B*`, 3 with a raised anchor at
the value of `z2`); the case of Lemma 2.8 with `b in U` occurs 125 times, always
as the last update; the remaining case (`z2` passes `g`, the anchor of `z2`
below `g`) occurs 28 times, once before the last update. The unraised element
passed by a raised anchor repeats inside an epoch in 3 of the 196 epochs, all
with `rho >= 2` (two raised anchors at different heights pass the same
unraised element), and those epochs still stay within `|U|`. The counterexample above is the
other side of Theorem 2.4: an unraised anchor passed by one raised element per
update. Both kinds of pairs counted there occur, so the bound `k m` per epoch
may be the right order. The longest stages found grow faster than `m` with `k`
(`m - 1`, `m`, `m + 4`, `m + 5` at `k = 3, 4, 5, 6`, Section 2.6 table): no
bound of the form `m + c` holds, and the truth lies between `m - 3` (Theorem
2.5, at `k = 3`) and `1 + (r - 1) k m` (Theorem 2.4).

## 3. Other families (Question 2)

All families below are computed from the relation `G = G_t` alone (and `M`),
through `stage_families.relation(v, t)`, so they are determined by `G_t` by
construction, and (F5) holds with the levels `{0} cup {|v_e - v_f|}`. Each is
`N(t) = M^{u_t}` with `u_t` a weak order on `PO_t` (other elements on top).
Notation: for `x in E` let `U(x) = {w : (x,w) notin G}` (the elements more than
`t` above `x`) and `D(x) = {w : (w,x) notin G}` (more than `t` below). Write
`x <_G z` when `U(x) supseteq U(z)` and `D(x) subseteq D(z)` with one inclusion
strict; then `v_x < v_z` in every realization of `G`. Call `x, z` **twins** of
`G` when `U(x) = U(z)` and `D(x) = D(z)`; then swapping their values gives
another realization of `G`, so their order is not determined by `G`.

| family | links | order of classes | polynomial |
|---|---|---|---|
| `posl` | `x, z` in `PO_t`, one component, `|v_x - v_z| <= t` | value | yes |
| `clsl` | as `posl`, and `x, z` in one component of `M | {g : v_g <= min(v_x, v_z) + t}` | height in certain comparisons | yes |
| `clheight` | none; arcs `f -> e` for `(e,f) in G` with `e, f` in one component of `M | {g : v_g <= v_e + t}`, and certain comparisons | height of strong components | yes |
| `xlink` | exchange pairs `(e, f)` of bases of `P(G)` unless `f <_G e`; twins | certain comparisons | no (base enumeration) |
| `xh` | none; arcs `f -> e` for every exchange pair of a base of `P(G)`, and `<_G` | height of strong components | no |

Admissibility (`experiments/stage_admissible.py L family`, every `v` in
`{0..L}^E` with `min v = 0`, every level), on U24, U25, U35, U36, MK4, W3,
P6dbl, K4minus+par, C4+chord par, sumU12U23, sumU12U12, gf3_U24,
U23+loop+coloop:

| family | L = 3 | L = 4 |
|---|---|---|
| `clsl`, `clheight` | (F1)-(F4) hold | (F1)-(F4) hold |
| `xlink`, `xlink2` | hold | **(F2) fails** on MK4 (36 transitions), W3 (27), K4minus+par (46), C4+chord par (32) |
| `xh` | hold | **(F2) fails** on K4minus+par (32), C4+chord par (16) |

(`xlink`, `clsl` and `clheight` also hold on F7 at `L = 2`.) On random larger matroids (graphic up to 6 vertices, binary rank 3 to 5, uniform, `m <= 9`, `v in {0..6}^E`; `experiments/stage_admissible_random.py`), `clsl`, `clheight` and `posl` pass (F1)-(F4) at all 19,296 levels of 3,180 states. A failure of `xh`, K4minus+par
(edges 01,02,03,12,13,13), `v = (3,1,4,3,2,0)`: at `t = 2` a certain comparison
closes a cycle with an upward exchange arc and `u_2` is constant, so `N(2) = M`
(13 bases); at `t = 3` that comparison is no longer certified and
`N(3) = P_3` (10 bases). Certified comparisons and twins are not monotone in
`t`, so merges driven by them are not monotone either.

Stage lengths (`experiments/stage_compare.py`; `scan=True`, no monotonicity
assumed; every run ends at `Psi = Opt`):

| instance | m | posl | clsl, clheight | xlink, xlink2 | xh | exact `P_t` |
|---|---|---|---|---|---|---|
| ladder `L = 0..6` | `L + 5` | `L + 2` | `L + 1` | 1, then 2 for `L >= 1` | 1 | 1 |
| paper, stage of 4 | 6 | 4 | 2 | 2 | 2 | 2 |
| paper, stage of 7 | 9 | 7 | 5 | 3 | 2 | 2 |
| k = 3, exponential weights | 8 | 7 | 5 | 3 | 1 | 1 |
| k = 4, exponential weights | 9 | 9 | 5 | 3 | 2 | 2 |
| k = 4, hill climbing | 10 | 10 | 7 | 4 | 3 | 3 |

Reading:
1. The polynomial refinements `clsl`, `clheight` are admissible on the zoo and
   shorten stages by up to a factor 2, but they still link the bridge `b` to
   the raised anchor `h` of the ladder through the circuit `{b, h, y}` as soon
   as `v_y <= v_b + t`, so they stay linear on ladders.
2. The brute-force families that link only what `P_t` forces reach the exact
   family's stage lengths (`xh`) or come within one update (`xlink`), which is
   consistent with Theorem 2.6, but they violate (F2).
3. Twins force an early event for order-preserving families
   (Proposition 3.1 below).

**Proposition 3.1 (order-preserving families).** Call a family
`N(t) = M^{u_t}` *order-preserving* if `u_t` is a function of `G_t` (and `M`),
`u_t(e) <= u_t(f)` whenever `v_e <= v_f` for `e, f in PO_t` in one component, and
`u_t` is on top outside `PO_t`. Every order-preserving family with
`P_t subseteq Bases N(t)` takes at least 2 updates in stage 2 of the halving
ladder of Theorem 2.5 for `L >= 1`, where the exact family takes 1. Neither (F1)
nor (F2) is used.

*Proof.* Step 1, twins. Take `t = A = 2^L >= 2`. In `G_A` the elements `b_1`
(value `A/2`) and `h` (value `A`) have the same sets
`{w : v_w > v_x + A} = {}` and `{w : v_w < v_x - A} = {}` (the largest value is
`A + 1 <= 3A/2`, the least is 0). So swapping the values of `b_1` and `h` gives
a realization `v'` of the same relation `G_A`, and `u_A` is the same at `v` and
`v'`.
Step 2, forced equalities. `B_1 = {g', b_1, y}` has `theta(B_1) = A/2`, so
`B_1 in P_A` (a function of `G_A`). At `v'`, `(h, b_1)` is an exchange pair of
`B_1` with `v'_{b_1} > v'_h`: (F3) gives `u(b_1) <= u(h)` and order preservation
gives `u(h) <= u(b_1)`. At `v`, `{g', b_i, h}` (`theta = v_{b_i}`) and
`{g', g, y}` (`theta = 1`) lie in `P_A` and give, in the same way, `u(g) = u(b_i)`
for every bridge and `u(h) = u(y)`; `u(h) = u(h')` by equal values.
Step 3. So `g, b_1, ..., b_L, h, h', y` share one class, `{g', y, h'}` is a base of
`N(A)`, `nu(N(A)) = 3` and `tau <= A`. The raised blocks move by `tau`, so the
pair `(y, g)` keeps `v'_y - v'_g >= D - tau >= 1` (Theorem 2.2(2)), and the epoch
(the whole stage) needs a second update.

`xlink` attains this bound (2 updates on every ladder, Section 3 table);
`xh`, which is not order-preserving, avoids the merge and takes 1 update, but it
violates (F2). Twins alone cannot do more: a class of `G_t`-twins has diameter
at most `t` (an element above both by more than `t` relative to one and not to
the other would distinguish them), so a long forced chain at a small scale has
to use exchange pairs of different bases of `P_t`. Whether such chains, which
are what any matroid closure of `P_t` must add, can force stages longer than
`r + 1` for every admissible family read from `G_t` is open.

## 4. Connection to B1 (capacities, transportation)

### 4.1 The rainbow form of the capacitated transportation problem

Sources `i` (supply `a_i`), sinks `j` (demand `b_j`), edges `e = (i,j)` (capacity
`c_e`, cost `w_e`), `sum a = sum b = F`, `m0` edges. Ground set: an element
`(e, s)` for every edge `e = (i,j)` and every **slot** `s = 1..a_i` of its source;
the block of `(e, s)` is the slot `(i, s)`, so `k = F`. `M` is the laminar
matroid `|X cap e| <= c_e`, `|X cap sink j| <= b_j`. Rainbow bases of `M` are the
integral feasible flows with labelled slots, and `Opt` is the minimum cost.
The instance is pseudo-polynomial in size (`m = sum_e a_{i(e)}`); the stages
are indexed by `r = 1..F - 1`.

**Proposition 4.1 (compression).** The slots of one source are
interchangeable, so along the PO-SL schedule from `p = 0` the potentials of the
slots of a source stay equal, and the update can be computed on edge types:
`e in PO_t` iff the edges into `j` cheaper than `v_e - t` offer fewer than `b_j`
units (`min(c_f, a_{i(f)})` each); clusters are single linkage at scale `t` on
the PO edges of each sink; `nu(N(t))` is the maximum flow
`S -> i (a_i) -> e (c_e) -> (j, cluster) (b_j - C_j(<cluster)) -> T`; source `i`
is avoidable iff it is reachable from `S` in the residual network of a maximum
flow; `a_i = (tau - lambda_i)_+`.

*Proof.* Step 1, symmetry. Permuting the slots of a source is an automorphism
of `M` and of the partition into blocks that fixes `w`; the update is a function
of the state that commutes with these automorphisms, so a symmetric state goes
to a symmetric state, and `S0` and every `Av(N(t))` are unions of whole
sources. With symmetric potentials all copies `(e, s)` of an edge have the value
`v_e = w_e - p_i`.
Step 2, closure. In the laminar matroid a copy of `e` lies in the closure of a
set `X` not containing copies of `e` iff `X` fills sink `j`, that is
`r(X cap sink j) = b_j`; the set `{g : v_g < v_e - t}` contains all or none of
the copies of each edge `f`, which contribute `min(c_f, a_{i(f)})` to the rank.
This is the stated test for `PO_t`.
Step 3, components and levels. If the edges into `j` offer more than `b_j`
units in total, any two copies of edges into `j` lie in a circuit of `b_j + 1`
copies within the edge capacities, so sink `j` is one component; otherwise the
sink constraint never binds and the copies of each edge form their own
components, and ordering different edges of `j` against each other does not
change `M^u`. Equation `(rank-mu)` gives, at sink `j`, the level pieces with
sink capacity `b_j - C_j(<l)` and the edge capacities.
Step 4, `nu` and `Av`. A rainbow independent set of `M^u` uses at most `a_i`
copies with distinct slots of source `i`, and conversely every integral flow
in the network of the statement is realized by such a set (assign distinct
slots); so `nu(M^u)` is the maximum flow. A slot of source `i` is avoidable iff
some maximum flow sends fewer than `a_i` units out of `i`. The set of nodes
reachable from `S` in the residual network is the same for every maximum flow
(the source side of the least minimum cut); if `i` is reachable along a path
starting with `S -> i'`, pushing one unit along it and removing one unit from
`S -> i` gives a maximum flow with `i` unsaturated, and conversely an
unsaturated `i` is reachable by the arc `S -> i`.
Checked: `experiments/stage_transport_fast.py` agrees with the uncompressed
run of `experiments/stage_transport.py` (stage length at every `r` and final
`Psi = Opt`) on 40 random instances.

**Theorem 4.2 (stage length does not depend on the capacities).** Every stage
of the PO-SL schedule on this instance takes at most `p (floor(m0^2 / 4) + 1)`
updates, `p` the number of sources.

*Proof.* Step 1. By Proposition 4.1, `S0` is a union of whole sources, so a
stage has at most `p` epochs.
Step 2. Elements of one edge have equal values and the same membership in
`E_{S0}`, so `Pi(v)` of Theorem `thm:potential` is a union of products
`(copies of e) x (copies of f)`; item 3 adds at least one new pair of edges
`(e, f)` with `e` from a raised source and `f` not, and there are at most
`floor(m0^2 / 4)` such pairs.

So the only pseudo-polynomial quantity left is the **number of stages**, `F - 1`.

### 4.2 Measurements

`experiments/stage_transport_growth.py 3 3 4`: random `3 x 3` instances with
supplies, demands and capacities up to `U`, 20-bit costs, 112 instances per `U`:

| U | F max | longest stage | active stages (max) | updates in total (max) |
|---|---|---|---|---|
| 1 | 3 | 2 | 2 | 2 |
| 8 | 23 | 2 | 5 | 5 |
| 64 | 184 | 2 | 5 | 6 |
| 256 | 676 | 2 | 6 | 6 |

Every run ends at `Psi = Opt` (min-cost flow by successive shortest paths).
Hill climbing for long stages (`experiments/stage_transport_search.py 3 3 16
400`, adversarial costs, capacities, supplies) found at most 4 updates in a
stage, against the bound 63 of Theorem 4.2. In the window picture (Lemma 1.2)
a sink `j` is one component whose minimum base takes at most `deg(j)` values,
so clusters chain across at most `deg(j)` windows; for the assignment problem
(`b_j = 1`) there is one window and no chaining, which is the companion paper's
case.
The dynamics is short; a static schedule is long only because it must allot
updates to all `F - 1` rank values, not knowing which are active.

### 4.3 A scaling schedule

Chain: `x_0` a feasible flow of `I_0 = I` (fixed data, computed by the
generator), `x_{f+1} = floor(x_f / 2)`, `I_{f+1}` = (row sums of `x_{f+1}`,
column sums of `x_{f+1}`, `ceil(c_f / 2)`); `I_{f+1}` is feasible and balanced,
and `I_f = 2 I_{f+1} + ` corrections of at most `deg` per node and 1 per edge.
Schedule: run the coarsest instance from `p = 0`; for `f = J-1, ..., 0` keep the
potentials and run only the stages `r >= F_f - X`.

**Conjecture 4.3 (warm start).** With `X = p + q + 2 m0`, the restart deficit
`F_f - nu0^{I_f}(p)` is at most `X` for every cost vector.

*Status (2026-10-12, `docs/phase3-b1-warmstart-2026-10-12.md`).* False for the
chain above (floor chain): `T(1, 7, 3)` has restart deficit `42 > 37`, and the
floor chain's worst case is `Theta(m0 q)` (Proposition 3.6, Corollary 3.5 there).
True, with room, for the balanced chain of that note, whose deficit is at most
`m0 + floor((p + q) / 2)` (Corollary 3.7 there).

Evidence (`experiments/stage_transport_warm.py`, `stage_transport_scaling.py`):
the deficit under doubling `I = 2 I' + bits` was at most 3 in 1,955 cases
(`m0 <= 16`); along the chain it was at most 6 in 504 instances (`3 x 3` with
`U = 4, 64, 1024`, `4 x 4` with `U = 256`, `F` up to 2,658, at most 11 phases);
the scaled schedule returned `Opt` every time with at most 10 updates.
Sketch: an optimal flow `y'` of `I_{f+1}` is a rainbow minimum base at the
potentials `p`; `2 y'` fits `I_f` after dropping at most one unit per edge
(capacity rounding) and, at each sink, the units displaced by extra cheap
capacity (at most one per edge and per extra slot); the uncovered slots add at
most `sum_i (a_i - 2 a'_i)`. This gives a polynomial bound
(`O(m0 q)` with the corrections above); the constant `p + q + 2 m0` is
observed, not proved.

**Consequence (conditional on Conjecture 4.3, or on its polynomial version).**
The schedule has `(ceil(log2 U) + 1) X` stages of `p (floor(m0^2/4) + 1)` updates,
`poly(m0, log U)` in total; each update is a threshold integral over pairs of
edge types whose observer is a maximum flow with fixed integer capacities
(`poly(m0, log U)` Boolean gates), and the output `sum a_i p_i + beta(w - p)` is
the greedy value of a polymatroid, a threshold integral of an integer rank
(Corollary `cor:integer`). So the minimum cost of a capacitated transportation
problem would have signed tropical circuits of size polynomial in `m0` and
`log U`.

**Where pseudo-polynomiality sits.** Not in the stage length (Theorem 4.2), and
not in the dynamics (Section 4.2): in the static index set of stages. Within
one epoch the geometric decrease of Theorem 2.2 is an automatic cost scaling
(at most `1 + (2k-1) ln(kW)` updates for integer costs), but it acts on the
costs, which are real inputs of the circuit; the capacities enter only through
the number of rank values, and the scaling chain is what reduces it.

## 5. Scripts (all in `experiments/`, exact integer arithmetic)

| script | what it does |
|---|---|
| `stage_core.py` | oracle-based matroids (bitmasks), `M^u`, `nu` and `Av` by augmenting paths, PO-SL, the update (binary search, or `scan=True`), stages, schedule; the exact family `P_t` by base enumeration |
| `stage_crosscheck.py` | agreement with the referee's `referee_phase2a/core.py` (195 states), the paper's stages of 4 and 7 |
| `stage_trace.py` | update-by-update trace of a stage: values, `S0`, `delta`, `tau`, `lambda`, clusters |
| `stage_ladder.py` | the halving ladder of Theorem 2.5, `L = 0..12`, PO-SL and `P_t` |
| `stage_verify_lemmas.py` | Lemma 1.2, Proposition 1.3, stage one (Theorem 2.1) exhaustively |
| `stage_verify_epoch.py` | Theorems 2.1, 2.2, 2.4 exhaustively on the zoo, every base `B*` (log `stage_logs/verify_epoch_L3.txt`) |
| `stage_epoch_check.py` | the same checks along random and long stages |
| `stage_konig.py`, `stage_forced.py`, `stage_forced_random.py` | Theorem 2.6: the cycle lemma, `tau_P >= D` and `t1 >= D` |
| `stage_epoch_U.py`, `stage_epoch_U_random.py` | epoch length against `|U|` (Section 2.6) |
| `stage_search.py`, `stage_search_exp.py`, `stage_search_epoch.py` | hill climbing for long stages (small and exponential weights) and against Conjecture 2.7 (logs `stage_logs/`) |
| `stage_epoch_cases.py` | the case of Theorem 2.4 used at every update (Lemma 2.8) |
| `stage_families.py`, `stage_admissible.py`, `stage_compare.py` | the families of Section 3, their admissibility, their stage lengths |
| `stage_transport.py`, `stage_transport_fast.py` | B1: transportation in rainbow form, uncompressed and type-compressed PO-SL |
| `stage_transport_growth.py`, `stage_transport_warm.py`, `stage_transport_scaling.py` | B1: growth with `U`, warm-start deficit, the scaling schedule |

## 6. Recommended next steps

1. **Order of the stage length.** Decide between `O(r m)` and `Theta(r k m)`.
   Both kinds of pairs of Theorem 2.4 are used one per update (the ladder: a
   raised anchor passing unraised elements; the counterexample to
   Conjecture 2.7: an unraised anchor passed by raised elements), but every
   epoch found has at most `m - 2` updates. Either prove "an epoch takes at
   most `m` updates" by a charging argument that gives each update its own
   element (Lemma 2.8 and `experiments/stage_epoch_cases.py` are the
   starting points), or combine the two mechanisms over `k` anchors into
   epochs of `Omega(k m)`.
2. **Lower bounds growing with `r`.** Find an explicit family with `r` long
   epochs in one stage (the `k = 5` search instance has epochs of 11 and 4,
   Section 2.6). Until then, use Theorem 2.4 (`1 + (r-1) k m` per stage) and
   Theorem 2.1 (one update for stage 1) in the paper.
3. **Paper text.** The paragraph "Stage length" of Section 7 can now say: the
   bound `r + 1` fails for PO-SL and no bound in `r` alone holds (ladder,
   Theorem 2.5); stages take at most `1 + (r-1) k m` updates (Theorem 2.4), and
   at most `1 + (r-1)(1 + (2k-1) ln(kW))` for integer weights of range `W`
   (Corollary 2.3); the exact family `P_t` is ideal (Theorem 2.6), and the
   factor `2q - 1` of single linkage is the whole loss (Proposition 1.3).
4. **Question 2.** Look for a monotone version of `xh`: a family read from
   `G_t` whose classes only merge as `t` grows, that links only exchange pairs
   of `P_t` (or a polynomial certificate for them), and that need not be
   order-preserving (Proposition 3.1 shows order preservation costs an extra
   update). Two concrete sub-questions: is deciding whether `(e, f)` is an
   exchange pair of some base of `P_t` NP-hard (the reduction of
   Proposition `prop:nphard` is a candidate)? Does the strongly connected
   closure of the exchange arcs of `P_t` ever create a base with more than
   `rho` raised elements before `D` (the data says no)?
5. **Lower bounds for all admissible families** must use chains of exchange
   pairs of different bases of `P_t` (twins have diameter at most `t`,
   Theorem 2.6 excludes `P_t` itself). Search small matroids for a state where
   every matroid containing `P_t` and read monotonically from `G_t` has
   `nu > r` before `D`.
6. **B1, the main open step: prove Conjecture 4.3** (a polynomial bound on the
   restart deficit suffices; the sketch gives `O(m0 q)`). With it, Theorem 4.2
   and the scaling chain give a static schedule of `poly(m0, log U)` updates for
   the capacitated transportation problem with a max-flow observer. Then
   extend the slot compression to weighted polymatroid intersection where one
   side is a generalized partition matroid.
