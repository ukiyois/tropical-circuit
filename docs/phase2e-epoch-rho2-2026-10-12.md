# Phase 2e: epochs with two or more raised values (2026-10-12)

Question: bound the number of PO-SL updates in one epoch with `rho >= 2`
(Conjectures P and Q of `docs/phase2d-epoch-2026-10-12.md`, called B0d below),
so as to shorten the schedule of Theorem C. Setting:
`paper/greedy_intersection.tex`, Section 4; notes B0
(`docs/phase2b-stage-length-2026-10-12.md`) and B0d. This note does not touch
`paper/`, `daishu-formal/` or the other notes.

## Status log (for a relaunched agent)

- 2026-10-12 21:00, coordinator. Stopped at the user's direction: open conjecture,
  no proof. Nothing from this note goes into the paper or Lean.
- 19:11 start. Read B0d completely, paper Section 4, B0 Sections 1 and 2,
  `ep_common.py`, `ep_cases2.py`, `ep_repeats.py`, `ep_conjQ.py`,
  `stage_core.py`. Scripts go to `experiments/ep2_*.py`, logs to
  `experiments/ep2_logs/`.
- 19:15 to 19:40. `ep2_trace.py` (R-frame trace with PO_delta, clusters, linking
  pairs). Found the *gap potential* `Phi` (Section 4): holds on all 473 logged
  epochs (`ep2_phi.py`), but REFUTED by hand-built instances with *low
  linking* (R6). Observed on all 397 logged updates with `rho >= 2`: the linking
  is at the top raised value (`ep2_linkpos.py`); false in general (R7).
- 19:40 to 20:05. Searches against `Phi` (`ep2_search.py`, logs
  `ep2_logs/search_phi_*.txt`): `Phi` fails, always at low-linking updates.
  Proved Lemmas E.1 to E.4 and Theorem E.5 (Conjecture P for components with at
  most two raised values, no raised element strictly between them and no
  linkable raised non-anchor at the lower value), Sections 1 and 2; checks
  `ep2_psi.py`, `ep2_repeat_anchor.py` (no failure, false variants fail).
- 20:05. `ep2_searchQ.py` (objective: Q slack) REFUTED Conjecture Q (R8, two
  instances, slack 1, P tight on both); independently recomputed with the
  referee code only (`ep2_refQ.py`). The P search (struct 7/14) stayed at
  `n - 1 - P1 = 0`. Running at 20:07: `ep2_minimize.py` on R8a (1 process),
  P searches binary 5/12 (2 workers) and cut 7/13 (1 worker), 1200 s, logs
  `ep2_logs/searchQ_P_*.txt`.
- 20:15. Note body written (Sections 0 to 8). `ep2_referee.py` now also checks
  R8a, R8b state by state (5 instances, no mismatch); both R8 instances are of
  type (b) of Theorem E.5 (`ep2_psi.comp_type`). New script `ep2_searchE5.py`
  (modes `E5`: test of Theorem E.5; `LOW`: P on epochs with low linking; `S3`:
  P on epochs with three raised values in a component), to be launched when
  the running searches end (about 20:27).
- 20:27. R8 minimized to `m = 9` (weights at most 8), recomputed with the
  referee code (`ep2_refQ.py`, `ep2_referee.py`). P searches binary 5/12 and
  glued 7/13 ended at `n - 1 - P1 = 0`. `ep2_phi_by_span.py`: `Phi` drops at
  all 1,250 updates with a linking pair reaching `T_K`, fails at 17 of 30 low
  ones. Running until about 20:43, one worker each: `ep2_searchE5.py LOW`
  (struct 7/14), `E5` (struct 7/14), `S3` (struct 8/15), `ep2_ft_search.py ft2`;
  logs `ep2_logs/searchE5_*.txt`, `ep2_logs/ft_search_ft2.txt`.
- 20:38. Lemmas E.1, E.2 checked (`ep2_lemmas12.py`, false variants fail).
  R9: a hand-built instance where `Phi` stays constant at a top-linking update
  (one gate, rigid motion), referee-checked; added to Sections 3 and 6.
- 20:42. Searches done: LOW (struct 7/14) best `n - 1 - P1 = -1`; E5 (struct
  7/14) no violation of Theorem E.5, longest epoch of its class `n = 11 = m - 3`;
  S3 (struct 8/15) best `n - 1 - P1 = 0`; ft2 design found no high update that
  empties `W_K`. Running until about 20:58: `LOW` graphic 6/12 (1 worker),
  `S3` graphic 7/14 (1 worker), P struct 8/16 (2 workers).
- How to resume: Sections 1 and 2 are complete proofs (Lemmas E.1 to E.4,
  Theorem E.5). Open: Conjecture P without the hypotheses of Theorem E.5
  (Section 6: low linking; raised elements strictly between two raised values,
  where the gap potential with a history clause per gap fails to be monotone
  in components other than the linking one).

## Summary of results

**Proved** (Sections 1 and 2; proofs use B0's Lemma 1.1 and Theorem 2.2(1),(2),
B0d's Lemmas A.2, B.1, B.2 and Theorem A', Steps 2, 3, 5 of the proof of Theorem
`thm:potential`, Lemmas `lem:avoidable`, `lem:minbases` and the cluster
structure of Definition `def:posl`).
1. Lemma E.1 (every `rho`): the first event `delta` of an update is the least
   scale at which some D-pair `(y, g)` has `y in PO_t` and `y`, `g` in one
   cluster; equivalently the least `t` with `r_{N(t)}(R) > rho`.
2. Lemma E.2 (conveyor, every `rho`): an unraised element lying inside the span
   of a cluster at scale `delta` reaches the next value of that cluster above
   it, so it crosses every raised element up to that value.
3. Lemma E.3 (repeat anchor, every `rho`): if `z` is designated at raised values
   `l_i < l_j`, then at the second designation the linking anchor `g` satisfies
   `l_i <= v_g <= v_z`, and `l_j` is the least raised-anchor value above `v_g`.
4. Lemma E.4 (scales after a linking, every `rho`): after a non-last update with
   linking pair `(y, g)` and raised anchor `h` of `C(B*, y)` within `delta` below
   `y`, the first events of all later non-last updates sum to less than
   `v_h - v_g`.
5. **Theorem E.5 (Conjecture P for a class of epochs).** If every component `K`
   with a raised anchor has either one raised-anchor value, or exactly two values
   `a_K < T_K` with no raised element of value strictly between them and no
   raised non-anchor of value `a_K` whose fundamental circuit meets `U`, then
   `n <= 1 + P1(v^0) <= m - rho`. The class contains `rho = 2` epochs with
   repeats: B0d's R4 instance and the counterexamples R8a, R8b to Q below
   satisfy the hypotheses, with `n = 1 + P1(v^0)`.

**Refuted** (Section 3).
- R8: **Conjecture Q of B0d** (repeats plus case (IV) updates at most the raised
  non-anchors below the top raised value): two instances found by search (slack
  1, Conjecture P tight on both), one minimized instance with `m = 9` and
  weights at most 8; all recomputed with the referee code only, all covered by
  Theorem E.5.
- R6: the gap potential `Phi` (Section 4), which held on all 473 logged epochs,
  fails at updates with low linking (hand-built instances; 17 of the 30
  low-linking updates in the data), and has not failed at any of the 1,250
  updates with a linking pair reaching the top raised value.
- R7: "the linking pair always uses the top raised value" (true on all 397
  logged updates with `rho >= 2`) fails.
- R9: "`Phi` drops at every update whose linking reaches the top value" (true
  on all 1,250 such updates in the data) fails on a hand-built `rho = 2`
  instance with one raised non-anchor strictly between the two raised values.

**Open** (Section 6): Conjecture P without the hypotheses of Theorem E.5; the
obstacles are low linking and raised elements strictly between two raised
values (in particular every component with three or more raised values).
Conjecture P survived all new searches (best `n - 1 - P1 = 0`).

**Consequences** (Section 7): unconditionally the stage lengths of B0d are
unchanged; Theorem E.5 gives `n <= m - rho` for the epochs it covers. Under
Conjecture P, or under the weaker `n <= 1 + P1 + c(k)` with `c(k) = O(m)`, the
schedule has about `k^2 m / 2` update blocks and Theorem C becomes
`O(k^3 m^6 (s + m))`.

## 0. Notation

As in B0d, Section 0: stage `r`, epoch with `S0 = S`, states `v^0, ..., v^n`
(update `i` maps `v^i` to `v^{i+1}`; update `n - 1` is the last), `R = E_S`,
`U = E - R`, `rho = |S| - (k - r)`, `B*` fixed, anchors, `K(e)`, the R-frame,
`delta <= tau`, and

    v'_x = v_x - tau   (x in R),        v'_z >= v_z - (tau - delta)   (z in U).

A *D-pair* is `(y, g)` with `y in R - B*`, `g in C(B*, y) - R`;
`D(v) = min (v_y - v_g)` over D-pairs. A *linking pair* of an update is a D-pair
with `y in PO_delta` and `y`, `g` in one cluster `C` at scale `delta` (it exists
by Step 5 of the proof of Theorem `thm:potential`); we fix one per update (the
one of `ep_cases2.classify`), call `g` the *linking anchor* and say the update
*links in* `K(y)`. For a component `K` with a raised anchor, `a_K <= T_K` are the
least and largest raised-anchor values (they do not depend on `B*`, B0d
Lemma P.0). An unraised `z` *crosses* a raised `x` (or the value `v_x`) at an
update if `v_z < v_x` and `v'_z >= v'_x`. The linking is *top* if some raised
anchor `h in C(B*, y)` with `v_y - delta <= v_h <= v_y` has `v_h = T_K`, and
*low* otherwise.

## 1. Structural lemmas (every rho)

**Lemma E.1 (first event = first linking).** At a state `v` of the epoch and
`t >= 0` the following are equivalent:
(i) `Av(N(t)) != S` or `nu(N(t)) > r`;
(ii) `r_{N(t)}(R) > rho`;
(iii) some D-pair `(y, g)` has `y in PO_t` and `u_t(g) = u_t(y)`.
Hence `delta = min { t : (iii) holds }`.

*Proof.* Step 1, (i) implies (ii). If `nu(N(t)) > r`, Lemma `lem:avoidable`(1)
gives

    |S| - r_{N(t)}(R) <= k - nu(N(t)) < k - r,   so   r_{N(t)}(R) > |S| - (k - r) = rho.

If `nu(N(t)) = r` and `Av(N(t)) != S`: for `b in S`, a base of `M^v` meeting
exactly `r` blocks and missing `b` is a base of `N(t)` by (F1), (F2), and since
`nu(N(t)) = r` it shows `b in Av(N(t))` (paragraph after Definition
`def:update`). So `S` is a proper subset of `Av(N(t))`, and by Lemma
`lem:avoidable`(3) the set `S` does not attain equality in Lemma
`lem:avoidable`(1):

    |S| - r_{N(t)}(R) < k - r.

Step 2, (ii) implies (i). If `nu(N(t)) = r` and `Av(N(t)) = S`, Lemma
`lem:avoidable`(2) gives `|S| - r_{N(t)}(R) = k - r`, that is `r_{N(t)}(R) = rho`.
Step 3, (ii) iff (iii). `B*` is a base of `N(t)` by (F1), (F2), and
`B* cap R` is independent with `rho` elements (B0d, Section 0), so
`r_{N(t)}(R) > rho` iff some `y in R - B*` has its circuit in `B* + y` (in
`N(t)`) meeting `B* - R`. `B*` is a minimum base of `u_t`, so by Lemma
`lem:minbases`(3) that circuit is `{y} cup {f in C(B*, y) : u_t(f) = u_t(y)}`;
elements of `B*`, which lies in `PO_0` and so in `PO_t`, have `u_t <= m`, so the
circuit meets `B* - R` iff `y in PO_t` and some `g in C(B*, y) - R` has
`u_t(g) = u_t(y)`.
Step 4. By (F5) the set of `t` with (i) is a union of intervals `[c_i, c_{i+1})`;
its least element is `delta` (Step 3 of the proof of Theorem `thm:potential`).

*Hypotheses used:* (F1), (F2), (F5) (Proposition `prop:posl`), Lemma
`lem:avoidable`(1)-(3), Lemma `lem:minbases`(3), `|B* cap R| = rho`.
*Checks* (`ep2_lemmas12.py`, logs of B0 and B0d): `delta` equals the least
level with (iii) at all 1,439 updates of the epochs with `rho >= 1`; the false
variant without the cluster condition in (iii) fails at 1,097 of them.

*Formal statement (for Lean).* Data: `M` of rank `k` on `Fin m`, `blk`, `r < k`,
`v` with `nu(M^v) = r`, `S = Av(M^v)`, `R = E_S`, `rho = |S| - (k - r)`, `B*` a
base of `M^v` meeting exactly `r` blocks, `N(t) = M^{u_t}` (PO-SL). Conclusion:
for all `t >= 0`,
`(Av(N t) != S or nu(N t) > r) <-> rank (N t) R > rho <->
exists y in R \ B*, exists g in C(B*, y) \ R, y in PO_t and u_t g = u_t y`.

**Lemma E.2 (conveyor).** At an update with first event `delta`, let `C` be a
cluster at scale `delta` of a component `K`, `z in U cap K` with
`min_C v <= v_z < max_C v`, and `c+ = min { v_c : c in C, v_c > v_z }`. Then
`z` crosses every raised `x` with `v_z < v_x <= c+`.

*Proof.* Step 1. Let `c- = max { v_c : c in C, v_c <= v_z }`. The values `c-` and
`c+` are consecutive values of `C`, so `c+ - c- <= delta` (Definition `def:posl`).
Step 2. By Steps 2 and 3 of the proof of Theorem `thm:potential`,

    v'_x - v'_z <= (v_x - tau) - (v_z - (tau - delta)) = (v_x - v_z) - delta
                <= (c+ - c-) - delta <= 0.

*Hypotheses used:* the cluster gaps of Definition `def:posl`; Steps 2, 3 of the
proof of Theorem `thm:potential`. *Checks* (`ep2_lemmas12.py`, same updates, all
clusters at scale `delta`): 3,183 pairs `(z, x)`, no failure; the false variant
"up to the second value of `C` above `v_z`" fails at 1,158 updates.

*Formal statement (for Lean).* Data: an update `v -> v'` of stage `r` with first
event `delta`, a cluster `C` of `K` at scale `delta`, `z in U cap K`, `x in R`.
Hypotheses: `min_C v <= v_z < v_x <= min { v_c : c in C, v_c > v_z }`.
Conclusion: `v'_x <= v'_z`.

**Lemma E.3 (repeat anchor).** Let `i < j` be updates of case (I) of Lemma B.1,
neither last, with the same designated element `z = z1`, passing raised anchors
`h_i`, `h_j` with `v_{h_i} < v_{h_j}`. Then at the state of update `j`, with
linking anchor `g`,

    v_{h_i} <= v_g <= v_z < v_{h_j},

and `v_{h_j}` is the least raised-anchor value of `K(z)` above `v_g`.

*Proof.* Step 1. At update `i` the element `z` crosses `h_i`; raised elements
stand still in the R-frame and `z` rises, so `v_z >= v_{h_i}` at every later
state.
Step 2. At update `j` let `C` be the cluster of the linking pair `(y, g)`. By
Lemma B.1 (Step 1 of its proof) `v_{z2} = v_{h_j} <= v_{h°} <= v_y`. The element
`g` is unraised, lies in `C` and below `z2`, and `z = z1` is the highest such
element, so `v_g <= v_z < v_{h_j}`.
Step 3. Suppose `v_g < v_{h_i}`. By Step 1, `v_{h_i}` lies in `(v_g, v_z]`, a
subset of `(v_g, v_y]`. The anchor `h_i` lies in `PO_delta`, and in `K(z)`
(at update `i`, `z` and `h_i` lie in one cluster), which is `K(g)` (at update
`j`, `z` and `g` lie in `C`). So `h_i in C` (an interval of the values of
`PO_delta cap K`).
Then the lowest raised element of `C` above `g` has value at most
`v_{h_i} <= v_z < v_{z2}`, against the choice of `z2`.
Step 4. A raised anchor of `K` with value in `(v_g, v_{h_j})` would lie in `C`
below `z2`.

So a repeated designation needs an unraised anchor that has passed the earlier
raised value and stays below the repeated element. *Hypotheses used:* Lemma
B.1, `B*` in `PO_0`, the interval property of clusters. *Checks*
(`ep2_repeat_anchor.py`, all logs of B0, B0d and this note): 74 pairs of
designations, no failure; the false variants "`v_z - v_g <= delta`" and
"`v_g >= v_{h_j} - delta`" fail on 15 and 45 of them.

*Formal statement (for Lean).* Data: the epoch, updates `i < j < n - 1` of case
(I) with designated element `z` and raised anchors `h_i`, `h_j`, linking anchor
`g` of update `j`. Hypothesis: `v^j_{h_i} < v^j_{h_j}`. Conclusion:
`v^j_{h_i} <= v^j_g <= v^j_z < v^j_{h_j}` and no `h in B* cap R cap K(z)` has
`v^j_g < v^j_h < v^j_{h_j}`.

**Lemma E.4 (scales after a linking).** Let `t < n - 1` be an update with
linking pair `(y, g)` and let `h in B* cap R cap C(B*, y)` with
`v_y - delta_t <= v_h <= v_y` (it exists by Lemma A.2). Then

    delta_{t+1} + delta_{t+2} + ... + delta_{n-2}  <  v^t_h - v^t_g.

*Proof.* Step 1. At every update `i`, `y` moves down by `tau_i` and `g` by at most
`tau_i - delta_i`, so

    v^{i+1}_y - v^{i+1}_g <= (v^i_y - v^i_g) - delta_i.

Step 2. At `i = t`, with `v^t_y - delta_t <= v^t_h`,

    v^{t+1}_y - v^{t+1}_g <= v^t_y - v^t_g - delta_t <= v^t_h - v^t_g.

Step 3. `(y, g)` is a D-pair and `v^{n-1}` is a state of the epoch, so
`D(v^{n-1}) > 0` (B0, Theorem 2.2(1)); by Steps 1 and 2,

    0 < v^{n-1}_y - v^{n-1}_g <= (v^{t+1}_y - v^{t+1}_g) - sum_{i=t+1}^{n-2} delta_i
      <= v^t_h - v^t_g - sum_{i=t+1}^{n-2} delta_i.

*Hypotheses used:* B0 Theorem 2.2(1); Steps 2, 3 of the proof of Theorem
`thm:potential`. *Checks* (`ep2_psi.py`, all logs and 600 random instances):
1,414 pairs (linking pair, anchor `h`), no failure; the false variant with
`(v_h - v_g)/2` on the right fails 472 times.

*Formal statement (for Lean).* Data: the epoch, `t < n - 1`, a D-pair `(y, g)`,
`h in B* cap R cap C(B*, y)`, first events `delta_i`. Hypotheses:
`v^t_y - delta_t <= v^t_h`; `v^{i+1}_y - v^{i+1}_g <= v^i_y - v^i_g - delta_i`
for all `i`; `v^{n-1}_y - v^{n-1}_g > 0`. Conclusion:
`sum_{i=t+1}^{n-2} delta_i < v^t_h - v^t_g`.

## 2. Theorem E.5: Conjecture P for components with at most two raised values

**Theorem E.5.** Consider an epoch with `rho >= 1` and its base `B*`. Suppose
every component `K` of `M` that contains a raised anchor is of one of two types:
- (a) all raised anchors of `K` have one value;
- (b) the raised anchors of `K` take exactly two values `a = a_K < T = T_K`, and
  (H2) no element of `R cap K` has value in the open interval `(a, T)`, and
  (H1') no `x in (R - B*) cap K` with `v_x = a` has an unraised element in
  `C(B*, x)`.
Then

    n <= 1 + P1(v^0) <= m - rho.

(The hypotheses concern `v^0`; they hold at every state of the epoch, since raised
elements move together and fundamental circuits do not depend on the weights.)

*Proof.* Step 0, the potentials. For `K` of type (a) put
`Psi_K(v) = |{z in U cap K : v_z < T_K}|`. For `K` of type (b) put
`W_K(v) = {z in U cap K : a <= v_z < T}`, call an update *high in K* if it is
not last, links in `K`, and its linking anchor has `v_g >= a`, and put

    Psi_K(v^j) = |{z in U cap K : v^j_z < T}| + iota_K(j),
    iota_K(j) = 1  iff  W_K(v^j) is empty, some z in U cap K has v^j_z < a,
                        and none of the updates 0, ..., j-1 is high in K;
    iota_K(j) = 0  otherwise.

Write `N_K(j) = |{z in U cap K : v^j_z < T_K}|` and `c` for the number of
elements of `U cap K` crossing `T_K` at the update considered.

Step 1, linking in a component of type (b). Let update `j < n - 1` link in `K`
of type (b), with pair `(y, g)`, cluster `C` and scale `delta`. By Lemma A.2 some
raised anchor `h in C(B*, y)` has `v_y - delta <= v_h <= v_y`, so
`v_h in {a, T}`, and every element of `C(B*, y) - y` with value at least
`v_y - delta` is a raised anchor, so

    v_g < v_y - delta <= v_h <= T.

If `v_y < T`, then `v_h = a <= v_y < T`, so `v_y = a` by (H2), and `g in C(B*, y)`
contradicts (H1'). Hence `v_y >= T`, and `C`, an interval of the values of
`PO_delta cap K` containing `v_g` and `v_y`, contains every raised anchor of `K`
with value in `[v_g, v_y]`. Every raised element of `K` in `PO_delta` has value
at least `a` (Lemma A.2), and none has value in `(a, T)` (H2).

Step 2, no increase. For every component `K` of type (b) and every update `j`,
`Psi_K(j + 1) <= Psi_K(j)`. Unraised elements rise relative to raised ones, so
`N_K(j + 1) = N_K(j) - c` with `c >= 0`. If `iota_K(j + 1) = 1` and
`iota_K(j) = 0`: no update before `j + 1` is high in `K`, `W_K(v^{j+1})` is empty
and some `z` lies below `a` at `v^{j+1}`, hence at `v^j`; so `iota_K(j) = 0`
forces `W_K(v^j)` to be nonempty, and its elements, at least `a` at `v^{j+1}`
but not in `W_K(v^{j+1})`, crossed `T`, so `c >= 1`. In all cases

    Psi_K(j+1) - Psi_K(j) = -c + iota_K(j+1) - iota_K(j) <= -c + [c >= 1] <= 0.

For `K` of type (a), `Psi_K = N_K` does not increase.

Step 3, a non-last update linking in `K` of type (b) with `v_g < a`. Then
`v_g < a < T <= v_y`, so the raised anchors of values `a` and `T` lie in `C`.
Let `z1` be the unraised element of `C` with the largest value below `a`
(`g` qualifies). No value of `C` lies in `(v_{z1}, a)` (an unraised one would
contradict the choice of `z1`, a raised one has value at least `a`), so by Lemma
E.2 `z1` crosses `a`, and at `v^{j+1}` it lies in `W_K` or at or above `T`.
- Case `W_K(v^j)` nonempty. Let `gamma` be the largest value of `C` below `T`;
  `gamma >= a`. If `gamma > a`, the elements of `C` with value `gamma` are
  unraised (H2), lie in `W_K(v^j)`, and cross `T` by Lemma E.2. If `gamma = a`,
  then `T - a <= delta`, and every `z in W_K(v^j)` has `v_g < v_z < T` and next
  value `T` in `C`, so it crosses `T` by Lemma E.2. So `c >= 1`, and
  `iota_K(j) = 0`. If `iota_K(j + 1) = 1`, then `W_K(v^{j+1})` is empty, so every
  element of `W_K(v^j)` and `z1` crossed `T`: `c >= |W_K(v^j)| + 1 >= 2`. Hence

      Psi_K(j+1) - Psi_K(j) <= -c + iota_K(j+1) <= -1.

- Case `W_K(v^j)` empty. The values of `C` strictly between `a` and `T` would
  belong to unraised elements of `W_K(v^j)` or to raised elements excluded by
  (H2), so `a` and `T` are consecutive values of `C`:

      T - a <= delta_j.                                                   (*)

  If an update `t < j` were high in `K`, with linking pair `(y', g')` and anchor
  `h'` as in Lemma E.4, then `v_{h'} <= T`, `v_{g'} >= a`, and Lemma E.4 would give

      delta_j <= sum_{i=t+1}^{n-2} delta_i < v^t_{h'} - v^t_{g'} <= T - a,

  against (*). So no earlier update is high in `K`, and `iota_K(j) = 1`
  (`z1` lies below `a`). If `z1` crosses `T`, then `c >= 1` and

      Psi_K(j+1) - Psi_K(j) <= -1 + iota_K(j+1) - 1 <= -1;

  otherwise `z1 in W_K(v^{j+1})`, `iota_K(j + 1) = 0`, and
  `Psi_K(j+1) - Psi_K(j) <= 0 - 1 = -1`.

Step 4, a non-last update linking in `K` of type (b) with `v_g >= a` (high).
By Step 1, `a <= v_g < T <= v_y`, so the raised anchor of value `T` lies in `C`.
Let `gamma` be the largest value of `C` below `T`; `gamma >= v_g >= a`. If
`gamma > a`, the elements of `C` of value `gamma` are unraised (H2); if
`gamma = a`, then `v_g = a` and `g` has value `gamma`. Either way an unraised
element of `C` of value `gamma` lies in `W_K(v^j)` and crosses `T` by Lemma E.2,
so `c >= 1`. The update is high, so `iota_K(j + 1) = 0`, and

    Psi_K(j+1) - Psi_K(j) <= -c + 0 - iota_K(j) <= -1.

Step 5, components of type (a). A non-last update linking in `K` of type (a)
makes an unraised element of `K` cross `T_K` (B0d, Theorem A', Step 1: case (IV)
needs two raised values in `K`), so `Psi_K` drops by at least 1.
Step 6, counting. Every non-last update links in one component, which contains a
raised anchor (Lemma A.2). By Steps 2 to 5 the sum `Psi = sum_K Psi_K` drops by
at least 1 at each of the updates `0, ..., n - 2` and never increases, and
`Psi >= 0`. So

    n - 1 <= Psi(v^0) - Psi(v^{n-1}) <= Psi(v^0).

For `K` of type (b), Lemma B.2 gives a twin `x in (R - B*) cap K` of the raised
anchor of value `a`, with `v_x = a < T`, so

    Psi_K(v^0) <= N_K(0) + 1 <= |{e in K - (R cap B*) : v^0_e < T}|,

and for type (a), `Psi_K(v^0) = N_K(0)`. Summing, `Psi(v^0) <= P1(v^0)`, and
`P1(v^0) <= m - rho - 1` (B0d, Section 5).

*Hypotheses used:* B0 Lemma 1.1, Theorem 2.2(1); B0d Lemmas A.2, B.2 and
Theorem A'; Lemmas E.2 and E.4; Steps 2, 3, 5 of the proof of Theorem
`thm:potential`; the interval property of PO-SL clusters; `B*` in `PO_0`.
(H1') is used only in Step 1, (H2) in Steps 1, 3, 4. So the conclusion
`n <= 1 + P1(v^0)` also holds for every epoch whose components with raised
anchors are of type (a) or satisfy (H2), provided that every update linking in
a component `K` of the second kind has some linking pair with `v_y >= T_K` (that
pair is then the one fixed for the update). The history clause of
`iota_K` is paid for by Lemma E.4: without it, a high update that empties `W_K`
while unraised elements remain below `a` would leave `Psi_K` unchanged.

*Checks* (`ep2_psi.py`): on all epochs of the logs of B0, B0d, of this note's
searches against `Phi` and of 600 random instances, 533 epochs (of every `rho`)
have only components of types (a) and (b)
(100 of them with a component of type (b)); the conditions C1 (no increase), C2
(a drop at every non-last update in the linking component; 1,076 updates, 187 of
them in a component of type (b)) and C3 (`n <= 1 + Psi(v^0) <= 1 + P1(v^0)`,
equality on 172 epochs) never fail. The false variants fail: without `iota_K`,
C2 fails at 16 updates; applying `Psi_K` to components violating (H2) fails on
24 of the 30 such epochs. The same checks on the epochs of the searches against
Q and P (`ep2_logs/searchQ_*.txt`; 27 updates, 19 in type (b)) found no failure.
A hill climbing aimed at C1, C2, C3 is in Section 5.

*Formal statement (for Lean).* Data: as in the formal statement of Theorem A
(B0d, Section 2): `M`, `blk`, `r < k`, states `v^0, ..., v^n` of an epoch of
stage `r` with `S`, `R = E_S`, `rho = |S| - (k - r) >= 1`, `B*` a base of
`M^{v^0}` meeting exactly `r` blocks. Hypotheses: for every connected component
`K` with `K cap B* cap R` nonempty, either `v^0` is constant on `K cap B* cap R`,
or it takes exactly two values `a_K < T_K` there, no `e in R cap K` has
`a_K < v^0_e < T_K`, and no `x in (R \ B*) cap K` with `v^0_x = a_K` has
`C(B*, x) \ R` nonempty. Conclusions: `n <= 1 + P1(v^0)` and `n <= m - rho`,
where `P1(v) = |{e notin R cap B* : K(e) cap B* cap R nonempty, v_e < T_{K(e)}}|`.
Lemmas to formalize first: B0 Theorem 2.2(1); Step 5 of the proof of Theorem
`thm:potential` (the linking pair); B0d Lemma A.2, Lemma B.2, Theorem A';
Lemmas E.2 and E.4.

**What the theorem covers.** Every epoch with `rho = 1` (type (a)); every epoch
whose raised anchors in each component share one value (B0d's Theorem A'); the
epochs with two raised values in a component whose raised non-anchors are twins
and parallel copies at the two values, or elements above the top value. This is
the shape of B0d's R4 instance (stage 3, `n = 7 = 1 + P1(v^0)`, with repeats)
and of the counterexamples R8, R8a, R8b to Conjecture Q (Section 3). It does not
cover B0d's
reuse example (raised non-anchor 8 strictly between 12491 and 23266), nor B0's
epoch with `|U| = |R| = 5` (raised non-anchor 5 strictly between 233742 and
313619), nor any component with three raised values (the twin of the middle
anchor lies strictly between the extreme values). Among the 281 epochs with
`rho >= 2` of all logs and 600 random instances, 223 are covered (100 of them
with a component of type (b); 75 with `n = 1 + P1(v^0)`), 30 fail (H2), 14 have
a component with three raised values and 14 fail only (H1'); Conjecture P holds
on all 281 (largest `n - 1 - P1(v^0)`: 0 in the first three groups, -2 in the
last).

## 3. Refuted statements

**R8. Conjecture Q of B0d** ("#repeats + #(case (IV) updates) <=
|{x in R - B* : v^0_x < T_{K(x)}}|"). Found by `ep2_searchQ.py graphic 6 12 1200
2 Q` (objective: the slack of Q; log `ep2_logs/searchQ_Q_graphic_6_12.txt`) and
minimized by `ep2_minimize.py` (deleting edges and lowering weights while the
slack stays positive).

*Minimized instance R8.* Graphic, 6 vertices, edges
`04,42,25,10,42,03,31,43,35` (elements 0 to 8), blocks `[2,4,4,1,3,1,1,1,0]`,
weights `[2,5,8,5,5,3,6,1,8]` (`m = 9`, `k = 5`). Stage 4, epoch
`S0 = {0,3,4}`, `rho = 2`, `B* = {0,1,3,7,8}`, `n = 5`. Raised anchors 1 (value
`a = 5`) and 8 (`T = 8`); raised non-anchors 4 (the twin of 1, parallel to it,
value 5) and 2 (value 8, the linking element; its circuit contains the unraised
anchor 7). Unraised: 7 (value 1), 0 (2), 5 (3) below `a`, and 3 (5), 6 (6) in
`[a, T)`. Every update has `delta = tau` and linking pair `(2, 7)`:

| update | `delta` | designation | other crossings of `T` |
|---|---|---|---|
| 1 | 2 | 5 crosses `a` | 6 |
| 2 | 2 | 0 crosses `a` (7 crosses `a` as well) | 3 |
| 3 | 1 | 5 crosses `T` (repeat) | |
| 4 | 1 | 0 crosses `T` (repeat) | |
| 5 | 1 | last (7 reaches 2: `D = 0`) | |

Repeats 2, case (IV) updates 0, raised non-anchors below `T`: only the twin 4.
So `2 > 1`. Conjecture P holds: `n - 1 = 4 <= P1(v^0) = 5 + 1 = 6`; the
unraised elements 6 and 3 cross `T` without ever being designated, and these are
the tokens that pay for the repeats. The instance is of type (b) of Theorem E.5,
and `Psi = 5, 4, 3, 2, 1` along the epoch.

Instance R8a (as found): graphic, 6 vertices, edges
`31,04,42,25,10,53,42,43,03,31,43,35`, blocks `[3,2,4,4,1,4,3,2,1,1,1,0]`,
weights `[1281482,133,11648,17729,10126,17727,32915,4,3019,6032,1,4212010]`
(`m = 12`, `k = 5`). Stage 4, epoch `S0 = {0,3,4}`, `rho = 2`, `n = 8`. In the
R-frame: raised anchors 2 (value `a = 11648`, twin 6) and 11 (`T = 17727`,
twin 5), raised non-anchors 3 (17729, the linking element, with the unraised
anchor 10 in its circuit) and 0 (far above); unraised 10, 7, 1, 8, 9, 4 below
`a`. Designations: `(a, 4), (a, 8), (a, 1), (T, 8), (T, 1), (T, 7), (T, 10)`,
last. The repeats are 8 and 1, there is no case (IV) update, and the only raised
non-anchor below `T` is the twin 6: `2 > 1`. Conjecture P holds with equality:
`P1(v^0) = 6 + 1 = 7 = n - 1`. The extra token comes from the unraised anchor 9,
which crosses `a` at update 1 and `T` at update 3 without ever being designated.
Instance R8b: graphic, 6 vertices, edges `13,34,52,14,50,04,20,51,20,34,20,52`,
blocks `[0,0,1,3,4,4,4,3,0,2,1,2]`, weights `[479687,466508,458311,679,173546,
252769,3835886,75534,3630001,810749,1917939,662535]`, stage 4, `rho = 2`,
`n = 6`, repeats 7 and 3, budget 1, `P1(v^0) = 5 = n - 1`. R8, R8a and R8b
satisfy the hypotheses of Theorem E.5 (type (b) by `ep2_psi.comp_type`: no
raised element strictly between the two raised values, no linkable raised
non-anchor at the lower value).
*Verification.* `ep_conjQ.py` (B0d's own script) reports R8a and R8b as
failures with slack 1; `ep2_refQ.py` recomputes states, `S0`, `B*`, the first
events, the PO-SL clusters, the linking pairs and the cases with the referee
code only (`referee_phase2a/core.py`), with a different `B*` in each case, and
finds the same counts for R8, R8a and R8b (repeats 2, case (IV) 0, budget 1);
`ep2_referee.py` checks that the state sequences of both implementations
coincide on all three.

So the right count mixes the two kinds of tokens: an unraised element that
crosses the top value without being designated pays for a repeat, which is how
P survives where Q fails (B0d's R5 was the other half of this observation).

**R6. The gap potential `Phi` (Section 4) is not a potential.** Instance R6a:
graphic, 5 vertices, edges `01,12,23,34,12,23,02,04,12,34,34`, blocks
`[0,1,2,0,3,3,3,1,3,0,0]`, weights `[0,10,100,0,10,100,11,1000,50,45,60]`
(`m = 11`, `k = 4`). Stage 3, `S0 = {1,2,3}`, `rho = 2`, `B* = {0,1,2,3}`,
`n = 2`. Raised anchors 1 (value 10) and 2 (100); raised non-anchors 4 (twin,
10), 6 (11, circuit `{6,0,1}`), 8 (50, parallel to 1), 5 (twin, 100), 7.
Update 1 has `delta = tau = 10`, linking pair `(6, 0)` (low: the anchor within
`delta` below 6 has value 10 < 100), and is not last (`D = 11 -> 1`). It moves
the unraised element 9 from 45 past the raised element 8 (value 50) into the gap
`[50, 100)` already occupied by 10, so the gap `[11, 50)` becomes empty with the
unraised elements 0, 3 below it: `Phi = 5 -> 5`. Instance R6b (B0's halving
ladder with `L = 4` plus a top anchor): graphic, 5 vertices, edges
`30,20,10,10,21,20,20,20,20,14,14,42`, blocks `[1,1,0,2,0,1,1,1,1,3,2,1]`,
weights `[0,0,16,16,17,8,4,2,1,64,64,1600]`: stage 3, `rho = 2`, `n = 6`,
`P1 = 7`, `Phi = 7, 6, 5, 5, 5, 5` (every update links low, at value 16, and the
designees pile up in the gap `[17, 64)`). Conjecture P holds on both (`n - 1 = 1`
and `5`, against `P1 = 7`). R6a, R6b, R8, R8a, R8b and B0d's R4 instance agree
exactly with the referee implementation (`ep2_referee.py`, state by state).

**R7. "The linking is always top."** On all 397 updates with `rho >= 2` that are
not last in the logs of B0 and B0d (`ep2_linkpos.py`), every linking pair has a
raised anchor of value `T_K` within `delta` below `y`. R6a, update 1, is a
counterexample (linking pair `(6, 0)`, anchors within `delta = 10` below 6: only
the anchor of value 10 < 100). In the searches against `Phi` all 16 failures of
`Phi` are at low-linking updates (`ep2_logs/search_phi_*.txt`).

**R9. "`Phi` drops at every update whose linking reaches the top value."** True
at all 1,250 such updates in the data (Section 4), false in general; the
instance was built by hand from the failing step identified in Section 6 (an
update that empties the lower gap into an occupied upper gap while an unraised
element stays below `a`). Graphic, 5 vertices, edges
`01,12,23,34,01,12,01,13,23,01,41,02` (elements 0 to 11), blocks
`[1,2,0,0,3,3,2,1,0,0,3,2]`, weights
`[100,200,96,40,100,200,104,210,102,150,1000,5000]` (`m = 12`, `k = 4`, one
unraised block, so every update moves `U` rigidly). Stage 3, `S0 = {1,2,3}`,
`rho = 2`, `B* = {0,1,2,3}`, `n = 4`. Raised anchors 0 (`a = 100`) and 1
(`T = 200`); raised non-anchors 4 (twin of 0), 6 (the gate, parallel to 0,
value 104), 5 (twin of 1), 7 (210, circuit `{7,1,2}`), 10, 11. Unraised: 3
(anchor, 40), 2 (anchor, 96), 8 (102, parallel to 2), 9 (150, parallel to 0).
Update 1: `delta = tau = 50` (the element 9 enters `PO_t` at `t = 50` and
closes the chain `2, 0, 8, 6, 9, 1, 7`), linking pair `(7, 2)` with the top
anchor 1 within `delta` below 7, not last (`D = 114 -> 64`). It moves 2 from 96
past `a` and the gate into `[104, 200)`, moves 8 from 102 past the gate, moves 9
to `T`, and leaves 3 at 90 below `a`: the gap `[100, 104)` is emptied while 3
stays below it, one element crosses `T`, and `Phi = 4 -> 4`. Conjecture P holds
(`n - 1 = 3 <= P1(v^0) = 4 + 2`). The referee implementation agrees state by
state (`ep2_referee.py`). So the obstacle "raised elements strictly between two
raised values" is not an artifact of the proof: the gap potential itself fails
there, already for `rho = 2`, one gate and rigid motion.

## 4. The gap potential Phi (data; refuted as a potential)

For a component `K` with raised anchors let `rho_0 = a_K < rho_1 < ... < rho_L =
T_K` be the distinct values of the raised elements of `K` in `[a_K, T_K]`, and
`G_i = [rho_{i-1}, rho_i)`. A gap is *pending* if it contains no unraised element
of `K` while some unraised element of `K` lies below `rho_{i-1}`.

    Phi(v) = sum_K ( |{z in U cap K : v_z < T_K}| + #{pending gaps of K} ).

Equivalently `Phi_K = sum_{i = j0}^{L} max(N_i, 1)` with `N_i` the number of
unraised elements of `K` in `G_i` and `j0` the gap of the lowest one.
`Phi <= P1`: the upper end of each gap `G_i` with `i < L` is the value of a raised
non-anchor in `(a_K, T_K)` (a twin, Lemma B.2, when it is a raised-anchor value),
and the top gap is matched with the twin of the anchor of value `a_K`. Data
(`ep2_phi.py`, `ep2_phi_events.py`): on the 473 epochs with `rho >= 1` of the
logs of B0, B0d and 400 random instances, `Phi` drops by at least 1 at every
update that is not last (1,201 updates); at the 191 such updates with `rho >= 2` of B0's logs it
drops by exactly 1 (186 of them with `tau = delta`). False variants fail: without
the pending term on 41 epochs, counting empty gaps without the condition on the
elements below on 45, with only the raised-anchor values as gap ends on 23, and
"drops by at least 2" on 223. The searches aimed at `Phi` (`ep2_search.py`)
broke it within 20 minutes (R6), always at low-linking updates. Over all
logged, searched and 600 random instances (`ep2_phi_by_span.py`), `Phi` drops
at each of the 1,250 non-last updates that have a linking pair with
`v_y >= T_K` (36 of them in epochs with three raised values in a component,
many in epochs with raised elements strictly between two raised values), and
fails at 17 of the 30 updates whose linking pairs are all low; R9 shows that
the first observation is not a theorem. `Phi` is `Psi` of Theorem E.5 when (H2)
holds, without the history clause; the history clause and Lemma E.4 are what
makes the proof of Theorem E.5 work.

## 5. Searches (exponential integer weights up to `2^24`, hill climbing)

| script, objective | instances | workers x s | best |
|---|---|---|---|
| `ep2_search.py`, `Phi` violation | graphic 6 vertices, `m = 12` | 2 x 1200 | violation 2 (`Phi` rises by 1), at low-linking updates; `n - 1 - Phi(v^0) <= -2` |
| same | two multigraphs glued at a vertex, 7 vertices, `m = 13` | 2 x 1200 | same |
| `ep2_searchQ.py`, slack of Q | graphic 6, `m = 12` | 2 x 1200 | **slack 1** (R8a, R8b), with `n - 1 - P1 = 0` |
| `ep2_searchQ.py`, `n - 1 - P1` | trees + parallel copies + 3 chords, 7 vertices, `m = 14` | 2 x 1200 | `n - 1 - P1 = 0` (never positive) |
| same | binary rank 5, `m = 12` | 2 x 1200 | `n - 1 - P1 = 0` (never positive) |
| same | glued multigraphs, 7 vertices, `m = 13` | 1 x 1200 | `n - 1 - P1 = 0` (never positive) |
| `ep2_searchE5.py LOW`, `n - 1 - P1` over epochs with a low-linking update | trees + parallel copies + 3 chords, 7 vertices, `m = 14` | 1 x 1200 | `n - 1 - P1 = -1` (an epoch with 6 low-linking updates, `n = 7`) |
| `ep2_searchE5.py E5`, violations of C1, C2, C3 (test of Theorem E.5) | trees + parallel copies + 3 chords, 7 vertices, `m = 14` | 1 x 900 | no violation; longest epoch of the class found: stage 5, `rho = 2`, `n = 11 = m - 3`, `P1 = 11` |
| `ep2_searchE5.py S3`, `n - 1 - P1` over epochs with three raised values in a component | trees + parallel copies + 3 chords, 8 vertices, `m = 15` | 1 x 900 | `n - 1 - P1 = 0` (never positive), `n = 10` |
| `ep2_ft_search.py ft2` (weights only, fixed design aimed at high updates that empty `W_K`) | graphic 6 vertices, `m = 13` | 1 x 900 | no such update; `n - 1 - P1 = 0` |

## 6. Open problems and obstacles

1. **Conjecture P in general.** It survives all searches of B0d and of this
   note (best `n - 1 - P1 = 0`), and Theorem E.5 proves it for components with
   at most two raised values, no raised element strictly between them, and no
   linkable raised non-anchor at the lower value. Three obstacles remain; each
   is a place where the proof of Theorem E.5 breaks, not a known failure of P.
   - *Low linking* (R6, R7): the linking raised non-anchor `y` sits above a
     raised anchor below the top value, the cluster ends near `y`, and the
     conveyor (Lemma E.2) does not act above `y`. The designees of a low-linking
     ladder pile up above `y` (R6b). Lemma E.4 still applies: after a low
     linking at value `l`, the later first events sum to less than `l - v_g`.
     A proof must show that a designee of a low-linking update is not pushed
     across `T` by a later update that has nothing else to pay with. In the
     potential of Theorem E.5 this is the only failing step: a low-linking
     update with `W_K` nonempty and no crossing of `T` leaves `Psi_K` unchanged.
   - *Raised elements strictly between two raised values* (gates; R6a and R9
     have one). The natural potential is `Phi` (one pending indicator per gap
     `G_i = [rho_{i-1}, rho_i)`) with a history clause per gap. Two steps fail.
     First, an update can empty a gap, also below the linking anchor or in a
     component other than the linking one, by moving its elements into an
     occupied higher gap; this re-arms the indicator of the emptied gap with a
     single crossing of `T` to pay for it, and R9 realizes it at a top-linking
     update (so a history clause must also cover this event, and Lemma E.4,
     which bounds the later first events after R9's update by `T - v_g = 104`,
     does not exclude a later restart into the gap `[100, 104)`). Second, the
     restart argument (Step 3 of Theorem E.5) needs, for a gap `G_i`, that the
     later first events stay below `rho_i - rho_{i-1}`, while Lemma E.4 bounds
     them only by `T - v_g`, which suffices for the top gap and not for lower
     ones.
   - *Three or more raised values in a component.* The twins of the middle
     raised anchors are gates, so the second obstacle applies. A concrete case
     where a gap potential stays constant: values `a_1 < a_2 < T`, the linking
     anchor `g` is the only unraised element of `[a_1, a_2)` and the designee,
     it crosses `a_2` into an empty gap `[a_2, T)`, and unraised elements remain
     below `a_1`; the indicator moves from the upper gap to the lower one. The
     budget of P has one twin per raised value below `T`, so P itself is not
     contradicted; the accounting has to let each twin pay once.
2. **A weaker target that would suffice for Theorem C**:
   `n <= 1 + P1(v^0) + c(k)` with `c(k) = O(m)`, for instance `c(k) <= k`. The
   three obstacles above each involve an unraised anchor that is the linking
   anchor of the update, which suggests a defect bounded by a function of the
   number of unraised anchors (at most `k - rho`) times the number of raised
   values.
3. **Monotone phases.** In all data the active raised value is non-decreasing
   (B0d, observation 3). Lemma E.4 proves a part of it in the setting of
   Theorem E.5: after an update whose linking anchor has passed `a`, no update
   can find `W_K` empty with an unraised element below `a` and link across
   `[a, T]` (Step 3).
4. **Suggested next step.** Extend Theorem E.5 to one gate (a raised element
   strictly between `a` and `T`, as in B0d's reuse example and R9) in a single
   component. R9 shows that the pending indicator of the lower gap must not be
   re-armed for free when that gap is emptied into an occupied upper gap; the
   budget of P has one raised non-anchor per gap (the gate, and the twin of the
   anchor of value `a`) that `Phi(v^0)` does not use when the gaps start
   occupied (in R9, `Phi(v^0) = 4 < P1(v^0) = 6`). A potential that gives each
   gap one token, spent at most once, at the first update that needs it (a
   restart into that gap with no crossing of `T`), is the candidate; the proof
   must show that a second restart into the same gap is paid by an extra
   crossing, as in Step 3 of Theorem E.5.

## 7. Consequences for the stage length and Theorem C

Notation of B0d, Section 6: Theorem C runs stage `r` for `ell_r` updates.

**Unconditional.** Theorem E.5 does not cover every epoch, so the stage bounds
of B0d stand: `ell_1 = 1`, `ell_2 = m - 1`,
`ell_r = (m - 1) + (r - 2) min(k m, floor(m^2/4) + 1)` and
`ell_r <= m r (r - 1)/2 + (r - 2)(1 + k^2 (k - 1)/2) - 1` (`r >= 2`); Theorem C
keeps the order `O(k^4 m^6 (s + m))` with about `k^3 m / 6` updates when
`m >> k^2`.

**For the epochs covered by Theorem E.5** (in particular every stage whose epochs
with `rho >= 2` have at most two raised values per component, no raised element
strictly between them and no linkable raised non-anchor at the lower value),
every epoch with `rho >= 1` has at most `m - rho` updates, so such a stage has at
most `1 + sum_{rho=1}^{r-1} (m - rho) = 1 + (r - 1) m - r (r - 1)/2` updates.

**Under Conjecture P** (or the weaker `n <= 1 + P1(v^0) + c(k)`):

    ell_r <= 1 + (r - 1) m - r (r - 1)/2   (+ (r - 1) c(k)),
    sum_{r=1}^{k-1} ell_r <= (k - 1) + m (k - 1)(k - 2)/2 - (k - 2)(k - 1) k / 6
                             (+ (k - 1)(k - 2) c(k) / 2),

about `k^2 m / 2` update blocks (plus `(k - 1)(k - 2) c(k) / 2`), a factor `k`
below the proved count `k^3 m / 2`. With B0d's cost per block, Theorem C becomes
`O(k^3 m^6 (s + m))` whenever `c(k) = O(m)` (for instance `c(k) <= k`), and
`O(k^3 m^6 (s + m) + k^3 c(k) m^5 (s + m))` in general (B0: each update costs
`O(k m^5 (s + m))`). The refutation of Q does not affect this: Q was only a
route to P.

## 8. Scripts (all in `experiments/`, exact integer or Fraction arithmetic)

| script | what it does |
|---|---|
| `ep2_common.py` | epochs of the schedule with their states, `delta`, `tau`, `B*`; `P1`; instance sources (log globs, random) |
| `ep2_trace.py` | R-frame trace of the epochs with `rho >= 2`: tags, `PO_delta`, clusters, linking pairs, case, crossings |
| `ep2_phi.py` | the gap potential `Phi` and its false variants F0 to F3 on logged and random epochs |
| `ep2_phi_events.py` | what makes `Phi` drop (newly pending gaps, filled gaps, crossings of `T`) |
| `ep2_phi_states.py` | one-update test of `Phi` at random states |
| `ep2_phi_by_span.py` | `Phi` at updates with a linking pair reaching the top value, and at low-linking updates |
| `ep2_linkpos.py` | top or low linking at every update (R7) |
| `ep2_search.py` | hill climbing against `Phi` (graphic, glued, structured instances) |
| `ep2_searchQ.py` | hill climbing against Q or P (objective: slack), counts low-linking updates |
| `ep2_psi.py` | Theorem E.5 (C1, C2, C3 and the false variants V1, V3) and Lemma E.4 (and its false variant) |
| `ep2_lemmas12.py` | Lemmas E.1 and E.2 and their false variants |
| `ep2_repeat_anchor.py` | Lemma E.3 and two false variants |
| `ep2_searchE5.py` | hill climbing in four modes: `E5` (violations of Theorem E.5), `LOW` (P on epochs with low linking), `S3` (P on epochs with three raised values in a component), `PHIT` (`Phi` at top-linking updates) |
| `ep2_referee.py` | state-by-state agreement with the referee implementation on R6a, R6b, R8, R8a, R8b, R9 and B0d's R4 instance |
| `ep2_refQ.py` | recomputation of the Q count of R8, R8a, R8b with the referee code only |
| `ep2_minimize.py` | greedy minimization of a counterexample to Q |
| `ep2_ft_search.py` | weight-only hill climbing on a fixed design aimed at high updates that empty `W_K` (the step that the history clause of Theorem E.5 handles) |
