# Phase 2d: the length of one PO-SL epoch (2026-10-12)

Question: the worst-case number of PO-SL updates in one epoch (fixed stage `r`,
fixed `S0 = S`), as a function of `m`, `k`, `rho`, `|R|`, `|U|`; consequence for
the stage length (paper, Section 7, first open problem) and for Theorem C.
Setting: `paper/greedy_intersection.tex`, Section 4; note
`docs/phase2b-stage-length-2026-10-12.md` (B0), Sections 1 and 2.

## Status log (for a relaunched agent)

- 2026-10-12, coordinator. Read Lemmas A.1, A.2, Theorem A (and its sharp form) and
  Lemma B.2 against B0 and the paper: the steps hold as written. Not formalized and not
  in the paper: the gain over Theorem `thm:stagelength` is a constant factor. The
  continuation `docs/phase2e-epoch-rho2-2026-10-12.md` (Conjecture P for rho >= 2) was
  stopped without a proof.
- 17:12 start. Read paper Section 4, B0 Sections 1 and 2, `stage_core.py`.
  Scripts go to `experiments/ep_*.py`, logs to `experiments/ep_logs/`.
- 17:22 launched `ep_search.py` (objective `n - m`, graphic `6/12`, `7/14`,
  `8/15`, 3 workers each, 1500 s; logs `ep_logs/search_m_graphic_*.txt`).
- 17:25 refuted "epoch <= m - k + rho - 1" in 20 s (Section 7, R1).
- 17:35 charging data (Section 7): on the 354 epochs of the B0 logs, the
  updates always admit a system of distinct representatives among the elements
  of their anchored crossing pairs (scheme E); charging only non-anchors fails
  once; greedy online rules fail.
- 17:48 searches `n - m` (graphic `6/12`, `7/14`, `8/15`, 9 workers, 1500 s)
  done: best `n = m - 2` everywhere, always `rho = 1`, `|R| = 2`, `|U| = m - 2`
  (pure ladders). Found and proved Theorem A (`rho = 1`: at most `|U| + 1`
  updates, Section 2). Launched `ep_verify_rho1.py 3` (exhaustive zoo,
  6 workers, log `ep_logs/verify_rho1_L3.txt`) and `ep_search.py` with
  objective `n - m` over epochs with `rho >= 2` (4 workers, log
  `ep_logs/search_mrho2_graphic_6_12.txt`).
- 18:00 to 18:20 proved Lemmas B.1 (dichotomy), B.2 (twins), Theorem A' (one
  raised value per component), the sharp form `n <= m - 2` of Theorem A, and
  Corollary A.3 (stage 2 at most `m - 1`); formulated Conjectures P and Q
  (tight on all epochs tested). Exhaustive zoo run at `L = 3` done (no
  failure). Running at 18:20: `ep_struct.py` (`n - m`, `rho >= 2`, 5 workers,
  log `ep_logs/struct_mrho2_7_14.txt`), `ep_search.py` against Conjecture P
  (`P1+1|rho>=2`, 4 workers, `ep_logs/search_P1_graphic_6_12.txt`); queued:
  the same at `k = 6` and B0's `stage_search_exp.py` at `k = 7`
  (`ep_logs/stage_excess_graphic_8_14.txt`).
- 18:20 to 18:35: Corollary A.3 shown tight (stage 2 of `m - 1` at `k = 3` in
  B0's logs); stage formula refined (Section 6); cross-epoch data (Section 6);
  Conjecture Q statistics; observations 3 and 4 checked on 216 epochs.
- 18:35 to 18:45: Lemma B.3 (mirror ladders), Lemma P.0 (`P1` independent of
  `B*`), direct check of Theorem A', referee cross-check of all cited
  instances (`ep_referee.py`, no mismatch), Conjecture P survived the search
  against it at `k = 5` (best `n - 1 - P1 = 0`); refuted the strengthening R5;
  stage search at `k = 7`: `m + 6`. 18:53: the search against Conjecture P at
  `k = 6` (`ep_logs/search_P1_graphic_7_14.txt`) also stopped at
  `n - 1 - P1 = 0`.
- 18:55 to 19:05: Corollary B.4 (every `rho`; the `O(k m)` contribution of the
  crossings of raised non-anchors with unraised anchors replaced by `O(k^3)`)
  and its stage formula; the search against Conjecture P at `rho >= 3`
  (`ep_logs/struct_P1rho3_8_15.txt`) also stopped at `n - 1 - P1 = 0`. All
  searches finished; no workers left running. Final counts: Conjectures P and
  Q on 468 epochs, no failure.
- Open: Conjectures P and Q (`rho >= 2`); the stage length across epochs.
- How to resume: the proofs are complete in Sections 1 to 5 (Theorem A, its
  sharp form, Theorem A', Lemmas A.1, A.2, B.1, B.2, B.3, P.0, Corollaries A.3,
  B.4). The next
  step is a proof of Conjecture Q for two raised values in one component
  (`rho = 2`), where the data shows a clean two-phase structure (Section 5);
  `ep_cases2.py` and `ep_repeats.py` (prints, per epoch with repeats, the
  designations with the raised non-anchors passed) are the starting point.
  Mechanism seen in every traced two-value epoch (values `a < T`): in the
  phase at `a`, each update after the first also moves the previously
  designated element (or an unraised element above it) past the next raised
  element above it, either the top value `T` (that element is then never
  designated again) or a raised non-anchor of `[a, T)`; the last element
  designated at `a` is paid by the twin of `a`. Turning this into an injection
  from repeats and case (IV) updates to `R - B*` below `T` would prove Q for
  `rho = 2`, hence stage 3 at most `1 + (m - 2) + (m - 2)`.

## Summary of results

**Proved** (Sections 1 to 5; every proof uses only B0's Lemma 1.1 and
Theorem 2.2 (part (3) only in Lemma B.3 and Corollary B.4), Step 5 of the proof
of Theorem `thm:potential`, Theorem `thm:validity`(2), Lemma `lem:minbases`,
the interval property of PO-SL clusters and, for Lemma B.2, the sharp form of
Theorem A and Corollary B.4, the symmetric basis exchange property).
1. Lemmas A.1, A.2 (every `rho`): at an update that is not the last of its
   epoch, `D > delta`, and every raised non-anchor in `PO_delta` lies within
   `delta` above a raised anchor of its fundamental circuit, with no unraised
   anchor of that circuit within `delta` below it.
2. Theorem A (`rho = 1`, `B* cap R = {h}`): every update but the last makes an
   unraised element of the component of `h` pass `h`, so
   `n <= 1 + |{z in U cap K(h) : v^0_z < v^0_h}| <= |U| + 1`; sharp form
   `n <= m - 2`, attained.
3. Lemma B.1 (dichotomy, every `rho`): at an update that is not last, either
   (I) an unraised element passes the lowest raised value above the linking
   unraised anchor `g`, or (IV) a raised non-anchor passes `g`, which lies
   above a raised anchor of that non-anchor's circuit.
4. Lemma B.2 (twins): every raised anchor `h` has a raised non-anchor `x` with
   `v_x = v_h` and `h in C(B*, x)`. Lemma B.3: for a fixed unraised anchor `g`
   and raised anchor `h2`, at most `2q - 2 <= 2k - 2` updates are of case (IV)
   with these two. Corollary B.4 (every `rho >= 1`):
   `n <= 1 + rho (m - rho - 1) + 2 (k - 1) rho (k - rho)`; the crossings of
   raised non-anchors with unraised anchors cost `O(k^3)` updates, not
   `O(k m)`.
5. Theorem A' (all raised anchors of each component share one value `T_K`):
   `n <= 1 + |{z in U : v^0_z < T^0_{K(z)}}|`.
6. Corollary A.3: stage 1 takes at most one update and stage 2 at most `m - 1`
   (attained at `k = 3`); for `k = 3` the whole schedule takes at most `m`.

**Conjectured** (Section 5; equality attained, no counterexample in 468
epochs and in hill climbing aimed at it at `k = 5, 6` and `rho >= 3`):
Conjecture P,
`n <= 1 + P1(v^0) <= m - rho` for every epoch with `rho >= 1`, where `P1` counts
the elements other than raised anchors below the top raised value of their
component (it does not depend on the choice of `B*`, Lemma P.0); Conjecture Q, a refinement (repeated designations plus case (IV)
updates are at most the raised non-anchors below the top raised value).

**Refuted** (Section 7): `n <= m - k + rho - 1`; charging only to non-anchors
or only through anchored pairs; greedy online charging; `P1` and a stronger
variant as strict potentials; the strengthening R5 of Conjecture P (updates
that pass nothing through the top raised value are at most the raised
non-anchors below it).

**Stages (data, Section 6).** The longest stages found exceed `m` by
`-1, 0, 4, 5, 6` at `k = 3, ..., 7`; each consists of one long `rho = 1` epoch
(at most `m - 2`, Theorem A) and short epochs.

**Consequences** (Section 6): proved `ell_1 = 1`,
`ell_r = (m - 1) + (r - 2) min(k m, floor(m^2/4) + 1)` and
`ell_r <= m r (r - 1)/2 + (r - 2)(1 + k^2 (k - 1)/2) - 1` for `r >= 2`; the
order `k^3 m` of Theorem C's schedule is unchanged (its constant drops from
`1/2` to about `1/6` when `m >> k^2`), and for `k = 3` the schedule takes at
most `m` updates. Under Conjecture P, `ell_r <= 1 + (r - 1) m - r (r - 1)/2`, about
`k^2 m / 2` update blocks in total and size `O(k^3 m^6 (s + m))` for
Theorem C.

## 0. Notation and standing facts

Stage `r`, an epoch with `S0 = S` fixed, states `v^0, ..., v^n` (`n` updates;
`v^n` is the first state after the epoch). `R = E_S`, `U = E - R`,
`rho = |S| - (k - r) = r_{M^v}(R)`. `B*` is a minimum base of `v^0` meeting `r`
blocks; by Theorem `thm:validity`(2) it is a minimum base meeting `r` blocks at
every state of the epoch, and `|B* cap R| = rho` (Step 1 of the proof of
Theorem `thm:stagelength`). Elements of `B*` are *anchors*; `B* cap R` are the
*raised anchors*. `K(e)` is the connected component of `e`. For one update
`v -> v'`: `delta` is the first event (Step 3 of the proof of
Theorem `thm:potential`), `tau >= delta` its length, and

    v'_x = v_x - tau   (x in R),
    v'_z = v_z - a_{blk z},  0 <= a_{blk z} <= tau - delta   (z in U),

so in the *R-frame* (values plus the total length of the updates so far) the
raised elements stand still and each unraised element `z` rises by
`Delta_z = tau - a_{blk z}`, with `delta <= Delta_z <= tau`.

`D(v) = min { v_y - v_g : y in R - B*, g in C(B*, y) - R }` (B0, Section 2.2).
We use from B0: Lemma 1.1 (windows: if `f in PO_t`, `f notin B*`, some
`b in C(B*, f) - f` has `v_f - t <= v_b <= v_f`), Theorem 2.2(1) (`D(v) > 0` at
every state of the epoch and `D(v^n) = 0`) and Theorem 2.2(2)
(`D(v') <= D(v) - delta`). An update is *last* if it is the `n`-th.

## 1. Two lemmas valid for every rho

**Lemma A.1.** For every update of the epoch except the last, `D(v) > delta`.

*Proof.* Step 1. The update is not last, so `v'` is a state of the epoch and
`D(v') > 0` by Theorem 2.2(1).
Step 2. By Theorem 2.2(2),

    0 < D(v') <= D(v) - delta.

**Lemma A.2 (raised windows).** At an update that is not last, let
`y in R - B*` with `y in PO_delta`. Then every `b in C(B*, y) - y` with
`v_b >= v_y - delta` lies in `B* cap R`, and at least one such `b` exists. In
particular `y` lies within `delta` above a raised anchor of `C(B*, y)`:

    v_y - delta <= v_b <= v_y   for some  b in B* cap R cap C(B*, y).

*Proof.* Step 1. By Lemma 1.1 some `b in C(B*, y) - y` has
`v_y - delta <= v_b <= v_y`; every `b in C(B*, y) - y` lies in `B*`.
Step 2. If such a `b` lies in `U`, then `(y, b)` is one of the pairs defining
`D`, and by Lemma A.1

    D(v) <= v_y - v_b <= delta < D(v),

a contradiction. So every such `b` lies in `B* cap R`.

## 2. Theorem A: epochs with rho = 1

**Theorem A.** Let an epoch have `rho = 1`, and let `B* cap R = {h}`. Then
every update of the epoch except the last makes some `z in U cap K(h)` pass
`h`:

    v_z < v_h   and   v'_z >= v'_h.

Consequently the epoch has at most

    1 + |{ z in U cap K(h) : v^0_z < v^0_h }|  <=  1 + |U|

updates. Since `R` contains `h` and some element of `R - B*`, this is at most
`m - 1`.

*Proof.* Fix an update `v -> v'` that is not last.

Step 1, the linking pair. By Step 5 of the proof of Theorem `thm:potential`,
applied to `B = B*` (which attains `|B* cap R| = r_{M^v}(R)`), there are
`y in R - B*` and `g in C(B*, y) cap U` in one cluster `C` at scale `delta`,
with `v_g < v_y` and `y in PO_delta` (as `u_delta(y) <= m`).

Step 2, `g` lies below `h`. By Lemma A.2 and `B* cap R = {h}`,
`h in C(B*, y)` and `v_h >= v_y - delta`. As `(y, g)` is one of the pairs
defining `D`, Lemma A.1 gives

    v_y - v_g >= D(v) > delta >= v_y - v_h,   so   v_g < v_h <= v_y.

Step 3, `h in C`. `h in B* subseteq PO_0 subseteq PO_delta` lies in the
component of `y` (`h in C(B*, y)`), and `v_g < v_h <= v_y`. The cluster `C` is
an interval of the sorted values of `PO_delta cap K(y)` containing `v_g` and
`v_y`, so `h in C`.

Step 4, the lowest raised element above `g`. Let `z2 in C cap R` have
`v_{z2} > v_g` least. By Step 3, `v_{z2} <= v_h`. If `z2 != h`, then
`z2 in (R - B*) cap PO_delta`, so Lemma A.2 gives `h in C(B*, z2)`, and the
minimality of `B*` (Lemma `lem:minbases`(1)) gives `v_h <= v_{z2}`. In both
cases

    v_{z2} = v_h.

Step 5, the highest unraised element below it. Let `z1 in C cap U` have
`v_{z1} < v_{z2}` largest (`g` qualifies). An element of `C` with value in
`(v_{z1}, v_{z2})` would lie in `U`, against the choice of `z1`, or in `R`,
against the choice of `z2` (its value exceeds `v_{z1} >= v_g`). So `z1`, `z2`
are consecutive in `C`, and

    0 < v_h - v_{z1} = v_{z2} - v_{z1} <= delta.

Step 6, the passage. `h` moves down by `tau` and `z1` by at most
`tau - delta`, so

    v'_h - v'_{z1} <= (v_h - tau) - (v_{z1} - (tau - delta))
                    = (v_h - v_{z1}) - delta <= 0,

and `z1 in C subseteq K(y) = K(h)`.

Step 7, counting. For every `z in U` and every update of the epoch,

    (v'_h - v'_z) = (v_h - v_z) - (tau - a_{blk z}) <= (v_h - v_z) - delta
                  < v_h - v_z,

so `v_h - v_z` strictly decreases along the epoch, and `z` passes `h` at most
once, and only if `v^0_z < v^0_h`. By Steps 1 to 6 every update but the last
has such a passage, and distinct updates have distinct passing elements
`z1`. Hence `n - 1 <= |{z in U cap K(h) : v^0_z < v^0_h}|`.

Step 8, the last bound. `R` contains `h` and the element `y in R - B*` of
Step 1, so `|U| <= m - 2`.

**Theorem A, sharp form.** With `rho = 1`, `n <= m - 2`.

*Proof.* Step 1. If `|R| >= 3`, Theorem A gives `n <= 1 + |U| <= m - 2`.
Step 2. Let `|R| = 2`. By Lemma B.2 (Section 3) `h` has a twin `x`, so
`R = {h, x}`, and every pair defining `D` is `(x, g)` with
`g in C(B*, x) cap U`; such a `g` exists (B0, Section 2.2: otherwise
`r_M(R) <= rho < |S|` and `M` has no rainbow base), lies in `K(h)` (it shares
the circuit `C(B*, x)` with `h`) and has `v^0_g <= v^0_x - D(v^0) < v^0_h`.
Step 3. If an update passes such a `g` through `h`, then

    D(v') <= v'_x - v'_g = v'_h - v'_g <= 0,

so the update is last. Hence the passing elements `z1` of the updates that are
not last avoid `C(B*, x) cap U`, which is nonempty and below `h`, and Step 7
gives `n - 1 <= |{z in U cap K(h) : v^0_z < v^0_h}| - 1 <= |U| - 1 = m - 3`.

The bound `m - 2` is attained: the searches of Section 7 found `rho = 1`
epochs with `n = m - 2` at `m = 9, 12, 14, 15` (with `|R| = 2` and
`n = |U|`, and at `m = 12` also with `|R| = 3` and `n = |U| + 1`).

*Checks* (`experiments/ep_sharpA.py`): on the 282 epochs with `rho = 1` of the
B0 logs (103), this note's logs (11) and 600 random instances (168), `n <= m - 2`
and, when `|R| = 2` (97 epochs), `n <= |{z in U cap K(h) : v^0_z < v^0_h}|`;
the false variant `n <= m - 3` fails on 61 of them.

*Hypotheses used:* for Theorem A, PO-SL (B0's Lemma 1.1, the cluster
structure of Definition `def:posl`), Theorem `thm:validity`(2) (to fix `B*`),
Theorem 2.2(1),(2) of B0, Step 5 of the proof of Theorem `thm:potential`, Lemma
`lem:minbases`(1); nothing about `k` or about other components. The sharp form
also uses Lemma B.2 (symmetric basis exchange) and the existence of a rainbow
base.

*Checks.* `experiments/ep_verify_rho1.py L` checks, at every state of the zoo
with `nu0 = r < k` and `v in {0..L}^E`, for every `B*`, the per-update statement
(T1: if `D(v') > 0` and `rho = 1`, some `z in U cap K(h)` passes `h`) and
Lemmas A.1 (T2) and A.2 (T3), together with three false variants: F1 (the
passing `z` can be taken outside `B*`), F2 (T1 also at the last update), F3
(T1 for `rho = 2`; the zoo has no state with `rho = 2`, as `k <= 3` there).
Run at `L = 3` (log `ep_logs/verify_rho1_L3.txt`; the 13 matroids of the
referee zoo, every block assignment, 85,725 states with `rho >= 1`): T1, T2, T3
hold at all 12,422 pairs (state, `B*`) with `rho = 1` and `D(v') > 0` (MK4,
W3, K4minus+par, C4+chord par); F1 fails at 7,008 of them and F2 at 48,396 of
191,950 last updates. So the checks discriminate.

*Data.* All epochs with `rho = 1` of the B0 logs and of this note's searches
satisfy Theorem A; the best ones found have `n = m - 2` (Section 7). The `+1` in the first bound is needed: the false
variant `n <= |{z in U cap K(h) : v^0_z < v^0_h}|` fails on 26 epochs
(`ep_check_random.py`, Section 3), all with `|R| >= 3`.

**Formal statement (for Lean).** Data: a matroid `M` of rank `k` on
`E = {0, ..., m-1}` with a rainbow base, blocks `blk : E -> [k]`, `r < k`, and
states `v^0, ..., v^n in R^E` with `v^i = v^{i-1} - (a^i)_blk`, where `a^i` is
the PO-SL update of Definition `def:update` at `v^{i-1}` for stage `r`.
Hypotheses: `nu(M^{v^i}) = r` and `Av(M^{v^i}) = S` for `0 <= i < n`, and
`nu(M^{v^n}) > r` or `Av(M^{v^n}) != S` (an epoch); `|S| - (k - r) = 1`;
`B*` a base of `M^{v^0}` meeting exactly `r` blocks; `h` the element of
`B* cap E_S`. Conclusions:

    n <= 1 + |{ z notin E_S : z in the component of h, v^0_z < v^0_h }|,
    n <= m - 2.

Lemmas to formalize first: B0 Lemma 1.1 (windows), B0 Theorem 2.2(1),(2)
(`D > 0` on the epoch, `D(v^n) = 0`, `D(v^i) <= D(v^{i-1}) - delta_i`), Step 5
of the proof of Theorem `thm:potential` as a stand-alone lemma (the linking
pair `(y, g)` in one `delta`-cluster with `y in PO_delta`), the interval
property of PO-SL clusters, and, for the second conclusion, Lemma B.2 (needs
the symmetric basis exchange property).

## 3. Structure of the updates for rho >= 2

**Lemma B.1 (dichotomy).** At every update of an epoch that is not last, let
`(y, g)`, the cluster `C` at scale `delta`, `z2` and `z1` be as in Steps 1, 4,
5 of the proof of Theorem A (`z2` the lowest raised element of `C` above `g`,
`z1` the highest unraised element of `C` below `z2`). Then one of the
following holds.
- (I) Some raised anchor `h` has `v_h = v_{z2}`, and `z1` passes it:
  `0 < v_h - v_{z1} <= delta` and `v'_h <= v'_{z1}`.
- (IV) `z2 notin B*`, some raised anchor `h2 in C(B*, z2)` has
  `v_{z2} - delta <= v_{h2} <= v_g`, and `z2` passes `g`:
  `0 < v_{z2} - v_g <= delta` and `v'_{z2} <= v'_g`.

Moreover `y` has a raised anchor `h° in C(B*, y)` with
`v_y - delta <= v_{h°} <= v_y`, and `v_g < v_{h°}`.

*Proof.* Step 1. Steps 1 to 3 of the proof of Theorem A use only Lemmas A.1
and A.2, and give `h°` (the `h` there) with `v_g < v_{h°} <= v_y`, `h° in C`.
So `z2` exists and `v_{z2} <= v_{h°}`.
Step 2. If `z2 in B*`, (I) holds with `h = z2` by Steps 5 and 6 of the proof
of Theorem A.
Step 3. Let `z2 notin B*`. By Lemma A.2 some raised anchor
`h2 in C(B*, z2)` has `v_{z2} - delta <= v_{h2} <= v_{z2}`. If `v_{h2} > v_g`,
then `h2 in C` (it is in `PO_delta`, in the component of `z2`, with value in
`(v_g, v_{z2}]`), and the choice of `z2` gives `v_{h2} = v_{z2}`: (I) holds
with `h = h2` by Steps 5 and 6 of the proof of Theorem A.
Step 4. Otherwise `v_{h2} <= v_g`, so `0 < v_{z2} - v_g <= v_{z2} - v_{h2} <=
delta`; `z2` moves down by `tau` and `g` by at most `tau - delta`, so
`v'_{z2} - v'_g <= (v_{z2} - v_g) - delta <= 0`.

For `rho = 1` case (IV) is impossible (`h2 = h° = h` would give
`v_h <= v_g < v_h`), which is Theorem A.

*Checks.* `experiments/ep_check_random.py` follows whole schedules and checks
Lemmas A.1, A.2 and B.1 at every update that is not last: on the 122 instances
of the B0 logs (810 such updates: 798 in case I, 12 in case IV), the 9 best
instances of the `n - m` searches (96 updates, all case I), and 194 further
updates (structured search, `k = 7` stage search, 600 random instances with
`k <= 7`), no failure; Theorem A held on all 112 `rho = 1` epochs of the logs,
and its false variant without the `+1` failed on 26 of them.

**Lemma B.3 (mirror ladders are short).** Fix an unraised anchor `g` and a
raised anchor `h2`. The updates of case (IV) of Lemma B.1 in which `g` is the
linking anchor and `h2` the raised anchor of `C(B*, z2)` below `g` are at most
`2q - 2` in number, where `q` is the largest number of distinct values of `B*`
in a component (B0, Section 1) at the state before the first of them; in
particular at most `2k - 2`.

*Proof.* Let `i_1 < ... < i_L` be these updates, `w_l` the element `z2` at
`i_l`, and `delta_l`, `D_l` the first event and the value of `D` at the state
before `i_l`.
Step 1. By Lemma B.1(IV), `v_{h2} <= v_g < v_{w_l} <= v_{h2} + delta_l` at
`i_l`, and `g` rises by at least `delta_l` in the R-frame while `h2` stands
still, so after `i_l` and at every later state `v_g - v_{h2} >= delta_l`.
Step 2. At `i_{l+1}`, `w_{l+1}` lies above `g`, so

    delta_{l+1} >= v_{w_{l+1}} - v_{h2} > v_g - v_{h2} >= delta_l.

Step 3. `D` decreases by at least the first event at every update (B0,
Theorem 2.2(2)), so by Step 2
`D_L <= D_1 - (delta_1 + ... + delta_{L-1}) <= D_1 - (L - 1) delta_1`.
Step 4. By B0, Theorem 2.2(3), `D_1 <= (2q - 1) delta_1`, and by Lemma A.1
and Step 2, `D_L > delta_L > delta_1` if `L >= 2`. Hence

    delta_1 < D_L <= (2q - 1) delta_1 - (L - 1) delta_1,   so   L < 2q - 1.

So a run in which one unraised anchor passes the raised non-anchors of one
raised window one per update (the mechanism of B0's counterexample to
Conjecture 2.7) has at most `2q - 2` updates.

**Corollary B.4 (every rho).** Let `s` be the largest number of distinct
values of raised anchors in one component (`s <= rho`), and `q <= k` the
largest number of distinct values of `B*` in one component over the states of
the epoch. Every epoch with `rho >= 1` has

    n <= 1 + sum_{z in U} |{ values v^0_h of raised anchors h in K(z) : v^0_h > v^0_z }|
           + (2q - 2) rho (k - rho)
      <= 1 + rho (m - rho - 1) + 2 (k - 1) rho (k - rho).

*Proof.* Step 1, case (I). A case (I) update makes its `z1` pass the value
`v_h` of a raised anchor of `K(z1)`; raised values stand still in the R-frame
and `z1` rises by at least `delta > 0`, so each pair (unraised element, raised
value of its component) occurs at most once, and only if the value is above
the element at the first state. So the case (I) updates number at most the
sum in the first line.
Step 2, case (IV). Assign to each case (IV) update its linking anchor `g` and
one raised anchor `h2` as in Lemma B.1(IV), so `v_{h2} <= v_g`; there are at
most `rho (k - rho)` such pairs, and the updates assigned to one pair are at
most `2q - 2` (Lemma B.3, whose proof uses only the chosen `h2`).
Step 3, the last update adds 1. For the second line, the sum is at most
`s |U| <= rho |U|`, and `|U| <= m - rho - 1` because `R` contains the `rho`
raised anchors and at least one twin (Lemma B.2).

So the pairs (raised non-anchor, unraised anchor) of B0's Theorem 2.4, which
contribute `(k_K - rho_K) |R cap K|` there, contribute at most
`2 (k - 1) rho (k - rho)` updates, independently of `m`. *Checks*
(`ep_corB4.py`): on the 468 epochs with `rho >= 1` of the B0 logs, 400 random
instances and this note's logs, both the total and the case (I) count stay
within their bounds; the false variant `#(case I) <= |U|` (the `rho = 1` count
for every `rho`) fails on 30 of them.

**Lemma B.2 (twins).** At every state of the epoch, every raised anchor `h`
has a *twin*: some `x in R - B*` with `blk(x) != blk(h)`, `v_x = v_h` and
`h in C(B*, x)`.

*Proof.* Step 1, an exchange at the first state. At `v^0`,
`blk(h) in S0 = Av(M^{v^0})`, so some base `B'` of `M^{v^0}` meeting exactly
`r` blocks misses `blk(h)`; then `h in B* - B'`. By the symmetric exchange
property of the matroid `M^{v^0}`, some `x in B' - B*` makes both
`B* - h + x` and `B' - x + h` bases of `M^{v^0}`.
Step 2, `x` is raised. A base of `M^{v^0}` meeting `j` blocks contains a
rainbow independent set of size `j`, so it meets at most `nu(M^{v^0}) = r`
blocks. Since `B'` misses `blk(h)`, the set `blk(B' - x + h)` contains
`blk(B') - {blk(x)}` and `blk(h)`, so

    r >= |blk(B' - x + h)| >= (r - 1) + 1 = r.

If `B' - x` still met `blk(x)`, then `blk(B' - x + h)` would contain
`blk(B') + blk(h)`, of size `r + 1 > r`. So `x` is the only element of `B'` in
its block, and `B' - x + h` is a minimum base meeting exactly `r` blocks that
misses `blk(x)`; hence `blk(x) in Av(M^{v^0}) = S0` and `x in R`. Also
`blk(x) != blk(h)` (as `blk(x) in blk(B')`) and `x notin B*`.
Step 3, the tie. `B* - h + x` is a minimum base of `v^0`, so by Lemma
`lem:minbases`(3), `h in C(B*, x)` and `v^0_x = v^0_h`.
Step 4, persistence. `C(B*, x)` does not depend on the weights, and `x`, `h`
both move down by `tau` at every update of the epoch.

*Consequence.* In case (I) of Lemma B.1, `z1` also passes a twin `x` of `h`:
`x in R - B*` lies in the component of `h` and `v_x = v_h`. So every update
that is not last makes some unraised element pass some element of `R - B*`
(the twin in case (I), `z2` in case (IV)).

*Checks* (`ep_twins.py`). In the 224 epochs with `rho >= 1` of the B0 logs and
of this note's search logs, all 370 raised anchors (at the first state) have a
twin.

## 4. Consequences for stages 1 and 2

A stage has at most one epoch for each value of `rho` in `{0, ..., r - 1}`
(B0, Section 1). The epoch with `rho = 0` takes one update (B0, Theorem 2.1)
and the epoch with `rho = 1` at most `m - 2` (Theorem A, sharp form). Hence:

**Corollary A.3.** Stage 1 takes at most one update and stage 2 at most
`m - 1` updates, for every matroid, block partition and weights. For `k = 3`
the PO-SL schedule takes at most `m` updates in total. The bound `m - 1` on
stage 2 is attained, so the bound `m` for `k = 3` is attained up to one
(below); the halving ladder (paper, Proposition `prop:ladder`) has a stage 2 of
`m - 3`.

*Proof.* Stage 2 has epochs with `rho in {0, 1}` only:
`1 + (m - 2) = m - 1` (B0, Theorem 2.1, and Theorem A, sharp form). For
`k = 3` the stages are `r = 1, 2`.

*Tightness.* `m - 1` is attained: B0's searched instances with `k = 3`
include stage 2 of `m - 1` updates, an epoch with `rho = 0` (1 update) followed
by an epoch with `rho = 1`, `|R| = 2` and `n = |U| = m - 2`: binary, columns
`[4,3,3,7,7,7,1,4,2]`, blocks `[1,1,1,1,1,1,2,1,0]`, weights
`[7878,418,737,2066,3449,65057,526012,3715,1048576]` (`m = 9`, stage lengths
`[0, 8]`); graphic, edges `21,23,12,10,31,20,02,21`, blocks
`[1,0,1,1,2,1,1,1]`, weights `[6143,188686,3799,94734,421930,1120,1457,54]`
(`m = 8`, `[0, 7]`); graphic, edges `23,01,30,30,01,02,03,31,03,10,13`,
blocks `[0,2,2,2,2,1,2,2,2,2,2]`, weights
`[242944,652,16002,2,121,151842,65,38028,75922,8135,356]` (`m = 11`,
`[0, 10]`). So for `k = 3` the PO-SL schedule takes at most `m` updates and can
take `m - 1`. Over the 140 instances of all logs, stage 1 never took more than
one update, and stage 2 never more than `m - 1`.

## 5. One raised value per component, and the general conjecture

**Theorem A'.** Suppose that in every component `K` all raised anchors of `K`
have the same value `T_K` (at the first state, hence at every state: raised
elements move together). Then every update of the epoch except the last makes
some `z in U` pass `T_{K(z)}` (`v_z < T_{K(z)}`, `v'_z >= T'_{K(z)}`), and

    n <= 1 + |{ z in U : K(z) has a raised anchor, v^0_z < T^0_{K(z)} }|.

This contains Theorem A (`rho = 1`) and every epoch whose raised anchors lie in
distinct components or share their value. Since `R` contains the `rho` raised
anchors and at least one twin (Lemma B.2), it gives `n <= 1 + |U| <= m - rho`,
the consequence of Conjecture P below, in this case.

*Proof.* Step 1. In case (IV) of Lemma B.1, `h2` and `h°` lie in the component
of `C` (`h2 in C(B*, z2)`, `h° in C(B*, y)`, `z2, y in C`) and

    v_{h2} <= v_g < v_{h°},

so they have different values; this is excluded. So every update but the last
is in case (I): `z1 in U cap K` passes a raised anchor of `K`, of value `T_K`.
Step 2. `T_K - v_z` strictly decreases at every update (`T_K` moves by `tau`,
`z` by at most `tau - delta`), so each `z` passes `T_{K(z)}` at most once, and
only if it starts below it. The map from updates that are not last to the
passing `z1` is injective.

*Checks* (`ep_thmA2.py`): on the 380 epochs with `rho >= 1` to which Theorem A'
applies (99 of them with `rho >= 2`) among the B0 logs, this note's logs and 500
random instances, the bound holds; the false variant without the `+1` fails on
102 of them.

**Conjecture P.** For every epoch with `rho >= 1`, with `T_K` the largest value
of a raised anchor of `K`,

    n <= 1 + P1(v^0),
    P1(v) = |{ e in E - (R cap B*) : K(e) has a raised anchor, v_e < T_{K(e)} }|.

Since the twin of a raised anchor of value `T_K` (Lemma B.2) is not counted,
`P1 <= |U| + |R - B*| - 1`, so Conjecture P gives `n <= |U| + |R - B*| = m - rho`.
(`P1` is defined through `B*`; the conjecture is stated for every choice of
`B*`. The tests use the base built by `stage_epoch_check.base_meeting_r`; in
addition `ep_P1_allB.py` computes `P1` for every minimum base meeting `r`
blocks on the 238 epochs with `rho >= 1` of all logs: `P1` never depended on
the choice (as Lemma P.0 below shows it cannot), and `n <= 1 + P1` held.)

**Lemma P.0 (`P1` does not depend on `B*`).** The multiset
`{(K(h), v^0_h) : h in B* cap R}` is the same for every minimum base `B*` of
`v^0` meeting `r` blocks; hence so are the values `T_K` and `P1(v^0)`.

*Proof.* Step 1. `B* cap R` is independent in `M^{v^0}` and has
`rho = r_{M^{v^0}}(R)` elements, so it is a basis of `M^{v^0} | R`.
Step 2. `M^{v^0}` is the direct sum, over the values `l`, of the matroids
`(M | {v <= l}) / {v < l}` on `{v = l}` (paper, after Lemma `lem:minbases`). A
circuit of a contraction `N / X` has the form `C - X` for a circuit `C` of `N`,
so every circuit of `M^{v^0}` lies in one value class and inside one circuit of
`M`, hence in one component of `M`.
Step 3. Any two bases of the matroid `M^{v^0} | R` are joined by single
exchanges `B -> B - x + x'` with `x` in the `M^{v^0}`-circuit of `x'` in
`B + x'`; by Step 2, `x` and `x'` have the same value and the same component,
so each exchange preserves the multiset.
Step 4. `T_K` is the largest value of the multiset in `K`, and
`P1 = |{e : K(e) has a raised anchor, v_e < T_{K(e)}}| -
|{h in B* cap R : v_h < T_{K(h)}}|` is read from the multiset and from `v^0`.

*Evidence.* `experiments/ep_potential.py` (potential `P1`, raised values read
in the current state): on the 208 epochs with `rho >= 1` of the B0 logs, the 72
of this note's logs (all searches, including those aimed at Conjecture P) and
the 188 epochs with `rho >= 1` of 400 random instances (468 epochs),
`n <= 1 + P1(v^0)` always holds, with equality attained (the maximum of
`n - 1 - P1(v^0)` is `0`). `P1` itself is not a potential in the strict sense:
it fails to decrease at 15 of the 1,213 updates that are not last (3 in case
(IV), 12 in case (I), classified by `ep_pfail_case.py`). In the
example below the unraised elements pass a
raised non-anchor `x` already passed earlier by unraised elements that have
since risen above `T_K` (the B0 instance
`13,31,20,20,03,13,42,21,42,04` / `[0,1,2,2,1,1,2,3,2,2]` /
`[335362,233742,26,3789,313619,273680,811,1048576,83842,120224]`, stage 3,
epoch `S0 = {0,1,3}`, update 4: 2, 3, 6 pass 5, which 8 and 9 passed at update
2; update 2 lowered `P1` by 3). For `rho = 1` Theorem A is stronger than
Conjecture P (it does not count raised non-anchors).

**Why `rho >= 2` is harder: reuse.** For `rho >= 2` an unraised element can be
the passing element `z1` of case (I) at several raised values: on the 105
epochs with `rho >= 2` of the B0 logs (`experiments/ep_cases2.py`), 42 of 179
case (I) updates designate an element designated before, at a lower raised
value. Example (B0 logs; graphic, edges
`01,40,24,02,41,03,45,30,03,01,35`, blocks `[0,1,1,0,1,4,3,3,3,0,2]`, weights
`[2172,15,3437,1011,54,40002,24996,14221,20361,606,41723]`, stage 4, epoch
`S0 = {2,3,4}`, `rho = 2`, `n = 8`, `m = 11`): raised anchors 5 (twin 7) and 6
(twin 10) at R-frame values 12491 < 23266, raised non-anchor 8 at 18631; the
designated pairs are `(5,2), (5,0), (6,2), (6,0), (6,3), (6,9), (6,4)` and a
last update. Elements 2 and 0 pass the lower anchor 5 one at a time, then the
upper anchor 6 one at a time; the extra updates are paid, in the count of
Conjecture P, by the raised non-anchors 7 and 8 below 23266. A rigorous version
of this payment is the missing step; the natural potentials fail at re-passages
(above).

**Conjecture Q (refines P).** In an epoch with `rho >= 1`, call a case (I)
update a *repeat* if its passing element `z1` was the passing element of an
earlier case (I) update of the epoch. Then

    #repeats + #(case (IV) updates)  <=  |{ x in R - B* : v^0_x < T^0_{K(x)} }|.

Since the first designations are distinct elements of `U` below `T`, Q implies
P: `n - 1 = #first + #repeats + #IV <= P1(v^0)`.

*Evidence* (`experiments/ep_conjQ.py`, the passing element chosen as in
`ep_cases2.classify`): 468 epochs (B0 logs 208, random 188, this note's logs
72), no failure. Equality holds in 105 of the 140 epochs with `rho = 2` and in
11 of the 67 with `rho >= 3`. In every `rho = 2` epoch printed by the
instrumentation (12 epochs with repeats or case (IV), B0 logs) the two raised
values `a < T` are passed in two phases (first `a`, then `T`), each case (IV)
update passes a raised non-anchor of the window of `a`, and the repeats plus
case (IV) updates number exactly the raised non-anchors in `[a, T)`: the twin
of `a` and the window elements. In the three traced examples equality
holds level by level: the repeats and case (IV) updates charged to the raised
non-anchors lying between a raised value and the next one (twins and window
elements), e.g. in the `rho = 2`, `m = 11` example of Section 5 the two repeats
`(6,2), (6,0)` against the raised non-anchors 7 (twin of 5) and 8.

## 6. Consequences for the stage length and for Theorem C

Notation of the paper: Theorem C runs stage `r` for `ell_r` updates. B0 and the
paper use `ell_r = min(r (floor(m^2/4) + 1), 1 + (r - 1) k m)`.

**Proved here.** A stage has at most one epoch for each `rho in {0, ..., r-1}`;
`rho = 0` takes one update (B0, Theorem 2.1), `rho = 1` at most `m - 2`
(Theorem A, sharp form), `rho >= 2` at most `min(k m, floor(m^2/4) + 1)`
(Theorem `thm:stagelength`, Step 5, and Theorem `thm:potential`, Step 8, which
bounds each value of `S0`).
Hence one may take

    ell_1 = 1,   ell_r = (m - 1) + (r - 2) min(k m, floor(m^2/4) + 1)   (r >= 2),

in particular `ell_2 = m - 1`. Corollary B.4 gives another bound for the
epochs with `rho >= 2`, `1 + rho m + k^2 (k - 1)/2` (as
`rho (k - rho) <= k^2/4`), hence

    ell_r <= m r (r - 1)/2 + (r - 2)(1 + k^2 (k - 1)/2) - 1   (r >= 2),

and in total about `k^3 m / 6 + k^5 / 4` updates instead of `k^3 m / 2`, which
is smaller when `m >= k^2` (the ratio tends to 3 when `m >> k^2`). Below we
use the branch `k m`:

    ell_1 = 1,   ell_2 = m - 1,   ell_r = (m - 1) + (r - 2) k m   (r >= 2),

and the schedule has at most

    sum_{r=1}^{k-1} ell_r = 1 + (k - 2)(m - 1) + k m (k - 2)(k - 3) / 2

updates, against `(k - 1) + k m (k - 1)(k - 2)/2` from `1 + (r-1) k m`. The
saving is `(k - 2)(k m - m + 2)`, about `k^2 m`; the order `k^3 m / 2` is
unchanged. For `k = 3` the whole schedule takes at most `m` updates
(Corollary A.3); B0's instances with a stage 2 of `m - 1` updates show this is
tight up to `+1` (the halving ladder takes `m - 3`).

**Across the epochs of a stage (data).** In the eight longest stages of the
B0 logs (`stage_logs/exp_*.txt`, stage minus `m` from 3 to 5, `k = 5, 6`) the
epochs, listed as `(rho, n, P1(v^0))`, are dominated by the `rho = 1` epoch:
e.g. `m = 12`, `k = 6`, `r = 5`: `(0,1,0), (1,10,10), (2,1,0), (3,3,5),
(4,2,2)` (17 updates), and `m = 13`, `k = 5`, `r = 4`: `(0,1,0), (1,11,11),
(2,1,0), (3,4,5)` (17 updates). So in these stages one epoch is long (at most
`m - 2`, Theorem A) and the others take a few updates each; the stage lengths
`m + 4`, `m + 5` of B0 come from `r - 1` short epochs added to one long one.
Whether several epochs of one stage can each be of order `m` is open; no
cross-epoch potential was found (`P1` is not monotone from one epoch to the
next: `0, 10, 0, 5, 2` above).

B0's `stage_search_exp.py` at `k = 7` (graphic, 8 vertices, `m = 14`, 5 workers
x 1200 s, log `ep_logs/stage_excess_graphic_8_14.txt`) found a stage of
`m + 6 = 20` updates (graphic, edges `75,24,64,36,53,14,64,46,65,13,21,47,70,04`,
blocks `[6,5,0,3,1,4,1,4,1,4,2,1,6,3]`, weights
`[430261,4251475,2240075,19124,153712,3840,2342092,1171454,102834,307393,
16777218,46321,200643,256338]`, stage 6), with epochs `(rho, n, P1)`:
`(0,1,0), (1,11,12), (3,5,6), (4,1,1), (5,2,4)`. The longest stage minus `m`
found so far is `-1, 0, 4, 5, 6` at `k = 3, ..., 7`: again one long `rho = 1`
epoch and short ones, all within Theorem A and Conjecture P.

**Under Conjecture P** (`n <= m - rho` for every epoch with `rho >= 1`):

    ell_r <= 1 + sum_{rho=1}^{r-1} (m - rho) = 1 + (r - 1) m - r (r - 1)/2,
    sum_{r=1}^{k-1} ell_r <= (k - 1) + m (k - 1)(k - 2)/2 - (k - 2)(k - 1) k / 6,

about `k^2 m / 2` update blocks, a factor `k` below the proved bound; the size
of Theorem C would become `O(k^3 m^6 (s + m))`.

## 7. Refuted statements and searches

**R1. "n <= m - k + rho - 1".** Refuted within 20 s of hill climbing
(`ep_search.py graphic 5 9 20 2 m-k+rho-1`): graphic, edges
`13,13,34,20,21,13,42,01,21`, blocks `[0,1,1,2,1,0,0,3,1]`, weights
`[140624,49368,34576,579690,32980,37332,34568,579690,295920]` (`k = 4`,
`m = 9`), stage 3 has an epoch with `rho = 1`, `|U| = 7`, `|R| = 2` of 7
updates (a pure ladder: the raised anchor 3 passes 8, 0, 1, 5, 2, 6, 4 one per
update), while `m - k + rho - 1 = 5`.

**R2. Charging each update to the non-anchor of an anchored crossing pair
(scheme N), or to a non-raised-anchor element of an anchored pair (F_anch).**
Fails (no injective charge exists): graphic, edges
`43,24,45,05,21,04,12,21,45,03,15`, blocks `[4,2,4,3,1,4,2,0,4,3,0]`, weights
`[18,10530,2,23,15770,64,8583,4308,7,880,6446]`, stage 4, epoch
`S0 = {0,1,2}`, `rho = 2`: updates 1 and 3 have the single anchored crossing
pairs `(4,9)` and `(1,9)`. Charging to any element of any crossing pair (scheme
F, `ep_charge2.py`) or of any anchored pair (scheme E, `ep_charge.py`) has a
system of distinct representatives on all 354 epochs of the B0 logs.

**R3. Greedy online charging** (priority unraised non-anchor, raised
non-anchor, raised anchor, unraised anchor; or designated pair first) fails on
2 and 5 of the 354 epochs (`ep_instr.py`).

**R4. Strict potentials.** `P1` fails to decrease at 15 of 1,213 updates
(Section 5); `P1 +` #(raised non-anchors below `T` with an unraised anchor still
below them) fails at 8 (`ep_potential.py`, mode 4; e.g. graphic `13,43,40,34,10,13,
24,42,23,10`, blocks `[3,1,0,1,0,2,1,1,1,3]`, weights `[57302,365,210758,9121,
210695,256960,14357,3887,489,60190]`, stage 3, update 3: element 7 passes the
lower raised value 57302 (anchor 0, twin 5) already passed by 6 and 3).

**R5. "The updates in which no unraised element passes the top raised value
are at most the raised non-anchors below it"** (a natural strengthening of
Conjecture P, since each other update passes some element through the top
value; `ep_Pprime.py`). Fails on 3 of the 468 epochs tested, by one each:
the instance of R4, stage 3 (updates 1 and 3 pass nothing through the top
value 60190, and only the twin 5 lies below it); binary, columns
`[15,11,24,9,20,10,7,11,31]`, blocks `[0,4,2,2,1,4,3,4,4]`, weights
`[3306,3,29,237,1977,10,2,11,1348]`, stage 4; and graphic, edges
`27,73,27,43,73,03,05,05,73,16,75,15,47,75,41`, blocks
`[3,0,6,0,2,4,4,3,2,2,4,1,0,5,2]`, weights `[40151,74772,2,11716,2842,149686,
149675,687206,0,34440,149544,45580,18471,346442,173226]`, stage 6, `rho = 3`
(from the `rho >= 3` search). Conjecture P holds on all three: the count must
mix the two kinds of updates.

**Searches** (hill climbing with midpoint and doubling moves, integer weights
up to `2^26`, logs in `experiments/ep_logs/`):

| script, objective | instances | workers x s | best |
|---|---|---|---|
| `ep_search.py`, `n - m` | graphic 6 vertices, `m = 12` | 3 x 1500 | `n = 10 = m - 2`, `rho = 1` |
| same | graphic 7, `m = 14` | 3 x 1500 | `n = 12 = m - 2`, `rho = 1` |
| same | graphic 8, `m = 15` | 3 x 1500 | `n = 13 = m - 2`, `rho = 1` |
| `ep_search.py`, `n - m` over `rho >= 2` | graphic 6, `m = 12` | 4 x 1500 | `n = 9 = m - 3`, `rho = 2` |
| `ep_struct.py`, `n - m` over `rho >= 2` | trees + parallel copies + 3 chords, 7 vertices, `m = 14` | 5 x 1200 | `n = 11 = m - 3`, `rho = 2` |
| `ep_search.py`, `n - (1 + P1)` over `rho >= 2` (against Conjecture P) | graphic 6, `m = 12` | 4 x 1200 | `n - (1 + P1) = 0` at best (e.g. `n = 9`, `P1 = 8`, `rho = 2`); never positive |
| same | graphic 7, `m = 14` | 4 x 1200 | `n - (1 + P1) = 0` at best (e.g. `n = 11 = m - 3`, `P1 = 10`, `rho = 2`); never positive |
| `ep_struct.py`, `n - (1 + P1)` over `rho >= 3` | trees + parallel copies + 3 chords, 8 vertices, `m = 15` | 5 x 1200 | `n - (1 + P1) = 0` at best (e.g. `n = 10`, `rho = 3`); never positive |

Every best `rho = 1` epoch has `n = m - 2` (the sharp form of Theorem A):
either `|R| = 2` and `n = |U|` (pure ladders: at each update one unraised
element passes the raised anchor), or `|R| = 3` and `n = |U| + 1` (graphic
`6/12` log, first entry: `|U| = 9`).
The best `rho = 2` epochs have `n = m - 3 = m - rho - 1`, `|R| in {3, 4}`; on
the instances of the structured search, Lemmas A.1, A.2, B.1, Theorem A and
Conjectures P and Q hold (50 updates that are not last, 8 epochs).

**Cross-check with the referee implementation** (`ep_referee.py`,
`referee_phase2a/core.py`: rank tables, base enumeration, a scan of all
breakpoints): the epoch decomposition (stage, `S0`, number of updates) of the
nine instances cited in this note (R1, R2, the three tight instances of
Corollary A.3, the reuse example of Section 5, the `P1` failure example, the
instance with `n = 1 + P1(v^0)` from the search against Conjecture P, and the
`k = 7` stage of `m + 6` updates) agrees exactly with `stage_core.py`.

## 8. Observed, not proved

1. Every epoch found satisfies `n <= m - 2`; with `rho >= 2`, `n <= m - rho - 1`
   (all searches here and in B0). Both follow from Conjecture P except for the
   last `-1`.
2. Conjectures P and Q hold with equality on many epochs (Sections 5, 7).
3. The active raised value (the value of `h` in case (I), of `h2` in case (IV))
   is non-decreasing in the R-frame along all 216 epochs with `rho >= 2` of the
   B0 logs, this note's search logs and 400 random instances (`k = 4..6`). So
   an epoch splits into phases, one per raised value, the last one at the top.
4. No raised non-anchor was the `z2` of two case (IV) updates of one epoch
   (12 case (IV) updates in those 216 epochs; small sample).
5. Twins (Lemma B.2) also exist at every state in the data, as the lemma says.

## 9. Scripts (all in `experiments/`, exact integer arithmetic)

| script | what it does |
|---|---|
| `ep_common.py` | epochs of the schedule from `p = 0` with `B*` fixed, crossing pairs, candidate bounds (`BOUNDS`), `P1` |
| `ep_trace.py`, `ep_trace_one.py` | update-by-update trace of the epochs of an instance in the R-frame |
| `ep_search.py` | hill climbing for long epochs against a bound (`m`, `m-k+rho-1`, `m|rho>=2`, `P1+1|rho>=2`, ...) |
| `ep_struct.py` | the same on trees with parallel copies and chords |
| `ep_hub.py` | weight-only hill climbing on a hub design with several raised anchors |
| `ep_charge.py`, `ep_charge2.py` | Hall's condition for charging schemes E, N, Z, X and F |
| `ep_instr.py` | rigid/non-rigid updates, cases of Theorem 2.4, greedy charging rules |
| `ep_bounds_scan.py` | maxima of `n -` bound over logged epochs |
| `ep_verify_rho1.py` | exhaustive zoo check of Theorem A (T1), Lemmas A.1 (T2), A.2 (T3), false variants F1, F2 |
| `ep_check_random.py` | Lemmas A.1, A.2, B.1 and Theorem A along whole schedules (random or logged instances) |
| `ep_cases2.py` | case (I)/(IV) sequence and repeats for `rho >= 2` |
| `ep_potential.py` | candidate potentials `P1`, `P2`, `P3`, mode 4 |
| `ep_conjQ.py` | Conjecture Q (and equality statistics) |
| `ep_sharpA.py` | sharp form of Theorem A, false variant `m - 3` |
| `ep_repeats.py` | designations, repeats and raised non-anchors passed, per epoch with `rho >= 2` |
| `ep_mono.py` | monotonicity of the active raised value; repeated case (IV) |
| `ep_pfail_case.py` | the case (I or IV) of each update where `P1` fails to decrease |
| `ep_twins.py` | twins of the raised anchors (Lemma B.2) on logged epochs |
| `ep_referee.py` | epoch decompositions of the cited instances, `stage_core` against the referee implementation |
| `ep_P1_allB.py` | Conjecture P for every choice of `B*` |
| `ep_thmA2.py` | Theorem A' and its false variant |
| `ep_Pprime.py` | the false strengthening R5 of Conjecture P |
| `ep_corB4.py` | Corollary B.4 and its false variant |
