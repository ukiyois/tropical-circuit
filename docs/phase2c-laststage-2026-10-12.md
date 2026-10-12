# Phase 2c: the last-stage block (2026-10-12)

Question (B1 note, Section 4.1; coordinator's brief): iterate the circuit block of
stage `r = k - 1` alone from `p = 0`. Does `nu0` never decrease, does the
iteration reach `nu0 = k` (so `Psi = Opt`), and how many iterations does it take?
Setting and labels: `paper/greedy_intersection.tex`, Section 4. This note does not
touch `paper/` or `daishu-formal/`.

## Status log (for a relaunched agent)

- 2026-10-12, coordinator. Not used in the paper or in Lean: these results do not
  strengthen Theorem `thm:C` (exact for all real `w`), which stays at `k^4 m^6`.
  Section 9, question 1 was attempted in `docs/phase2f-ls-uniform-2026-10-12.md` and
  stopped without a uniform bound.
- 2026-10-12, about 3 hours. Work finished; no process left running. Scripts
  `experiments/ls_*.py`, logs `experiments/ls_logs/`; Section 8 lists them.
- PROVED (with checks): Proposition 2.1 (Psi-ascent, Lead 1), Lemma 3.1
  (persistence), Theorem 3.2 (chain condition: no mismatch at the jumps of
  `nu(N)` implies monotonicity and equality in Proposition 2.1), Corollary 3.3
  (`k = 3`), Lemma 4.3 (along any block path `nu(L)` never drops from at least 2 to
  1), Corollary 4.4 (blocks at `nu0 <= 2` never decrease `nu0`; **for `k <= 4` the
  last-stage block is monotone**), Theorem 5.1 (**linear convergence**:
  `Opt - Psi(p+a) <= (1 - 1/(k(2k-1)))(Opt - Psi(p))` for the last-stage block, at
  every state), Corollary 5.2 (integer weights of range `W`: at most
  `1 + floor(k(2k-1) ln(kW))` LS iterations).
- REFUTED: the first half of Conjecture LS ("`nu0` never decreases"), by Instance
  LS-1 (Section 4.2; graphic, 6 vertices, `m = 10`, `k = 5`, weights in `{0..4}`,
  `nu0`: 3 -> 2 at the first block; the least possible `k` by Corollary 4.4); also
  the abstract Claim R (Section 4.1) and Lead 4's maximizer condition as an
  invariant (it fails on 108,140 path intervals without any decrease).
- OPEN: a bound on `T_LS` uniform in `w` (so: the exact LS circuit for real
  inputs), finite termination for irrational `w`. Observed: `T_LS <= m + 2` in all
  searches, LS parallelizes long stages (3 iterations against 14 regular updates)
  but can also be slower than the regular schedule (11 against 7).
- Consequence for Theorem `thm:C` (Section 7): exact count unchanged, `R(k, m)`;
  for integer `w` of range `W`, `1 + floor(k(2k-1) ln(kW))` last-stage blocks;
  for real `w`, `ceil(k(2k-1) ln(kW/epsilon))` blocks give `Opt - epsilon <= Psi <= Opt`.

## 0. Summary

1. **Lead 1 holds** (Proposition 2.1): at any state, the stage-`r` block raises
   `Psi` by at least `int_0^{tau_r} (k - nu(N(t))) dt >= (k - r) tau_r`; (F1) is not
   needed.
2. **Monotonicity fails** at `k = 5` (Instance LS-1), and holds for `k <= 4`
   (Corollary 4.4). The exact mechanism (Section 4.1): after the first jump of
   `nu(N(t))` the block raises `Av` of a family whose `nu` exceeds `nu(M^{v(s)})`;
   at a tie, moving `X = E_A` down can trade an element of an unraised block for a
   second element of a raised block that is already met. Persistence of an old
   base (Lemma 3.1) fails exactly at such a mismatch (Theorem 3.2).
3. **Termination with a rate** (Theorem 5.1): each LS iteration closes at least a
   `1/(k(2k-1))` fraction of the gap `Opt - Psi`, monotone or not; hence
   `O(k^2 log(kW))` iterations for integer weights, against about `k^3 log(kW)`
   from the regular schedule (phase 2b, Corollary 2.3).
4. **Iteration counts** (Section 6): several regular stages can be long at once
   (two stages of `m - 4` at `m = 11, 12`); LS then runs them in parallel; LS can
   also be slower than the regular schedule; no growth with the bit length was
   found (`T_LS <= m + 2`).
5. **For Theorem `thm:C`** the exact worst-case count stays `R(k, m)`; see
   Section 7 for the integer and approximate versions.

## 1. Setting

`M` has rank `k` on `E`, `|E| = m`, blocks `R_1, ..., R_k`, a rainbow base exists.
A state is `v = w - p_blk`; `Psi(p) = sum_b p_b + beta(v)`; `nu0 = nu(M^v)`,
`S0 = Av(M^v)`. During one application of a block the family is
`N(t) = N_v(t)`, PO-SL at the state `v` where the block starts (it satisfies
(F1) to (F5), Proposition `prop:posl`), with levels `0 = c_0 < c_1 < ...` (F5).

**The stage-`r` block at any state** (`1 <= r <= k - 1`):

```
a_b = int_0^inf [nu(N(t)) <= r] [b in Av(N(t))] dt .
```

`tau_r = min { t : nu(N(t)) >= r + 1 }` (finite by (F4)); by (F2) `nu(N(t))` is
nondecreasing, so the integrand vanishes for `t >= tau_r`. At `nu0 = r` this is the
PO-SL update of stage `r` (eq. `eq:update-integral`); at `nu0 > r` it is `0`. The
**last-stage block** is `r = k - 1`; the **LS iteration** applies it from `p = 0`
until `nu0 = k`.

**The path.** For `s >= 0` put

```
a(s)_b = int_0^s [nu(N(t)) <= r][b in Av(N(t))] dt,   v(s) = v - a(s)_blk,
L(s) = M^{v(s)},   phi(s) = Psi(p + a(s)).
```

So `a(0) = 0`, `a(tau_r) = a`, `a(s) in [0, s]^k`, and on a piece
`[c_i, c_{i+1})` below `tau_r` the path moves in direction `-1_X`,
`X = E_{A_i}`, `A_i = Av(N(c_i))`.

## 2. Psi-ascent (Lead 1): proved

**Proposition 2.1 (Psi-ascent).** Let `N(t)` be any family of matroids on `E`
satisfying (F2), (F3), (F4), (F5) for the state `v` ((F1) is not used, and `nu0`
is arbitrary). Then for every `s >= 0`

```
phi(s) - phi(0)  >=  int_0^s [nu(N(t)) <= r] (k - nu(N(t))) dt ,
```

and in particular, for the block output `a = a(tau_r)`,

```
Psi(p + a) - Psi(p)  >=  int_0^{tau_r} (k - nu(N(t))) dt  >=  (k - r) tau_r .
```

*Proof.* Step 1, the path. The integrand is a step function of `t` with values in
`{0, 1}` (F5), so `a(s)` is continuous, piecewise linear and `a(s) in [0, s]^k`.
As `beta(v(s))` is a minimum of finitely many continuous piecewise linear functions
of `s`, so is `phi`, and

```
phi(s) - phi(0) = int_0^s phi'(sigma+) d sigma .
```

Step 2, the right derivative. Let `sigma in [c_i, c_{i+1})`, `g = [nu(N(c_i)) <= r]`,
`A = Av(N(c_i))`, `X = E_A`. For small `h > 0`, `a(sigma + h) = a(sigma) + h g 1_A`,
and the minimum bases of `v(sigma) - h 1_X` are the minimum bases of `v(sigma)` with
the most elements in `X` (for `h` below the least positive gap between values of
bases, divided by `k`). Hence

```
phi'(sigma+) = g ( |A| - max { |B cap X| : B in Bases(M^{v(sigma)}) } )
             = g ( |A| - r_{M^{v(sigma)}}(X) ).
```

Step 3, the sandwich. By Lemma `lem:path` with `y = a(sigma) in [0, sigma]^k`, and by
(F3),

```
Bases(M^{v(sigma)})  subseteq  P_sigma  subseteq  Bases(N(sigma)),
```

so `r_{M^{v(sigma)}}(X) <= r_{N(sigma)}(X)`, and Lemma `lem:avoidable`(2) for
`N(sigma) = N(c_i)` gives

```
phi'(sigma+) >= g ( |A| - r_{N(sigma)}(E_A) ) = g ( |A| - |A| + (k - nu(N(sigma))) )
             = g ( k - nu(N(sigma)) ).
```

Step 4. Integrate Step 3 by Step 1. For the second display, `g = 1` and
`nu(N(t)) <= r` for `t < tau_r`, and `g = 0` for `t >= tau_r` by (F2).

So every block application at `nu0 < k` raises `Psi` by at least `tau_{k-1} > 0`
(`tau_{k-1} > 0` because `nu(N(0)) = nu0 < k` by (F1)), and `Psi <= Opt`
(Lemma `lem:duality`).

Checked (`ls_mono_random.py 8 60`): 311,707 block applications at 249,851 random
states (graphic, binary, uniform, sparse paving, sums; `k <= 5`, `m <= 10`), of
which 61,856 at `nu0 < r`: no failure. At `r = nu0` the harness also asserts
validity's equality `Psi(p + a) - Psi(p) = (k - nu0) tau` (Theorem `thm:validity`(1)),
which held in all 249,851 cases. Discrimination: the false variant
"`Psi(p + a) - Psi(p) >= (k - nu0) tau_r`" (rate of the first stage throughout)
fails in 53,933 of the 61,856 multi-stage blocks.

## 3. Persistence: when an old base survives

**Lemma 3.1 (persistence).** Let `N` satisfy (F1) to (F5), `0 <= s0 < s1 <= tau_r`,
and suppose `nu(N(t)) = mu` for `t in [s0, s1)` and `nu(L(s0)) >= mu`. Then every
base `B*` of `L(s0)` meeting `mu` blocks is a minimum base of `v(s)` for every
`s in [s0, s1]`, and

```
phi(s) = phi(s0) + (k - mu)(s - s0)        (s in [s0, s1]).
```

In particular `nu(L(s)) >= mu` on `[s0, s1]`.

*Proof.* Step 1. `nu(L(s0)) <= nu(N(s0)) = mu` (Proposition 2.1, Step 3, gives
`Bases(L(s0)) subseteq Bases(N(s0))`), so `nu(L(s0)) = mu` and `B*` exists.
Step 2. For `s in [s0, s1)` let `A = Av(N(s))`. By Step 3 of Proposition 2.1 and
(F2), `B* in Bases(N(s0)) subseteq Bases(N(s))`. A base of `N(s)` meeting
`mu = nu(N(s))` blocks contains a rainbow independent set of size `mu` missing the
same blocks, so the `k - mu` blocks missed by `B*` lie in `A`, and with Lemma
`lem:avoidable`(2),

```
|A| - (k - mu) <= |B* cap E_A| <= r_{N(s)}(E_A) = |A| - (k - mu).
```

Step 3. So `psi(s) = sum_b (p_b + a(s)_b) + v(s)(B*)` has right derivative
`|A| - |B* cap E_A| = k - mu` on `[s0, s1)`, and `psi(s0) = phi(s0)`. By
Proposition 2.1 (Step 3), `phi'(s+) >= k - mu`. Hence

```
psi(s) = phi(s0) + (k - mu)(s - s0) <= phi(s) <= psi(s)      (s in [s0, s1)),
```

the last inequality since `phi(s) = sum_b(p_b + a(s)_b) + beta(v(s))`. So `B*` is
minimum for `v(s)`; at `s1` by continuity.

**Theorem 3.2 (chain condition).** Let `0 = t_0 < t_1 < ... < t_j = tau_r` be the
points where `nu(N(.))` changes below `tau_r`, `mu_i = nu(N(t))` on
`[t_i, t_{i+1})`. If `nu(L(t_i)) >= mu_i` for every `i < j`, then
`nu(L(s)) >= mu_i` on `[t_i, t_{i+1}]`, `nu(M^{v'}) >= mu_{j-1} >= nu0`, and
Proposition 2.1 holds with equality:
`Psi(p + a) - Psi(p) = sum_i (k - mu_i)(t_{i+1} - t_i)`.

*Proof.* Lemma 3.1 on each `[t_i, t_{i+1}]`. For `i = 0` the hypothesis is
`nu(L(0)) = nu0 = mu_0` by (F1).

**Lead 3 (decomposition), checked.** With `v1 = v(t_1)` and `y = a(t_1) in [0, t_1]^k`,
`|(v1_f - v1_e) - (v_f - v_e)| <= t_1` for all `e, f`, so
`|theta_{v1}(B) - theta_v(B)| <= t_1` for every base `B` (both directions hold; the
one used is `theta_v(B) <= theta_{v1}(B) + t_1`), hence
`P_s(v1) subseteq P_{s + t_1}(v) subseteq Bases(N(t_1 + s))`: after `t_1` the block
runs the stale family `N(t_1 + .)`, which satisfies (F2) to (F5) and (F3) for `v1`,
and (F1) only when `nu(M^{v1}) = nu(N(t_1))` and the old base survives.

So the only danger is a **mismatch** at a jump `t_i`: `nu(L(t_i)) < nu(N(t_i))`.
At `t_1 = tau_{nu0}` the block has performed exactly the regular stage-`nu0` update
(`v(t_1)` is the state after it), so `nu(L(t_1)) >= nu0` by Theorem
`thm:validity`(2), and there is no mismatch at `t_1` iff that update ends stage
`nu0` with `nu(M^{v(t_1)}) >= nu(N(t_1))`.

**Corollary 3.3 (k = 3).** For `k = 3` the last-stage block never decreases `nu0`,
and at `nu0 = 1` one application gives `nu0 >= 2`. Hence the LS iteration takes
`[nu(M^w) = 1] + ` (stage-2 updates from the state reached), at most
`1 + min(2(floor(m^2/4) + 1), 1 + 3m)` iterations, the same bound as
`R(3, m)`.

*Proof.* At `nu0 = 2 = k - 1` the block is the regular update. At `nu0 = 1`:
stage 1 always takes exactly one PO-SL update (phase 2b note, Theorem 2.1: `|S0| =
k - 1` and `S0` cannot grow), so `nu(L(t_1)) >= 2`. If `nu(N(t_1)) = 3`, then
`tau_2 = t_1`; otherwise `nu(N(t)) = 2` on `[t_1, tau_2)` and Theorem 3.2 applies
with `mu_1 = 2`. The bound is Theorems `thm:potential` and `thm:stagelength` at
`r = 2`.

## 4. Monotonicity of `nu0`: refuted

### 4.1 The local mechanism, and an abstract claim that is false

On a piece `[c_i, c_{i+1})` of the path, `N(s) = N_i` is fixed and
`Bases(L(s)) subseteq Bases(N_i)` (Proposition 2.1, Step 3), so
`L(s) = N_i^{v(s)}`: the minimum bases of `v(s)` over all bases of `M` are those
over the bases of `N_i`. With `X = E_A`, `A = Av(N_i)`, the path moves in direction
`-1_X`. At a tie point `s1` inside the piece, with tie matroid `T = M^{v(s1)}`, the
matroids on the two adjacent open intervals are (eq. `eq:rank-mu` with two levels)

```
before  T^{+1_X} = T/X^c (+) T|X^c ,        after  T^{-1_X} = T|X (+) T/X ,
nu(before) = nu_A(T/X^c) + nu_{A^c}(T|X^c),  nu(after) = nu_A(T|X) + nu_{A^c}(T/X),
```

`nu_Q` the rainbow number for the blocks of `Q`. The `A`-side can only gain
(`T|X` has more independent sets than `T/X^c`) and the `A^c`-side can only lose.
At a tie the matroid contains both neighbours, so `nu` can drop along the path only
at the passage from `T` to `T^{-1_X}`.

**Claim R (false).** "For every matroid `N` with blocks, `A = Av(N)`, `X = E_A`, and
every `u`, `nu((N^u)^{-1_X}) >= nu((N^u)^{+1_X})`." Counterexample
(`ls_refine.py`, log `ls_logs/refine_claim.txt`): `N = M` the graphic matroid on
6 vertices with edges `23,51,10,10,42,51,03,53,04,30`, blocks
`[4,1,2,1,4,3,4,4,0,0]` (`k = 5`, `nu(N) = 4`, `Av(N) = {1,2,3}`), and
`u = (0,1,4,2,0,3,2,1,2,4)`: `T = N^u` has the bases `{0,1,3,4,7}` (blocks `{1,4}`,
two elements in `X`), `{0,1,4,6,7}` and `{0,1,4,7,8}` (blocks `{0,1,4}`, one element
in `X`); moving `X` down keeps only the first, which spends two elements on block
1, so `nu` drops from 3 to 2. Claim R failed in 4 of 1,176,000 random cases
(20,315 nontrivial); its variants with `A` replaced by a random set of blocks, a
random superset or a random proper subset of `Av(N)` fail 21,990, 14,445 and 957
times. Here `N = M` has no rainbow base, so this is not yet an instance of the
block.

### 4.2 The counterexample inside a block

Embedding the Claim R instance in a matroid with a rainbow base (adding edges;
`ls_embed.py`, log `ls_logs/embed_1.txt`) produced real decreases, and
`ls_minimize.py` reduced one to the following instance.

**Instance LS-1.** Graphic matroid on vertices `0..5`, `k = 5`, `m = 10`:

| element | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| edge | 23 | 51 | 10 | 42 | 51 | 53 | 04 | 05 | 10 | 24 |
| block | 0 | 1 | 1 | 0 | 2 | 0 | 3 | 4 | 3 | 1 |
| `w` | 0 | 3 | 3 | 0 | 4 | 0 | 2 | 2 | 0 | 4 |

At `p = 0` (`v = w`): `beta = 2`, the minimum spanning trees are `{0,3,5,6,8}`
(blocks `{0,3}`) and `{0,3,5,7,8}` (blocks `{0,3,4}`), so `nu0 = 3`. The
last-stage block (`r = 4`) has pieces

| `[c_i, c_{i+1})` | `nu(N)` | `Av(N)` |
|---|---|---|
| `[0,1)` | 3 | `{1,2}` |
| `[1,2)` | 3 | `{1,2,4}` |
| `[2,3)` | 4 | `{1,2}` |
| `[3,4)` | 4 | `{1,2,4}` |

`tau_4 = 4`, `a = (0, 4, 4, 0, 2)`, `v' = (0,-1,-1,0,0,0,2,0,0,0)`, `beta(v') = -2`,
and the minimum spanning trees of `v'` are `{0,1,2,3,5}` and `{0,1,2,5,9}`, both
meeting only blocks `{0,1}`: **`nu(M^{v'}) = 2 < 3 = nu(M^v)`**. Along the path,
`nu(L(s))` is `3` on `(0,1), (1,2), (2,3)` and at the points `1, 2, 3`, and `2` on
`(3,4)` and at `4`. The stage-3 part ends at `t_1 = 2` with
`nu(L(2)) = 3 < 4 = nu(N(2))` (a mismatch, Section 3). The drop happens at the
point `s = 3`, `v(3) = (0,0,0,0,1,0,2,1,0,1)`, where block 4 joins the raised set
(`A = {1,2,4}`): the bases of `L(3)` with the most elements in `E_A` are
`{0,1,2,3,5}` and `{0,1,2,5,9}`, which spend two or three elements on block 1
(elements `1, 2, 9`) and none on blocks 2, 3, 4, the mechanism of Claim R. `Psi` rises from 2 to 8 (`Opt = 12`), equal to
Proposition 2.1's bound `2 * (5-3) + 2 * (5-4) = 6`. Checked with the independent
referee implementation (`referee_phase2a/core.py`: same block vector, same `nu`
before and after, same `Psi`).

So **the first half of Conjecture LS is false**: with `w` as above the LS
iteration decreases `nu0` at its first step. It still ends at `Opt`: `nu0` runs
`3, 2, 5` (2 iterations; the regular schedule takes `0, 0, 3, 2`, 5 updates).

### 4.3 What survives: no drop to one block, and `k <= 4`

**Lemma 4.3 (no drop to one block).** Let `N` satisfy (F1) to (F5) for the state
`v`, `1 <= r <= k - 1`, `k >= 2`, and consider the path of the stage-`r` block. If
`0 <= s' <= s <= tau_r` and `nu(L(s')) >= 2`, then `nu(L(s)) >= 2`.

*Proof.* Step 1, the order of events. On each piece `v(s)` is affine in `s`, so
`[0, tau_r]` splits into finitely many points and open intervals on which the weak
order of `v(s)`, hence `L(s)`, is constant. At a point `s*` with `T = L(s*)`, the
matroids `L-` and `L+` of the adjacent open intervals satisfy
`Bases(L-), Bases(L+) subseteq Bases(T)` (a base that is minimum on an open interval
is minimum at its end, by continuity), so `nu(T) >= nu(L-)`. It remains to show:
`nu(L+) = 1` implies `nu(T) = 1`, for every point `s* < tau_r`.

Step 2, the matroid after `s*`. Let `A = Av(N(s*))`, `X = E_A`. As in Step 2 of
Proposition 2.1, `L+` consists of the bases of `T` with the most elements in `X`.
Suppose `nu(L+) = 1`. Two bases of `L+` inside different blocks `R_b`, `R_c` would
give, by basis exchange, a base of `L+` meeting both (as `k >= 2`), so every base of
`L+` lies in one block `R_b`.

Step 3, `b in A` is impossible. A base `B` of `L+` has `B subseteq R_b subseteq X`,
and `B in Bases(T) subseteq Bases(N(s*))` (Proposition 2.1, Step 3), so by Lemma
`lem:avoidable`(2)

```
k = |B cap X| <= r_{N(s*)}(X) = |A| - (k - nu(N(s*))) <= nu(N(s*)) <= r <= k - 1 .
```

Step 4, `b notin A`. Then `|B cap X| = 0` for the bases of `L+`, which maximize
`|B cap X|` over `Bases(T)`; so every base of `T` misses `X`, `L+ = T`, and
`nu(T) = nu(L+) = 1`.

**Corollary 4.4.**
1. Every stage-`r` block applied at a state with `nu0 = 2` gives `nu(M^{v'}) >= 2`.
2. Every stage-`r` block applied at a state with `nu0 = 1` gives `nu(M^{v'}) >= 2`.
3. For `k <= 4` the last-stage block never decreases `nu0`. Instance LS-1
   (`k = 5`) is therefore of the least possible rank, and at `k = 5` a decrease
   can only go from 3 to 2.

*Proof.* Item 1: Lemma 4.3 with `s' = 0`. Item 2: the first piece `[0, t_1)`,
`t_1 = tau_1 <= tau_r`, is the regular stage-1 update, which ends stage 1
(Theorem `thm:stagelength` at `r = 1`: one update), so `nu(L(t_1)) >= 2`; then
Lemma 4.3 with `s' = t_1`. Item 3: at `nu0 = k - 1` the block is the regular
update (Theorem `thm:validity`(2)); for `k <= 4` the remaining values are
`nu0 <= 2`, covered by items 1 and 2.

Checked exhaustively (`ls_k4_exhaustive.py 3 10`, log `ls_logs/k4_exhaustive_L3.txt`):
eight matroids of rank 4 (U46, C5+chord, C5+2chords, K4+pendant, U23+U23, a binary
matroid on 7 elements, C4par+tail, U45), every block assignment up to renaming with
a rainbow base, every `v in {0..3}^E` with `min v = 0`: 1,989,004 states with
`nu0 <= 2`, no decrease of `nu0`, no path interval with `nu(L) < 2`, and all
21,716 states with `nu0 = 1` end with `nu0 >= 2`. The statement "no drop below 3
once at least 3" is false (Instance LS-1), so Lemma 4.3 does not extend upwards.

## 5. Linear convergence of the LS iteration: proved

**Theorem 5.1.** Let `v` be a state with `nu0 < k`, `a` the last-stage PO-SL block
at `v`, `tau = tau_{k-1}`, and `q` the largest number of distinct values `v_b`,
`b in B cap K`, over the components `K` of `M`, `B` a minimum base of `v`
(`q <= k`; it does not depend on `B`). Then

```
(1)  Opt(w) - Psi(p)      <=  k (2q - 1) tau ,
(2)  Psi(p + a) - Psi(p)  >=  tau ,
(3)  Opt(w) - Psi(p + a)  <=  (1 - 1/(k(2q-1))) (Opt(w) - Psi(p))
                          <=  (1 - 1/(k(2k-1))) (Opt(w) - Psi(p)) .
```

*Proof.* Step 1, a rainbow base at `tau`. By the definition of `tau`,
`nu(N(tau)) = k`, so `N(tau)` has a rainbow base `B_R`.
Step 2, the scale sandwich (phase 2b note, Proposition 1.3:
`Bases N(t) subseteq P_{(2q-1)t}`): `theta(B_R) <= (2q - 1) tau`.
Step 3, Proposition `prop:pos` ((1) implies (3)) with `B'` a minimum base of `v`:

```
v(B_R) - beta(v) <= theta(B_R) |B_R \ B'| <= k (2q - 1) tau .
```

Step 4, `B_R` is rainbow, so

```
Opt(w) <= w(B_R) = sum_b p_b + v(B_R) <= sum_b p_b + beta(v) + k(2q-1) tau
        = Psi(p) + k (2q - 1) tau ,
```

which is (1). Step 5, (2) is Proposition 2.1, as `nu(N(t)) <= k - 1` for
`t < tau`. Step 6, (3): by (2) and (1),
`Opt - Psi(p + a) <= Opt - Psi(p) - tau <= (1 - 1/(k(2q-1)))(Opt - Psi(p))`.

**Corollary 5.2 (integer weights).** If `w` is integral with
`W = max w - min w >= 1`, the LS iteration from `p = 0` reaches `nu0 = k` (so
`Psi = Opt`) after at most `1 + floor(k (2k - 1) ln(k W))` iterations.

*Proof.* Step 1, integrality. The levels are differences of values, so every
`tau`, every piece length and every `a_b` is an integer, and `p`, `v`, `Psi` stay
integral. Step 2, the gap. `Opt(w) - Psi(0) = Opt(w) - beta(w) <= k W`. While
`nu0 < k`, `Psi(p) < Opt`: by Lemma `lem:avoidable`(2) the directional derivative
of the concave `Psi` in direction `1_{S0}` is `|S0| - r_{M^v}(E_{S0}) = k - nu0 > 0`,
so `p` is not a maximizer, and `max Psi = Opt` (Lemma `lem:duality` and the proof of
Theorem `thm:C`); so the gap is a positive integer. Step 3, by Theorem 5.1(3),
after `j` iterations the gap is at most `k W e^{-j/(k(2k-1))}`, which is below 1
for `j > k(2k-1) ln(kW)`.

For comparison, Corollary 2.3 of the phase 2b note bounds the regular schedule by
`sum_{r<k} (1 + (r-1)(1 + (2k-1) ln(kW)))`, about `k^3 ln(kW)`; the LS iteration
needs about `2k^2 ln(kW)`, a factor `k/2` fewer, **without monotonicity of `nu0`**.
The bound is not uniform in `w`: it does not give a static circuit for real inputs.

Checked (`ls_linear.py 10 150`, log `ls_logs/linear_1.txt`): 407,732 LS runs,
608,977 iterations (random graphic, binary, uniform, paving, sums, `m <= 10`; Opt and
`t* = min theta` of a rainbow base by enumeration): items (1), (2), (3) and
`tau >= t*/(2q - 1)` hold everywhere, Corollary 5.2's bound never fails, the largest
ratio `(Opt - Psi)/(k (2q-1) tau)` is `0.75`. Discrimination: "gap `<= (2q-1) tau`"
fails 11,906 times, "gap `<= k tau`" 240 times, "gap `<= k t*/2`" 1,512 times.

## 6. Iteration counts (Goal 3)

**Termination.** For rational weights the LS iteration always terminates
(Corollary 5.2 after scaling). For real weights, Theorem 5.1 gives linear
convergence of `Psi` to `Opt`, not finite termination. Since `nu0` is not monotone,
the pair potentials of Theorems `thm:potential` and `thm:stagelength` can be
undone by the continuation of a block (the blocks raised after `tau_{nu0}` are
`Av` of the stale family, not `S0`), and no uniform bound `T_LS(k, m)` is proved.
The block is integer-linear on finitely many rational cones, so the danger is a
Euclid-type mechanism: a cycle of combinatorial types whose composite linear map
contracts along an irrational ray would give finite but unbounded `T_LS` on
rational inputs near the ray. Nothing of the kind was observed (below).

**Measurements.** (`ls_stats.py 10 120`, log `ls_logs/stats_1.txt`; graphic,
binary, uniform, paving, sums, `k = 3..6`, `m <= 11`, mixed weights.)

| quantity | value |
|---|---|
| runs (all end at `Opt`) | 337,235 |
| `T_LS` < / = / > regular active updates | 65,086 / 272,107 / 42 |
| total `T_LS` against total regular | 452,724 against 522,217 |
| largest `T_LS`, largest regular | 7, 11 |
| `T_LS - regular`, `T_LS - longest stage` (max) | 2, 4 |
| `T_LS / R(k, m)` (max) | 0.25 |
| runs with a decrease of `nu0` | 0 (decreases are rare; Section 4.2) |

Hill climbing (`ls_search_T.py`, graphic, integer weights up to `2^30`, logs
`ls_logs/searchT_*.txt`, 5 to 10 workers, 200 to 240 s):

| objective | `n`, `m` (`k = n - 1`) | best found |
|---|---|---|
| `T_LS - regular` | 6, 10 | `+3` (8 against 5) |
| `T_LS - longest regular stage` | 6, 11 / 7, 12 | `+6` (9 against stages `(0,2,2,3)`) / `+8` (11 against `(0,0,1,3,3)`, total 7) |
| `T_LS - m`, 24 and 30 bits | 6, 10 / 5, 8 / 6, 9 | 12 = `m + 2` / 8 = `m` / 11 = `m + 2` |
| iterations at `nu0 <= k - 2` | 7, 12 | 10 (then one at `k - 1`) |
| two long regular stages | 6, 11 / 7, 12 | stages `(0,0,8,7)`: `T_LS = 8`; `(0,1,6,7)`: `T_LS = 3`; `(0,0,0,8,8)`: `T_LS = 9`; `(0,0,1,8,7)`: `T_LS = 5` |
| decreases of `nu0` | 5, 9 / 6, 10 / 7, 12 | none found by hill climbing (only by the embedding of Section 4.2) |
| decreases, then `T_LS - regular`, around LS-1 (`ls_recharge.py`, LS-1 plus 0 to 3 edges, weights scaled by up to `2^10`) | 6, 10 to 13 | at most one decrease per run; `T_LS - regular <= 3` (7 against 4, `nu0`: `3, 2, 3, 4, 4, 4, 4, 5`) |

Reading:
1. **Several regular stages can be long at the same time**: two stages of
   `m - 4` updates each at `m = 11, 12` (`k = 5, 6`). On these instances LS runs
   the stages in parallel (`T_LS` about one stage, down to 3 against 14).
2. **LS can also be slower than the regular schedule**: 11 iterations against 7
   (`k = 6`, `m = 12`), because its states differ and its own phases at each
   value of `nu0` are sequential.
3. **No growth with the bit length**: with 24 and 30 bits the longest LS runs are
   `m + 2`, and they are pure last-stage runs (`nu0 = k - 1` from the start), where
   LS is the regular schedule.
4. The worst `T_LS` found is about the worst single regular stage (`m + O(1)`
   here, `m + 5` at `k = 6` in phase 2b), far below `R(k, m)` (ratio at most 0.25).

## 7. Consequences for Theorem `thm:C` (Goal 4)

**Exact circuits for all real `w`.** The LS circuit (`T` copies of the
last-stage block, then `Psi`) is not justified: the monotonicity it relied on is
false (Instance LS-1), and no bound `T_LS(k, m)` uniform in `w` is proved. A
schedule of block indices is provably safe when every block of stage `r >= 3` is
applied only at states with `nu0 >= r` or `nu0 <= 2` (Theorem `thm:validity`,
Corollary 4.4); the regular schedule is such a schedule, and the results above
give no progress bound for blocks applied at `3 <= nu0 < r` (they can decrease
`nu0`) or for repeated blocks at `nu0 = 2` (they cannot decrease `nu0`, but the
pair potentials can be undone). So the worst-case count stays

```
R(k, m) = sum_{r=1}^{k-1} min( r (floor(m^2/4) + 1), 1 + (r-1) k m )
        <= (k - 1)(1 + (k - 2) k m) .
```

**Integer inputs (Corollary 5.2).** For integral `w` with `max w - min w <= W`, the
circuit of

```
T(k, W) = 1 + floor( k (2k - 1) ln(k W) )
```

last-stage blocks followed by the output `Psi` computes `Opt(w)` exactly. Each block
is the circuit of Lemma `lem:oneupdate` with `r = k - 1` (it computes the threshold
integral at every state, not only at `nu0 = k - 1`, by Steps 2 and 5 of the proofs
of Lemmas `lem:observer` and `lem:oneupdate`), so the size is
`O(k^3 m^5 (s + m) log(kW))`, against `O(k^4 m^6 (s + m))` for Theorem `thm:C`.

**Additive approximation for all real `w` (Theorem 5.1(3)).** For real `w` with
`max w - min w <= W` and `epsilon > 0`, after

```
T = ceil( k (2k - 1) ln(k W / epsilon) )
```

last-stage blocks, `Opt(w) - epsilon <= Psi(p_T) <= Opt(w)`. (Proof: the gap starts at
`Opt(w) - beta(w) <= kW` and is multiplied by at most `1 - 1/(k(2k-1))` per
iteration; `Psi <= Opt` by Lemma `lem:duality`.)

**What would give an exact gain.** A uniform bound `T_LS <= T(k, m)`; then
`T(k, m)` blocks replace `R(k, m)`. The data (Section 6) are consistent with
`T_LS <= m + O(k)`, about the longest single regular stage, which would be a gain
of order `k^2` against `R(k, m)` if proved. The obstacle is identified: drops of
`nu0` (Section 4) and a possible Euclid-type cycle (Section 6).

## 8. Scripts and logs (all in `experiments/`, exact arithmetic)

| script | what it does | log |
|---|---|---|
| `ls_core.py` | the stage-`r` block at any state, its pieces, the exact path with all tie points (`path_profile`), the LS iteration, `R(k, m)` | |
| `ls_mono_random.py` | Proposition 2.1, validity's equality at `r = nu0`, `nu0` monotonicity at random states, false variants | (console, Section 2) |
| `ls_lead4.py` | mismatch, Lead 4's maximizer condition, `Av(L) subseteq A` along multi-stage paths | (console, Section 4.1) |
| `ls_refine.py` | Claim R and its variants on arbitrary matroids | `ls_logs/refine_claim.txt` |
| `ls_search_drop.py` | path and end decreases on random larger instances and along LS and regular runs | `ls_logs/search_drop_1.txt` |
| `ls_ties.py` | gain on `A` and loss on `A^c` at the tie points of real paths | `ls_logs/ties_1.txt` |
| `ls_embed.py` | Claim R's instance embedded in matroids with a rainbow base: real decreases | `ls_logs/embed_1.txt` |
| `ls_minimize.py` | reduction to Instance LS-1 | (console, Section 4.2) |
| `ls_k4_exhaustive.py` | Lemma 4.3 and Corollary 4.4 exhaustively at `k = 4` | `ls_logs/k4_exhaustive_L3.txt` |
| `ls_linear.py` | Theorem 5.1 (1) to (3), `tau >= t*/(2q-1)`, Corollary 5.2, false variants | `ls_logs/linear_1.txt` |
| `ls_stats.py` | `T_LS` against the regular schedule and `R(k, m)` | `ls_logs/stats_1.txt` |
| `ls_search_T.py` | hill climbing: `T_LS - regular`, `T_LS - longest stage`, `T_LS - m` (24 and 30 bits), iterations below `k - 1`, two long stages, drops | `ls_logs/searchT_*.txt` |
| `ls_recharge.py` | hill climbing around Instance LS-1: repeated decreases and `T_LS - regular` | `ls_logs/recharge_1.txt` |

Additional numbers from runs without a log file: `ls_mono_random.py 8 60`:
249,851 states, 311,707 blocks (61,856 at `nu0 < r`), no decrease, no failure of
Proposition 2.1, `F_RATE0` fails 53,933 times. `ls_lead4.py 8 60`: 133,889
multi-stage blocks, 1,586,241 open intervals; mismatch on 109,146 intervals (in
14,460 blocks), Lead 4's condition fails on 108,140, `Av(L) not subseteq A` on
107,871, and still no decrease. `ls_search_drop.py 10 480`: 331,570 multi-stage
blocks, 4,791,073 intervals, no decrease (the generic random search does not find
the rare instances; the embedding does: `ls_embed.py 10 150` gave 8 path decreases
and 1 end decrease in 857,825 blocks).

## 9. Open questions and next steps

1. **A uniform bound for `T_LS`**, or a Euclid-type construction showing that
   none exists. The natural attempt: a potential combining `Psi` (Theorem 5.1) with
   crossings that the continuation cannot undo.
2. **A safe multi-stage block.** Theorem 3.2 says the only danger is a mismatch
   `nu(L(t_i)) < nu(N(t_i))` at a jump. A block whose raised set after a jump is
   chosen from information in `G_t` that certifies no mismatch would be safe; none
   is known.
3. **Repeated blocks at `nu0 = 2`** are monotone (Corollary 4.4); a progress bound
   for them would let a schedule merge stage 2 into stage 3 (a lower-order saving).
4. **Paper text** (for the coordinator): Section 7's question about the last-stage
   block can be stated with Instance LS-1 (monotonicity fails at `k = 5`, not for
   `k <= 4`) and Theorem 5.1 (linear convergence, `O(k^2 log(kW))` blocks for
   integer weights).
