# Phase 3, B1: the warm start of capacity scaling (2026-10-12)

Problem B1: signed tropical circuits (`max`, `+`, `-`, constant `0`) for the
minimum cost of a capacitated transportation problem. The rainbow-base schedule
of `paper/greedy_intersection.tex` (Section 4) runs one stage per rank value,
and there are `F - 1` rank values, `F` the total flow, pseudo-polynomial in the
capacities. The phase 2b note (`docs/phase2b-stage-length-2026-10-12.md`,
Section 4) bounds every stage by `p (floor(m0^2/4) + 1)` updates (Theorem 4.2)
and proposes a capacity-scaling schedule whose restart deficit it conjectures
to be at most `X = p + q + 2 m0` (Conjecture 4.3). This note settles the
conjecture and derives the B1 consequence. References "Proposition 4.1",
"Theorem 4.2", "Conjecture 4.3" are to the phase 2b note; labels such as
`lem:avoidable` are to the paper.

## Status log (for a relaunched agent)

- 2026-10-12, 13:00 to 17:30. Work finished; no process left running.
- Conjecture 4.3 is FALSE for the chain of the phase 2b note (floor chain):
  exact counterexamples `T(s, D, B)`, smallest found `T(1, 7, 3)` (deficit 42,
  `X = 37`), `experiments/b1_counterexample.py`.
- Proved (Section 3): Lemmas 3.1 to 3.3, Theorem 3.4 (comparison of two
  instances), Corollary 3.5 (floor chain, deficit `<= m0 max(q, 2)`),
  Proposition 3.6 (`T(s, D, B)`, deficit `(m0 - q)(q - 1)`), Corollary 3.7
  (balanced chain, deficit `<= m0 + floor((p+q)/2)`), Proposition 3.8
  (`R(k, q)`, deficit `m0 - p - Q + 1` on both chains). Section 5: Theorem 5.1
  (scaled schedule, `O(p m0^3 log U)` updates, ends at `Opt`), the circuit
  (Section 5.2), Proposition 5.3 (general min-cost flow).
- Checks (Section 4): every lemma on random data, with deliberately false
  variants that fail; the scaled schedule with the proven `X` on 720 random
  instances (6,401 restarts), always `Opt`; uncompressed cross-check of
  Lemma 3.1 on 339 instances.
- Proposition 5.3 checked on 720 random digraphs (brute-force min cost for
  small capacities, exact min-cost flow up to capacity 1,000):
  `experiments/b1_mincostflow.py`.
- Exploratory (Section 4.1): the circuit block of the last stage alone, iterated
  from `p = 0`, reached `Opt` with `nu0` never decreasing on every instance
  tried (general matroids, adversarial search, transportation with `F` up to
  136,639 and no scaling, at most 4 updates there). Recorded as a conjecture,
  Section 6, item 4; not proved.
- Open (Section 6): formal write-up of the typed observer; exact constant for
  the balanced chain; a chain with deficit `O(p + q)`; the last-stage block;
  polymatroids that are not networks.
- This note does not touch `paper/` or `daishu-formal/`. Scripts:
  `experiments/b1_*.py`, logs `experiments/b1_logs/`.

## 1. Summary

**Refuted.** Conjecture 4.3 is false for the chain of the phase 2b note
(`x_{f+1} = floor(x_f / 2)`, here the *floor chain*). The instances
`T(s, D, B)` of Proposition 3.6 have restart deficit exactly
`s D (D - 1) = (m0 - q)(q - 1)` at the potentials of the scaled schedule. The
smallest member found that violates the conjecture is `T(1, 7, 3)`: `p = 2`,
`q = 7`, `m0 = 14`, `F = 49`, deficit 42 against `X = 37`. Mechanism: a source
with no supply in `I_{f+1}` enters `I_f` with potential `0`; its edges stay
cheap, and each of its `deg` edges offers `min(c_e, a_i)` units, up to `deg`
units each, which push the other sources out at every sink at once. The
member `T(1, 3, 1)` has deficit 6, equal to the largest value observed on the
random instances of the phase 2b note.

**Proved.**
1. *Compressed Rado formula* (Lemma 3.1): `F - nu0 = max_A (a(A) - r_{M^v}(E_A))`
   over sets `A` of sources, with `r_{M^v}(E_A)` a sum of one term per sink.
2. *One sink* (Lemma 3.2): the largest number of units a set of sources
   receives in a cheapest fill of one sink is
   `min_t max(kappa(A_{<=t}), b - kappa(rest_{<=t}))`.
3. *Comparison* (Theorem 3.4): for feasible instances `I`, `I'` on one graph
   and any per-source potential `P` at which `I'` is solved, the deficit of `I`
   at `P` is at most `max_A [alpha(A) + sum_j max(L_A(j), G_A(j) - beta_j)]`,
   with `alpha`, `beta` the supply and demand corrections and `L`, `G` the
   losses and gains of the units `min(c_e, a_i)`. The bound is attained on the
   families `T(s, D, B)` and `R(k, q)` below and on the largest `4 x 4`
   instance found by search.
4. *Floor chain* (Corollary 3.5, Proposition 3.6): deficit at most
   `gamma + sum_i alpha_i max(1, deg(i) - 1) <= m0 max(q, 2)`, and
   `(m0 - q)(q - 1)` occurs: for `m0 >= 2q` the worst case is `Theta(m0 q)`.
5. *Balanced chain* (Corollary 3.7, Proposition 3.8): halving the flow along an
   orientation of its odd entries with `|in - out| <= 1` makes all corrections
   lie in `{-1, 0, 1}`, and the deficit is at most `m0 + floor((p + q)/2)`,
   which is below `p + q + 2 m0`. Capacity rounding alone forces
   `m0 - p - q + 1` on both chains. So Conjecture 4.3 holds for the balanced
   chain, with worst case `m0 + O(p + q)`.
6. *B1* (Theorem 5.1, Section 5.2): with the balanced chain the static scaled
   schedule ends at `Psi = Opt` for every real cost vector after at most
   `p (floor(m0^2/4) + 1) (m0 - 1 + ceil(log2 U) (m0 + floor((p+q)/2)))`
   updates, `O(p m0^3 log U)`. Each update is a signed circuit of size
   polynomial in `m0` and `log U` (its observer is a max flow with hardwired
   integer capacities), and the output is a threshold integral of an integer
   rank (Corollary `cor:integer`). So the minimum cost of a capacitated
   transportation problem, as a function of the real costs, has uniform signed
   tropical circuits of size polynomial in `m0` and `log U`; Section 5.2 lists
   the routine lemmas still to be written out.
7. *Min-cost flow* (Proposition 5.3): a min-cost flow problem with fixed
   integer capacities and demands is an uncapacitated transportation problem
   whose sources have degree 2, where already the floor chain has deficit at
   most `2m`: signed circuits of size polynomial in `m` and `log U`.

**Observed.** On the counterexamples the static schedule with the too small `X`
still ends at `Opt`. On the family the reason is simple: the values take only
the levels `0` and `1`, `nu(N(t))` jumps from `nu0` to `F` at `t = 1`, so the
stage-`r` update applied at `nu0 < r` coincides with the stage-`nu0` update,
and one update reaches `nu0 = F`. More is true in all experiments (Section
4.1): the circuit block of the *last* stage, `r = k - 1`, iterated alone from
`p = 0`, never decreased `nu0` and reached `Opt` on every instance tried
(240 random and 4 long instances of general matroids, an adversarial search,
and 307 transportation instances with `F` up to 136,639, without scaling), in
at most 4 updates on transportation and at most 2 more than the regular
schedule on general matroids. No theorem covers updates at `nu0 < r`; if the
last-stage block can be proved monotone with an update count independent of
`F`, neither the stage index nor the scaling chain is needed for B1
(Section 6, item 4).

## 2. Statement

### 2.1 Setting

An instance `I = (a, b, c)` lives on a bipartite graph `H` with sources `[p]`,
sinks `[q]` and `m0` edges `E_H`: supplies `a`, demands `b`,
`sum a = sum b = F`, capacities `c_e in {1, 2, ...} cup {inf}`. It is
*feasible* if an integral flow `x` has `x(delta(i)) = a_i`, `x(delta(j)) = b_j`
and `0 <= x <= c`. For `e = (i, j)` write `i(e) = i`, `j(e) = j`, and call

```
hc_e = min(c_e, a_{i(e)})
```

the *units* of `e`. For a sink `j` and `A subseteq [p]`, `delta_A(j)` is the set
of edges of `delta(j)` from sources in `A`, and for `Y subseteq E_H`,
`Y_{<=t} = {e in Y : v_e <= t}`; `Y_{<t}`, `Y_{=t}` likewise. Every feasible
flow has `x <= hc`, so `b_j <= hc(delta(j))` for a feasible instance.

Rainbow form (phase 2b, Section 4.1): one element `(e, s)` for every edge `e`
and slot `s in [a_{i(e)}]`, the block of `(e, s)` is the slot `(i(e), s)`,
`k = F`, and `M_I` is the laminar matroid `|X cap e| <= c_e`,
`|X cap sink j| <= b_j`. `M_I` is the direct sum over sinks, and the rank of all
copies of a set `Y subseteq delta(j)` of edges is `min(b_j, hc(Y))`.

Costs `w in R^{E_H}` (real), per-source potentials `P in R^p`, values
`v_e = w_e - P_{i(e)}`. For `A subseteq [p]` let `E_A` be the set of copies of
the edges of sources in `A`, and

```
r^v_I(A) = r_{M_I^v}(E_A),    nu0^I(P) = nu(M_I^v),    d_I(P) = F - nu0^I(P)  (the deficit).
```

### 2.2 Keeping the potentials

**Definition 2.1 (symmetric states, restarts).** The *symmetric state* of `I`
at `P in R^p` is the slot potential `p_{(i,s)} = P_i`, `s in [a_i]`. By
Proposition 4.1, PO-SL updates map symmetric states to symmetric states, so the
schedule acts on `P`: the update of stage `r` is `P -> P + eta` with
`eta_i = (tau - lambda_i)_+` read on the slots of `i`, and `eta_i = 0` when
`a_i = 0` (such a source has no slot and is never avoidable). The scaled
schedule *keeps the potentials*: phase `f` starts at the symmetric state of
`I_f` at the vector `P` reached at the end of phase `f + 1`. Every slot `(i, s)`,
`s in [a^{(f)}_i]`, receives `P_i`, the new slots `s > a^{(f+1)}_i` included; no
slot disappears, since `a^{(f)}_i >= a^{(f+1)}_i` in both chains of Section 2.4.
A source with `a^{(f+1)}_i = 0` has carried no slot in any coarser phase (in both
chains `x_{f+1}(delta(i)) = 0` forces `x_g(delta(i)) = 0` for `g > f`), so it
enters with `P_i = 0`. In edge terms the restart keeps the values
`v_e = w_e - P_{i(e)}` of the `m0` edge types.

### 2.3 What holds at the end of a phase

**Proposition 2.2.** Let `I'` be feasible. For `P in R^p` the following are
equivalent, and they hold for the vector `P` reached at the end of the schedule
of `I'` from any symmetric state.
1. `nu0^{I'}(P) = F'`.
2. `Psi^{I'}(P) = Opt(I')`, where `Psi^{I'}(P) = sum_i a'_i P_i + beta_{M_{I'}}(v)`
   is the Lagrangian of the paper at the symmetric state.
3. Some optimal integral flow `y'` of `I'` is a cheapest fill at every sink:
   with `l'_j` the least value `l` with `hc'(delta(j)_{<=l}) >= b'_j`,
   `y'_e = hc'_e` for `e in delta(j)_{<l'_j}` and `y'_e = 0` for `e in delta(j)`
   with `v_e > l'_j`.
4. `a'(A) <= r^v_{I'}(A)` for every `A subseteq [p]`.

Only item 4 enters the proofs of Section 3; nothing else about the potential of
the coarse phase is used.

*Proof.* Step 1, the end of the schedule. By Theorem 4.2 every stage `r` ends at
a state with `nu0 > r`; the last stage is `r = F' - 1`, and `nu0 <= F'`.

Step 2, items 1 and 2. Lemma `lem:duality` gives `Psi <= Opt` and the
implication from 1 to 2. Conversely, if `Psi(P) = Opt` and `B` is an optimal
rainbow base,

```
Opt = w(B) = sum_b p_b + v(B) >= sum_b p_b + beta(v) = Psi(P) = Opt,
```

so `v(B) = beta(v)`: `B` is a minimum base meeting all `F'` blocks, `nu0 = F'`.

Step 3, items 1 and 3. Rainbow bases are the integral feasible flows with
labelled slots. By Lemma `lem:minbases`(2) and `y' <= c'`, the base of `y'` is
minimum if and only if, at every sink `j` and every `t`,

```
min(b'_j, y'(delta(j)_{<=t})) = min(b'_j, hc'(delta(j)_{<=t})),
```

that is `y'(delta(j)_{<=t}) = hc'(delta(j)_{<=t})` for `t < l'_j` and
`y'(delta(j)_{<=t}) = b'_j` for `t >= l'_j`, which is item 3.

Step 4, items 1 and 4. Lemma 3.1 below gives
`F' - nu0^{I'}(P) = max_A (a'(A) - r^v_{I'}(A))`, and `A = empty` gives `0`.

### 2.4 Two chains

Let `x_0` be a feasible flow of `I_0 = I` (fixed data) and `U = max_e x_0(e)`.
Both chains put `c^{(f+1)} = ceil(c^{(f)} / 2)` (`inf` stays `inf`),
`I_{f+1} = (row sums of x_{f+1}, column sums of x_{f+1}, c^{(f+1)})`, and stop
at the first `f = J` with `max_e x_J(e) <= 1`.

- **Floor chain** (phase 2b note): `x_{f+1} = floor(x_f / 2)`.
- **Balanced chain**: let `O_f = {e : x_f(e) odd}`. Split `O_f` into
  edge-disjoint trails such that every node of odd degree in `O_f` is an end of
  exactly one open trail and the other trails are closed, and orient each trail
  along itself; then every node has `|in - out| <= 1` in `O_f`. Put
  `x_{f+1}(e) = floor(x_f(e)/2) + [e in O_f is oriented from its source to its sink]`.

In both chains `x_{f+1} <= ceil(x_f / 2) <= ceil(c^{(f)} / 2)`, so `I_{f+1}` is
feasible with the flow `x_{f+1}`, and `max x_f <= ceil(U / 2^f)`, so
`J <= ceil(log2 U)`. The corrections are

```
alpha = a^{(f)} - 2 a^{(f+1)},   beta = b^{(f)} - 2 b^{(f+1)},   Delta = hc^{(f)} - 2 hc^{(f+1)}.
```

### 2.5 Results

**Theorem A (comparison; Lemma 3.1, Theorem 3.4).** Let `I`, `I'` be feasible
instances on one graph, `w` any cost vector and `P` any potential with
`nu0^{I'}(P) = F'`. With `alpha = a - 2a'`, `beta = b - 2b'`,
`Delta = hc - 2hc'`,

```
d_I(P) <= max_{A subseteq [p]} [ alpha(A) + sum_j max( L_A(j), G_A(j) - beta_j ) ],
L_A(j) = sum_{e in delta_A(j)} Delta_e^-,     G_A(j) = sum_{e in delta(j) - delta_A(j)} Delta_e^+.
```

**Theorem B (floor chain; Corollary 3.5, Proposition 3.6).** At every restart of
the floor chain and for every cost vector,

```
d_{I_f}(P) <= gamma_f + sum_i alpha_i max(1, deg(i) - 1) <= m0 max(q, 2),
```

with `alpha_i` the number of odd entries of `x_f` at `i` and `gamma_f` the number
of edges with `c^{(f)}_e` odd. The instances `T(s, D, B)` have restart deficit
`s D (D - 1) = (m0 - q)(q - 1)` at the potentials of the scaled schedule.
Conjecture 4.3 fails, for instance for `T(1, 7, 3)` (42 > 37), and for
`m0 >= 2q` the worst case of the floor chain is `Theta(m0 q)`.

**Theorem C (balanced chain; Corollary 3.7, Proposition 3.8).** At every restart
of the balanced chain and for every cost vector,

```
d_{I_f}(P) <= |{e : Delta_e != 0}| + |odd(O_f)| / 2 <= m0 + floor((p + q) / 2),
```

`odd(O_f)` the set of nodes of odd degree in `O_f`. The instances `R(k, q)`
(`p = k + 1` sources, `Q = q + 1` sinks) have restart deficit
`k q = m0 - p - Q + 1` on both chains. So Conjecture 4.3 holds for the
balanced chain, and its worst case is `m0 + O(p + q)`.

**Theorem D (B1; Theorem 5.1, Section 5.2).** For a feasible capacitated
transportation instance with `p` sources, `q` sinks and `m0` edges, and a
feasible flow with largest entry `U`, the scaled schedule on the balanced chain
with `X = m0 + floor((p+q)/2)` ends at `Psi = Opt` for every real cost vector
after at most `p (floor(m0^2/4) + 1) (m0 - 1 + ceil(log2 U) X)` PO-SL updates.
Each update is a signed tropical circuit of size polynomial in `m0` and `log U`.

## 3. Proofs

**Lemma 3.1 (compressed Rado formula).** Let `I` be feasible and `P in R^p`.
Then

```
d_I(P) = max_{A subseteq [p]} ( a(A) - r^v_I(A) ),     r^v_I(A) = sum_j g_j(A),
g_j(A) = sum_l [ min(b_j, hc(delta(j)_{<l}) + hc(delta_A(j)_{=l})) - min(b_j, hc(delta(j)_{<l})) ],
```

the inner sum over the values `l` of `v` on `delta(j)`.

*Proof.* Step 1, symmetry. A permutation of the slots of one source is an
automorphism of `M_I` and of the partition into blocks, and it fixes `v` at a
symmetric state; so it maps `M_I^v` to itself and fixes `Av(M_I^v)`. The group of
these permutations is transitive on the slots of each source, so
`Av(M_I^v)` is the set of slots of some `A* subseteq [p]`.

Step 2, Rado. Lemma `lem:avoidable`(1) and (2) for `N = M_I^v` give, for every
set `Q` of slots,

```
|Q| - r_N(E_Q) <= k - nu(N),     with equality at Q = Av(N).
```

For `Q` the slots of `A`, `|Q| = a(A)` and `E_Q = E_A`. With Step 1,

```
F - nu0^I(P) = a(A*) - r_N(E_{A*}) = max_{A subseteq [p]} ( a(A) - r_N(E_A) ).
```

Step 3, the rank. At sink `j` the set `{v < l} cup (E_A cap {v = l})` consists
of all copies of `delta(j)_{<l} cup delta_A(j)_{=l}`, whose rank is
`min(b_j, hc(delta(j)_{<l}) + hc(delta_A(j)_{=l}))`. Equation `(rank-mu)`,
summed over the sinks of the direct sum `M_I`, gives
`r_N(E_A) = sum_j g_j(A)`.

**Lemma 3.2 (one sink).** Let `Y` be a finite set with values `v in R^Y`,
capacities `kappa in Z^Y_{>=0}`, an integer `0 <= b <= kappa(Y)`, and
`A subseteq Y`, `Abar = Y - A`. Put

```
g(A; kappa, b) = sum_l [ min(b, kappa(Y_{<l}) + kappa(A_{=l})) - min(b, kappa(Y_{<l})) ],
phi(t)         = max( kappa(A_{<=t}), b - kappa(Abar_{<=t}) ),      t in R or t = -inf.
```

Then `g(A; kappa, b) = min_t phi(t)`.

*Proof.* Step 1, `g <= phi(t)` for every `t`. Each term of `g` is at most
`kappa(A_{=l})`, and, as `min(b, .)` is nondecreasing, at most
`min(b, kappa(Y_{<=l})) - min(b, kappa(Y_{<l}))`. With the first bound for
`l <= t`, the second for `l > t`, and `kappa(Y) >= b`,

```
g <= kappa(A_{<=t}) + sum_{l > t} [ min(b, kappa(Y_{<=l})) - min(b, kappa(Y_{<l})) ]
  =  kappa(A_{<=t}) + b - min(b, kappa(Y_{<=t}))
  =  kappa(A_{<=t}) + (b - kappa(Y_{<=t}))^+
  =  max( kappa(A_{<=t}), b - kappa(Abar_{<=t}) )  =  phi(t).
```

Step 2, equality. If `b = 0`, every term of `g` is `0` and `phi(-inf) = 0`. Let
`b >= 1` and `l*` the least value with `kappa(Y_{<=l*}) >= b`. The terms with
`l < l*` equal `kappa(A_{=l})` and those with `l > l*` vanish, so

```
g = kappa(A_{<l*}) + min( b - kappa(Y_{<l*}), kappa(A_{=l*}) ).
```

If the minimum is its first entry, take `t` with `Y_{<=t} = Y_{<l*}` (the
previous value, or `-inf`); since `kappa(Y_{<l*}) < b`,

```
phi(t) = max( kappa(A_{<l*}), b - kappa(Abar_{<l*}) ) = b - kappa(Abar_{<l*}) = g.
```

If it is the second entry, take `t = l*`; since `kappa(Y_{<=l*}) >= b`,

```
phi(l*) = max( kappa(A_{<=l*}), b - kappa(Abar_{<=l*}) ) = kappa(A_{<=l*}) = g.
```

**Lemma 3.3 (sink comparison).** In the setting of Lemma 3.2 let
`kappa, kappa' in Z^Y_{>=0}` and integers `0 <= b <= kappa(Y)`,
`0 <= b' <= kappa'(Y)`; put `Delta = kappa - 2 kappa'`, `beta = b - 2b'`,

```
L = sum_{e in A} Delta_e^-,     G = sum_{e in Abar} Delta_e^+.
```

Then `g(A; kappa, b) >= 2 g(A; kappa', b') - max(L, G - beta)`.

*Proof.* Step 1, both entries. For every `t`,

```
kappa(A_{<=t})        =  2 kappa'(A_{<=t}) + Delta(A_{<=t})                               >=  2 kappa'(A_{<=t}) - L,
b - kappa(Abar_{<=t}) =  2 (b' - kappa'(Abar_{<=t})) + beta - Delta(Abar_{<=t})           >=  2 (b' - kappa'(Abar_{<=t})) - (G - beta).
```

Step 2, the maxima. With `phi'` the function of Lemma 3.2 for `(kappa', b')` and
`max(x - s, y - s') >= max(x, y) - max(s, s')`,

```
phi(t) >= 2 phi'(t) - max(L, G - beta)      for every t.
```

Step 3, the minima. Lemma 3.2 for both capacity vectors gives

```
g(A; kappa, b) = min_t phi(t) >= 2 min_t phi'(t) - max(L, G - beta) = 2 g(A; kappa', b') - max(L, G - beta).
```

**Theorem 3.4 (comparison).** Let `I = (a, b, c)` and `I' = (a', b', c')` be
feasible instances on the same graph `H`, `w` a cost vector and `P` a potential
with `nu0^{I'}(P) = F'`. With `alpha = a - 2a'`, `beta = b - 2b'`,
`Delta = hc - 2hc'` and `L_A(j)`, `G_A(j)` as in Theorem A, for every
`A subseteq [p]`

```
a(A) - r^v_I(A) <= alpha(A) + sum_j max( L_A(j), G_A(j) - beta_j ),
```

and `d_I(P)` is at most the maximum of the right side over `A`.

*Proof.* Step 1, the coarse instance. Lemma 3.1 for `I'` and `d_{I'}(P) = 0`
give `a'(A) <= r^v_{I'}(A) = sum_j g'_j(A)` for every `A`.

Step 2, splitting. Since `a = 2a' + alpha`,

```
a(A) - r^v_I(A) = 2 a'(A) + alpha(A) - sum_j g_j(A) <= alpha(A) + sum_j ( 2 g'_j(A) - g_j(A) ).
```

Step 3, sink by sink. At sink `j`, `g_j(A)` and `g'_j(A)` are the functions of
Lemma 3.2 on `Y = delta(j)` with the set `delta_A(j)` and the data
`(hc, b_j)`, `(hc', b'_j)`; feasibility gives `b_j <= hc(delta(j))` and
`b'_j <= hc'(delta(j))`. Lemma 3.3 gives

```
2 g'_j(A) - g_j(A) <= max( L_A(j), G_A(j) - beta_j ).
```

Step 4. Steps 2 and 3 give the displayed bound, and Lemma 3.1 for `I` gives the
bound on `d_I(P)`.

*Remark (refinement).* The minimum in Lemma 3.2 for `I` is attained at a `t`
with `Y_{<=t} = Y_{<l*}` or `t = l*`, `l*` the threshold of the sink in `I`;
running Step 3 of Lemma 3.3 at that `t` shows that only edges with
`v_e <= l*` enter `L_A(j)` and `G_A(j)`.

**Corollary 3.5 (floor chain).** Let `I = I_f` and `I' = I_{f+1}` be consecutive
members of the floor chain, `o(u)` the number of odd entries of `x_f` at a node
`u`, `deg(i)` the degree of source `i` in `H`, and `gamma(A)` the number of
edges `e in delta(A)` with `c_e` finite and odd and `c'_e <= a'_{i(e)}`. Then
`alpha_i = o(i)`, `beta_j = o(j)`, and for every `A`, every cost vector and
every `P` with `nu0^{I'}(P) = F'`

```
a(A) - r^v_I(A) <= alpha(A) + gamma(A) + sum_{i notin A} alpha_i (deg(i) - 1).
```

Consequently, with `gamma` the number of edges with `c_e` finite and odd,

```
d_I(P) <= gamma + sum_i alpha_i max(1, deg(i) - 1) <= m0 max(q, 2).
```

*Proof.* Step 1, `alpha` and `beta`. At a source `i`,

```
a_i = sum_j x_ij = sum_j ( 2 floor(x_ij / 2) + (x_ij mod 2) ) = 2 a'_i + o(i),
```

and likewise `b_j = 2b'_j + o(j)`.

Step 2, the edges. Let `e = (i, j)` and `gamma_e = c_e mod 2` (`0` if
`c_e = inf`), so `c_e = 2c'_e - gamma_e`. If `c'_e <= a'_i`, then
`2c'_e - gamma_e <= 2a'_i <= a_i` and

```
Delta_e = min(2c'_e - gamma_e, a_i) - 2 min(c'_e, a'_i) = (2c'_e - gamma_e) - 2c'_e = -gamma_e.
```

If `c'_e > a'_i` (in particular if `c_e = inf`), then
`c_e - 2a'_i >= 2(a'_i + 1) - 1 - 2a'_i = 1` and

```
Delta_e = min(c_e, 2a'_i + alpha_i) - 2a'_i = min(c_e - 2a'_i, alpha_i),      0 <= Delta_e <= alpha_i.
```

Step 3, losses. By Step 2, `Delta_e^- = gamma_e [c'_e <= a'_{i(e)}]`, so
`sum_j L_A(j) = gamma(A)`.

Step 4, gains against odd entries. Since `beta_j = o(j)` counts at least the odd
entries `x_ij`, `i notin A`, and `(sum y)^+ <= sum y^+`,

```
(G_A(j) - beta_j)^+ <= ( sum_{i notin A, ij in E_H} ( Delta_ij^+ - [x_ij odd] ) )^+
                    <= sum_{i notin A, ij in E_H} ( Delta_ij^+ - [x_ij odd] )^+.
```

Step 5, one source. For `i notin A`, Step 2 gives `Delta_ij^+ <= alpha_i` on every
edge; the `alpha_i` odd edges contribute at most `alpha_i - 1` each and the other
`deg(i) - alpha_i` edges at most `alpha_i` each:

```
sum_j ( Delta_ij^+ - [x_ij odd] )^+ <= alpha_i (alpha_i - 1) + (deg(i) - alpha_i) alpha_i = alpha_i (deg(i) - 1).
```

Step 6, assembling. Theorem 3.4 with `max(L, G - beta) <= L + (G - beta)^+` and
Steps 3 to 5 give the first display. Since `alpha_i <= deg(i) <= q` and
`sum_i deg(i) = m0`,

```
alpha(A) + gamma(A) + sum_{i notin A} alpha_i (deg(i) - 1)
   <= gamma + sum_i alpha_i max(1, deg(i) - 1)
   <= m0 + sum_i deg(i) max(1, q - 1)  =  m0 max(q, 2).
```

**Proposition 3.6 (the floor chain needs `(m0 - q)(q - 1)`).** For integers
`s >= 1`, `D >= 2` and `B >= 1` with `s D <= 2B + s`, let `T(s, D, B)` have sources
`0` and `1, ..., s`, sinks `1, ..., D`, and for every sink `j` and `t >= 1`

```
x_0(0, j) = 2B,   c(0, j) = 2B,   w(0, j) = 1;        x_0(t, j) = 1,   c(t, j) = D,   w(t, j) = 0.
```

So `a = (2BD, D, ..., D)`, `b_j = 2B + s`, `p = s + 1`, `q = D`,
`m0 = (s + 1) D`. On the floor chain the scaled schedule restarts `I_0` at
`P = 0`, and

```
d_{I_0}(0) = s D (D - 1) = (m0 - q)(q - 1).
```

It exceeds `p + q + 2 m0 = (s + 1)(2D + 1) + D` whenever
`s D (D - 1) > (s + 1)(2D + 1) + D`, for instance at `T(1, 7, 3)` (42 > 37),
`T(2, 5, 4)` (40 > 38), `T(5, 4, 8)` (60 > 58).

*Proof.* Step 1, the chain. `x_1(0, j) = B` and `x_1(t, j) = 0`; for every
`g >= 1` only source `0` has supply, `a^{(g)}_0 = D B_g` and `b^{(g)}_j = B_g`
with `B_g = floor(B / 2^{g-1})`.

Step 2, the coarse phases do not move. In `I_g`, `g >= 1`, the edges `(t, j)`
have `hc = min(c, 0) = 0`, and `(0, j)` has
`hc = min(ceil(2B / 2^g), D B_g) >= B_g`. At `P = 0` every minimum base takes
`B_g` copies of `(0, j)` at every sink, `D B_g = F_g` copies in all, which can be
given distinct slots of source `0`: `nu0 = F_g`. So no update occurs in phases
`J, ..., 1`, and `I_0` restarts at `P = 0`, `v = w`.

Step 3, the deficit from below. At sink `j` of `I_0`, the `s` new edges at value
`0` offer `min(D, D) = D` units each, the old edge at value `1` offers `2B`, and
`s D <= b_j = 2B + s < s D + 2B`. The formula of Lemma 3.1 at sink `j` with
`A = {0}` has a term `0` at the value `0` and, at the value `1`,

```
g_j({0}) = min(b_j, s D + 2B) - min(b_j, s D) = b_j - s D = 2B + s - s D,
d_{I_0}(0) >= a_0 - r^v({0}) = 2BD - D (2B + s - s D) = s D (D - 1).
```

Step 4, the deficit from above. In Corollary 3.5, `gamma(A) = 0` (the capacities
`2B` are even, and the edges `(t, j)` have `c' = ceil(D/2) > 0 = a'_t`),
`alpha_0 = 0` and `alpha_t = D = deg(t)` for `t >= 1`, so for every `A`

```
alpha(A) + gamma(A) + sum_{i notin A} alpha_i (deg(i) - 1) = sum_{t in A, t >= 1} D + sum_{t notin A, t >= 1} D (D - 1) <= s D (D - 1).
```

Step 5, the count. `m0 - q = s D` and `q - 1 = D - 1`.

**Corollary 3.7 (balanced chain).** Let `I = I_f` and `I' = I_{f+1}` be
consecutive members of the balanced chain. Then
1. `alpha_i = in(i) - out(i)` and `beta_j = out(j) - in(j)` in `O_f`, all in
   `{-1, 0, 1}`, and `|{i : alpha_i = 1}| + |{j : beta_j = -1}| = |odd(O_f)| / 2`;
2. `Delta_e in {-1, 0, 1}` for every edge;
3. for every cost vector and every `P` with `nu0^{I'}(P) = F'`,
   `d_I(P) <= |{e : Delta_e != 0}| + |odd(O_f)| / 2 <= m0 + floor((p + q) / 2)`.

*Proof.* Step 1, item 1. At a source `i` the rounded-up entries are the edges of
`O_f` oriented out of `i`, and at a sink `j` those oriented into `j`:

```
a_i - 2a'_i = o(i) - 2 out(i) = in(i) - out(i),        b_j - 2b'_j = o(j) - 2 in(j) = out(j) - in(j).
```

A node has `|in - out| = 1` exactly when its degree in `O_f` is odd, and
`sum_u (in(u) - out(u)) = 0`, so half of the odd-degree nodes have
`in - out = 1`; these are the sources with `alpha_i = 1` and the sinks with
`beta_j = -1`.

Step 2, item 2. Let `e = (i, j)`, `c_e = 2c'_e - gamma_e`, and
`a_i = 2a'_i + alpha_i` with `alpha_i in {-1, 0, 1}` (`alpha_i >= 0` if
`a'_i = 0`). Then

```
c'_e <  a'_i :   2c'_e - gamma_e <= 2a'_i - 2 < a_i,                 Delta_e = -gamma_e,
c'_e =  a'_i :   Delta_e = min(2a'_i - gamma_e, 2a'_i + alpha_i) - 2a'_i = min(-gamma_e, alpha_i),
c'_e >  a'_i :   c_e >= 2a'_i + 1 >= a_i,                           Delta_e = a_i - 2a'_i = alpha_i,
```

and `c_e = inf` falls in the last case.

Step 3, item 3. By item 2, `L_A(j)` counts the edges of `delta_A(j)` with
`Delta_e = -1` and `G_A(j)` the other edges of `delta(j)` with `Delta_e = 1`, so

```
max( L_A(j), G_A(j) - beta_j ) <= |{e in delta(j) : Delta_e != 0}| + [beta_j = -1],
```

and `alpha(A) <= |{i : alpha_i = 1}|`. Theorem 3.4 and item 1 give

```
d_I(P) <= |{i : alpha_i = 1}| + |{j : beta_j = -1}| + |{e : Delta_e != 0}|
        = |{e : Delta_e != 0}| + |odd(O_f)| / 2  <=  m0 + floor((p + q) / 2).
```

**Proposition 3.8 (capacity rounding forces about `m0` on both chains).** For
integers `k, q >= 1` and `H > 0` let `R(k, q)` have sources `0` and the set
`A = {1, ..., k}`, sinks `0` and `1, ..., q` (complete bipartite,
`p = k + 1`, `Q = q + 1`, `m0 = p Q`), and for `i in A`, `j >= 1`

```
x(i, j) = 2,    c(i, j) = 3,     w(i, j) = 0;       x(i, 0) = 2q,   c(i, 0) = 2q,   w(i, 0) = H;
x(0, j) = 2k,   c(0, j) = 2k,    w(0, j) = H;       x(0, 0) = 0,    c(0, 0) = inf,  w(0, 0) = 0.
```

Both chains give the same `I_1`, and for every optimal Lagrange multiplier `P` of
`I_1` with `P_i < P_0 + H` for all `i in A` (for instance `P = 0`)

```
d_{I_0}(P) = k q = m0 - p - Q + 1.
```

For `k = q = 2^L` the floor chain's scaled schedule restarts `I_0` at `P = 0`.

*Proof.* Step 1, the first halving. `x` is even, so both chains give
`x_1 = x / 2` and `alpha = beta = 0`:

```
a'_i = 2q (i in A),  a'_0 = kq,  b'_j = 2k (j >= 1),  b'_0 = kq,
c'(i, j) = 2,  c'(i, 0) = q,  c'(0, j) = k,  c'(0, 0) = inf.
```

Step 2, the multipliers of `I_1`. The costs are nonnegative, and a flow of cost
`0` uses only the edges `(i, j)`, `i in A`, `j >= 1`, and `(0, 0)`; the sinks
`j >= 1` then force `y'(i, j) = 2 = c'(i, j)`. So the unique optimal flow is `y'`
with `y'(i, j) = 2`, `y'(0, 0) = kq`, and by Proposition 2.2 (items 2 and 3) `P`
is optimal if and only if `y'` is a cheapest fill. At a sink `j >= 1`, `y'` takes
all `2k = b'_j` units of `A`, which requires

```
v(i, j) = -P_i <= H - P_0 = v(0, j),     that is   P_i >= P_0 - H     (i in A).
```

Step 3, the restart. In `I_0`, `hc(i, j) = 3`, `hc(0, 0) = a_0 = 2kq = b_0` and
`b_j = 4k`. At a sink `j >= 1`, the units of `A` lie at values
`-P_i <= H - P_0` and number `3k < 4k`, so all of them lie at or below the
threshold and `g_j(A) = 3k`. At sink `0`, the edge `(0, 0)` alone fills
`b_0 = 2kq` at value `-P_0 < H - P_i`, so `g_0(A) = 0`. With `a(A) = 4kq`,

```
d_{I_0}(P) >= a(A) - r^v(A) = 4kq - q (3k) = kq.
```

Step 4, the upper bound. `Delta(i, j) = 3 - 4 = -1` for `i in A`, `j >= 1`, and
`Delta = 0` on the other edges (`hc(i, 0) = 2q = 2 hc'(i, 0)`,
`hc(0, j) = 2k = 2 hc'(0, j)`, `hc(0, 0) = 2kq = 2 hc'(0, 0)`). Theorem 3.4 with
`alpha = beta = 0` gives, for every set `A'` of sources,

```
a(A') - r^v(A') <= sum_{j >= 1} L_{A'}(j) <= sum_{j >= 1} k = kq.
```

Step 5, the schedule for `k = q = 2^L` on the floor chain. For
`2 <= g <= L + 1`, `x_g(i, j) = 0`, `x_g(i, 0) = q / 2^{g-1}`,
`x_g(0, j) = k / 2^{g-1}`, `c_g(i, j) = 1`, so with `K_g = k / 2^{g-1}`:
`a_g(i) = K_g` (`i in A`), `a_g(0) = q K_g`, `b_g(j) = K_g`, `b_g(0) = k K_g`. At
`P = 0` each sink `j >= 1` holds `k >= K_g` units of `A` at value `0` and sink `0`
holds `a_g(0) = q K_g = b_g(0)` units of `(0, 0)` at value `0`; a `K_g`-regular
bipartite graph between `A` and the sinks `1..q` gives a rainbow cheapest fill,
so `nu0 = F_g`. The same holds at `g = 1` by Step 2 with `P = 0`. No update
occurs before the restart of `I_0`.

Step 6, the count. `m0 - p - Q + 1 = (k + 1)(q + 1) - (k + 1) - (q + 1) + 1 = kq`.

## 4. Computations

All scripts are in `experiments/`, exact integer arithmetic, at most 6 worker
processes, every search time-bounded. They reuse `stage_transport_fast.Transport`
(type-compressed PO-SL, `nu0` and `Av` by max flow) and
`stage_transport.build` (uncompressed rainbow form).

| script | what it checks | result |
|---|---|---|
| `b1_core.py` | chains (floor, balanced), `r^v` from `(rank-mu)`, Lemma 3.2 both sides, Theorem 3.4 terms, scaled schedule | helpers |
| `b1_counterexample.py` | Proposition 3.6: `T(s, D, B)` for 11 parameter sets, deficit by max flow and by Lemma 3.1, schedule potential, uncompressed form on `T(1, 3, 1)`, static schedule with `X` | deficit `= s D (D - 1)` in all 11 (max flow = Rado = Theorem 3.4 bound); 8 violate `X`; `P = 0` at every restart; uncompressed `nu0 = 3`, deficit 6 on `T(1,3,1)` |
| `b1_checks.py 6 4` | Part A: Lemma 3.2 and Lemma 3.3 on 153,300 (sink, set) cases; Part B: Lemma 3.1 (max flow = Rado) and Theorem 3.4 for every `A` on 1,440 random pairs `(I, I')` (10,778 sets), `P` from the schedule of `I'` started at random states; Part C: Theorem 3.4, Corollary 3.5 for every `A`, Corollary 3.7, on 1,416 floor and 1,797 balanced restarts of 600 random instances (1,200 chains) | no failure. Discrimination: the variants V1 (`L` only) fail 25,114 times, V2 (`G - beta` only) 24,544, V3 (`min` for `max`) 49,658, V4 (`G - 2 beta`) 373; Theorem 3.4 without `alpha(A)` fails on 84 sets. Theorem 3.4 is tight at 19 of the 1,440 pairs |
| `b1_scaled.py 6 120` | Theorem 5.1: 720 random instances (up to `5 x 5`, `U` up to 1,000, costs up to 20 bits, negative costs), both chains with the proven `X`, 6,401 restarts; the finer bounds of Corollaries 3.5 and 3.7 at each restart; uncompressed cross-check of Lemma 3.1 on 339 small instances | no restart above `X` or above the finer bound; `Psi = Opt` at the end of all 1,440 runs; at most 12 (floor) and 14 (balanced) updates in total; Lemma 3.1 agrees with the uncompressed `nu0` in all 339 |
| `b1_lower_linear.py` | Proposition 3.8: `R(k, q)` for 9 parameter sets and `R(8, 8)` (`m0 = 81`), both chains, real schedule | deficit `= kq` in all, both chains; at `R(8, 8)` both schedules restart `I_0` at `P = 0` (deficit 64) |
| `b1_mincostflow.py` | Proposition 5.3: random digraphs (`n <= 4`, `m <= 6`), the reduction `T(D)`, the scaled schedule on both chains (floor with `X = 2m`); reference: brute force over all integral flows of `D` (capacities `<= 3`), or with `B1_BIGU=1` capacities up to 1,000 and the exact min-cost flow of `T(D)` | 360 + 360 digraphs, 194 + 1,930 floor restarts: no deficit above `|O_f|` or `2m`; the final value equals the minimum cost in all 1,440 runs |
| `b1_search.py`, `b1_analyze.py` | hill climbing for large restart deficits (balanced chain), and the dissection of one restart | `3 x 3`: 6 (`m0 = 9`); `2 x 4`: 4 (`m0 = 8`); `4 x 4`: 11 (`m0 = 16`), attained by Theorem 3.4 at `A = {0, 1, 3}` |

Logs: `experiments/b1_logs/` (`counterexample.txt`, `lower_linear.txt`,
`lower_linear_8_8.txt`, `checks_scale4.txt`, `scaled_120.txt`,
`mincostflow_small.txt`, `mincostflow_bigU.txt`, `search_*.txt`). The earlier smaller runs (`b1_checks.py 6 1`,
`b1_scaled.py 6 40`) are contained in these, as they use the same seeds.

The side observation of Section 1: with `X = p + q + 2 m0` the static schedule
skips active stages on the counterexamples of Proposition 3.6, and the first
stage it runs starts at `nu0 < r`; on all 8 violating members the final `Psi`
still equals `Opt` and `nu0 = F` (`b1_counterexample.py`, column "static
scaled schedule"). A trace of `T(1, 7, 3)`, `T(2, 5, 4)`, `T(1, 8, 4)` (restart
at `nu0 = 7, 10, 16`, first stage `r = 12, 12, 30`) shows one update with
`tau = 1` raising source `0` by `1`, after which `nu0 = F`: the levels are
`{0, 1}`, so the update of stage `r` equals that of stage `nu0`.
`b1_static_fail.py` (circuit-faithful blocks, the block of stage `r` computing
the threshold integral at any state; hill climbing over costs and old-source
flows of `T`-like instances, 8 minutes, 6 workers) found restart deficits up to
84 against `X = 52`, and the static schedule with `X = p + q + 2 m0` still ended
at `Opt` every time.

### 4.1 Exploratory: the last-stage block alone

The circuit block of stage `r` computes
`eta_b = sum over levels l_i < tau_r of (l_{i+1} - l_i) [b in Av(N(l_i))]`, at
any state. For `r = k - 1` (`tau = ` the first level with `nu(N(t)) = k`), iterate
this block alone from `p = 0` until `nu0 = k`:

| script | instances | result |
|---|---|---|
| `b1_laststage_general.py 6 40` | 240 random graphic, binary, uniform matroids, `m <= 10`, Opt by brute force | `Opt` in all 240, `nu0` never decreased, at most 5 updates (regular schedule: at most 5; totals 205 against 221) |
| ladder of Theorem 2.5, `L = 0..10`; the four long instances of phase 2b, Section 2.6 | `k = 3, 4, 5`, stages up to 13 | `Opt` in all; updates equal to the regular schedule, or one fewer when an earlier stage is absorbed (8 against 9, 7 against 8) |
| `b1_laststage_search.py 420 6` | hill climbing (midpoint and doubling moves) for a decrease of `nu0`, a stuck run, a wrong value, or many more updates than the regular schedule; graphic, 5 and 6 vertices | no failure; at most 2 updates more than the regular schedule |
| `b1_laststage.py 6 25`, and `U` up to `2^14` | 147 + 160 random transportation instances (`F` up to 136,639), `T(1,7,3)`, `T(2,6,5)`, `R(4,4)`, `R(8,8)`; also the balanced chain with only the last stage per phase | `Opt` in all, `nu0` never decreased, at most 4 updates without any scaling (1 on the families) |

Logs: `b1_logs/laststage*.txt`, `b1_logs/static_fail.txt`.

## 5. Consequences for B1

### 5.1 The schedule

**Theorem 5.1.** Let `I = (a, b, c)` be a feasible capacitated transportation
instance with `p` sources, `q` sinks and `m0` edges, `x_0` a feasible flow with
`U = max_e x_0(e) >= 1`, and `I_0, ..., I_J` its balanced chain. Put
`X = m0 + floor((p + q)/2)` and `K = p (floor(m0^2/4) + 1)`. The static schedule

- phase `J`: from `P = 0`, stages `r = 1, ..., F_J - 1`;
- phase `f = J - 1, ..., 0`: from the potential of phase `f + 1`, stages
  `r = max(1, F_f - X), ..., F_f - 1`;
- every stage: `K` applications of the PO-SL update of stage `r` for `I_f`;

ends at a potential `P` with `Psi^I(P) = Opt(I)` for every real cost vector
`w`, after at most

```
K ( F_J - 1 + J X ) <= p (floor(m0^2/4) + 1) ( m0 - 1 + ceil(log2 U) (m0 + floor((p + q)/2)) )
```

update applications, which is `O(p m0^3 log U)` when `H` has no isolated node.
With the floor chain the same holds with `X = m0 max(q, 2)`, which gives
`O(p q m0^3 log U)`.

*Proof.* Step 1, phase `J`. `F_J >= 1` (the chain stops at the first member with
`max x <= 1`, and `max x_{J-1} >= 2` when `J >= 1`), and at `P = 0` a minimum base
of `M_{I_J}` is nonempty and meets a block, so `nu0 >= 1`.

Step 2, one phase. Let a phase start with `nu0 >= r_0`, `r_0` its first stage.
By induction on `r`, every stage starts with `nu0 >= r`: an application at
`nu0 > r` is the identity (`a = 0` in Definition `def:update`), `nu0` never
decreases (Theorem `thm:validity`(2)), and by Theorem 4.2 at most `K` updates
occur at `nu0 = r` before `nu0 > r`. So the phase ends with `nu0 = F_f`.

Step 3, the restarts. At the end of phase `f + 1`, `nu0^{I_{f+1}}(P) = F_{f+1}`
by Step 2, and Corollary 3.7 gives `d_{I_f}(P) <= X`, that is
`nu0^{I_f}(P) >= F_f - X`, which is Step 2's hypothesis for phase `f`.

Step 4, the output. After phase `0`, `nu0^{I}(P) = F` and Lemma `lem:duality`
gives `Psi^I(P) = Opt(I)`.

Step 5, the count. Phase `J` has `F_J - 1 <= m0 - 1` stages
(`x_J in {0, 1}^{E_H}`), every other phase at most `X`, and `J <= ceil(log2 U)`
(Section 2.4). Without isolated nodes `p + q <= 2 m0`, so `X <= 2 m0`. For the
floor chain replace Corollary 3.7 by Corollary 3.5.

The static schedule without scaling has `F - 1` stages, and `F` can be as
large as `m0 U`; the scaled one has at most `m0 - 1 + ceil(log2 U) X`.

### 5.2 The circuit

The circuit has the cost vector `w in R^{E_H}` as its only input. Everything
else is fixed data, computed once by the generator: a feasible flow `x_0` (max
flow), the balanced chain `I_0, ..., I_J` (halvings and Euler-type
orientations), the numbers `F_f`, `X`, `K`. The circuit is the sequence of update
blocks of Theorem 5.1, phase by phase; the block for `(f, r)` has the data of
`I_f` and the integer `r` hardwired. The per-source potential `P` (`p` real
wires) passes from block to block, and each block recomputes
`v_e = w_e - P_{i(e)}` (`m0` gates). The instances `I_f` never depend on `w`,
which is why the schedule is static.

**One update (typed version of Lemma `lem:oneupdate`).** By Proposition 4.1 the
PO-SL family at a symmetric state is determined by the relation
`G_t = {(e, f) : v_f - v_e <= t}` on the `m0` edge types, and the update is
`eta_i = int_0^inf F_i(G_t) dt` with
`F_i = [nu(N(t)) <= r] and [i in Av(N(t))]` (equation `(update-integral)`). So
Theorem `thm:compiler` on the `m0^2` ordered pairs of types, with
`D^+_{ef} = max(v_f - v_e, 0)` (`2 m0^2` gates) and `N = p` outputs, computes
`eta` with `3 m0^2 s + m0^2 p + 6 m0^4` gates from a Boolean observer of size
`s`. At `nu0 > r`, `nu(N(t)) > r` for all `t`, so the block is the identity.

**The observer.** From the bits of a relation `G` on types, at `G = G_t`:
1. `e in PO_t` iff `sum_{f in delta(j(e)), (f, e) notin G} hc_f < b_{j(e)}`:
   selected sums of hardwired integers and one comparison per edge.
2. Clusters: linkage bits `[(e,f) in G] and [(f,e) in G]` on the PO edges of
   each sink, closed by Warshall's algorithm (`O(sum_j deg(j)^3)` gates); the
   cluster order and the capacities `b_j - min(b_j, hc(lower clusters))` follow as
   in Step 2 of Lemma `lem:observer`.
3. `nu(N(t))` is the value of a maximum flow in the network
   `S -> i (a_i) -> e (hc_e, PO edges) -> cluster of e (hc_e) -> T (cluster capacity)`
   (Proposition 4.1, with `c_e` replaced by `hc_e`, which changes no flow), on
   `n_N = p + 2 m0 + 2` nodes (a cluster is represented by its least edge) and
   `a_N <= p + 2 m0 + sum_j deg(j)^2` arcs whose integer capacities, all at most
   `F <= m0 U`, are selected by the bits of steps 1 and 2.
4. A maximum flow by Edmonds and Karp: at most `n_N a_N` augmentations along
   shortest residual paths, each unrolled into a Boolean circuit (breadth-first
   layering in `n_N` rounds, path extraction, bottleneck, residual update) of
   `O(n_N a_N + a_N lambda)` gates, `lambda = O(log(m0 U))` the bit length of
   the capacities and of `F`. Total `O(n_N a_N (n_N a_N + a_N lambda))`.
5. `Av(N(t))` is the set of sources reachable from `S` in the final residual
   network (Proposition 4.1, Step 4), `O(n_N a_N)` gates, and `[nu <= r]` is one
   comparison of `lambda`-bit integers.

With `p <= m0` and `sum_j deg(j)^2 <= p m0` this is
`s = O(m0^3 p^2 (m0 + lambda))`, so one update costs
`O(m0^5 p^2 (m0 + log(m0 U)))` gates, and the whole schedule
`O(p^3 m0^8 (m0 + log(m0 U)) log U)` gates. The exponents are a crude count.
The capacities enter only as hardwired binary integers, through `lambda`.

**The output (integer rank, Corollary `cor:integer`).**
`Psi^I(P) = sum_i a_i P_i + beta(v)` with `beta(v)` the cheapest fill of all
sinks, `beta(v) = -h(-v)` for the polymatroid rank on edge types

```
rho(Y) = sum_j min(b_j, hc(Y cap delta(j))),     rho(E_H) = F,
```

and `h(u) = mu F + int_0^inf rho({e : u_e - mu > t}) dt`, `mu = min_e u_e`
(Lemma `lem:greedy` on the copies, which are constant on types). `rho` is an
integer with `lambda` bits and has a Boolean circuit of `O(m0 lambda)` gates, so
Corollary `cor:integer` computes `h` with `O(m0^2 lambda)` gates; `mu F` and
`sum_i a_i P_i` cost `O(p lambda)` gates by doubling.

**What is still missing.** Nothing conceptual for transportation: the deficit
bound was the missing step, and the balanced chain supplies it (Corollary 3.7).
To be written out: (i) the typed observer as a lemma with a proof, including the
component structure of Proposition 4.1, Step 3 (a sink with
`hc(delta(j)) = b_j` splits into per-edge components, a sink with `b_j = 0` into
loops) and the unrolled Edmonds-Karp circuit; (ii) the typed versions of
`lem:oneupdate` and `lem:greedy` (immediate, as all sublevel sets are unions of
types); (iii) uniformity of the generator (max flow and Euler orientations,
polynomial time). With these, the minimum cost of a capacitated transportation
problem with fixed integer data has uniform signed tropical circuits of size
polynomial in `m0` and `log U`.

### 5.3 General min-cost flow

**Proposition 5.3.** Let `D = (V, Arcs)` be a digraph without loops, `n = |V|`,
`m = |Arcs|`, with integer capacities `u_a >= 0`, `U = max u_a`, and integer
demands `d_v` (net inflow, `sum d = 0`) admitting a feasible flow. Let `T(D)` be
the transportation instance with one source per arc `a` (supply `u_a`), one sink
per node `v` (demand `d_v + u(delta^out(v))`), and for `a = (s, t)` the two
uncapacitated edges `(a, t)` of cost `w_a` and `(a, s)` of cost `0`. Then
1. `phi -> y`, `y(a, t) = phi_a`, `y(a, s) = u_a - phi_a`, is a cost-preserving
   bijection between the feasible flows of `D` and of `T(D)`;
2. on the floor chain of `T(D)` every restart deficit is at most `|O_f| <= 2m`;
3. the scaled schedule with `X = 2m` ends at the minimum cost after at most
   `m (m^2 + 1) (2m - 1 + 2m ceil(log2 U))` updates, and the minimum cost of a
   flow, as a function of the real costs `w`, has uniform signed tropical
   circuits of size polynomial in `m` and `log U`.

*Proof.* Step 1, item 1. Sink `v` receives
`sum_{a in delta^in(v)} phi_a + sum_{a in delta^out(v)} (u_a - phi_a) = d_v + u(delta^out(v))`
exactly when `phi` satisfies the demand at `v`, and `0 <= phi <= u` is
`y >= 0`; only `y(a, t) = phi_a` carries cost.

Step 2, item 2. In `T(D)` every edge is uncapacitated, so `gamma(A) = 0`, and
every source has degree 2. Corollary 3.5 gives, for every `A`,

```
a(A) - r^v(A) <= alpha(A) + sum_{a notin A} alpha_a (2 - 1) = sum_a alpha_a = |O_f| <= 2m.
```

Step 3, item 3. Theorem 5.1 with the floor chain, `X = 2m`, `p = m`, `m0 = 2m`,
`K = m (m^2 + 1)`, `x_0 <= U`, and Section 5.2 on `T(D)`.

This covers the entry "min-cost flow, costs variable" of the open-problem map
(`docs/research-direction-2026-10-11.md`, Section 2), with size polynomial in
`m` and `log U`; the size depends on `log U`, so it is not strongly polynomial.

### 5.4 Polymatroid intersection with a generalized partition matroid

Setting: types `E` (`|E| = m0`) split into blocks `E_1, ..., E_p` with supplies
`a_i` (the generalized partition matroid, here with `y(E_i) = a_i`), and an
integer polymatroid `f` on `E` with `f(E) = F = sum a_i`; the problem is the
least `w . y` over integral `y` in the base polytope of `f` with
`y(E_i) = a_i`. The rainbow form takes `a_{i(e)}` copies of each type, the slots
as blocks, and `M` the matroid induced by `f` on the copies,
`r(Z) = min_{T subseteq E} ( f(T) + |Z - copies(T)| )`.

**Network polymatroids reduce to Proposition 5.3.** If `f(Y)` is the value of a
maximum flow from the entry nodes of the types in `Y` to a sink `T` in a network
with integer arc capacities (laminar polymatroids are the case of a tree, and
transportation the case of one level), then the integral `y` of the problem are
the integral flows of value `F` in the network
`S -> block i (a_i) -> type e (uncapacitated) -> network -> T`, with cost `w_e`
on the arc `i -> e`. This is a min-cost flow problem with fixed integer data on
`p + m0 + (arcs of the network)` arcs, so Proposition 5.3 gives signed tropical
circuits of size polynomial in that number and in `log U`.

**Beyond networks.** What carries over verbatim:
- Proposition 4.1, Step 1 (symmetry), so the schedule acts on `P in R^p`.
- Theorem 4.2: a stage takes at most `p (floor(m0^2/4) + 1)` updates (its proof
  uses only that the copies of a type share their value and that `S0` is a
  union of the slot sets of whole blocks `E_i`).
- Lemma 3.1, Steps 1 and 2: `F - nu0 = max_A ( a(A) - r_{M^v}(E_A) )`.
- Theorem 3.4, Steps 1 and 2: the deficit of `I` at a potential solving `I'` is
  at most `max_A [ alpha(A) + ( 2 r_{M'^v}(E_A) - r_{M^v}(E_A) ) ]`.

What is missing: (a) a halving `f -> f'` of the polymatroid under which
`2 r_{M'^v}(E_A) - r_{M^v}(E_A)` is bounded independently of the number of
value levels. Lemma 3.3 does this for transportation through the min-max form of
Lemma 3.2; a perturbation of `f` by `epsilon` on every set gives only a loss of
`2 epsilon` per value level through `(rank-mu)`, which is not enough. (b) An
observer: `nu(N(t))` is a polymatroid intersection of the typed `N(t)` with the
partition side, and it must be a Boolean circuit polynomial in `m0` and `log U`;
for network polymatroids it is a maximum flow, in general it needs a strongly
polynomial polymatroid intersection unrolled into a circuit.

## 6. Open steps

1. **Write the typed observer** (Section 5.2, items (i) to (iii)). Routine, and
   then B1 for transportation and for min-cost flow is complete.
2. **The constant for the balanced chain.** The worst restart deficit lies
   between `m0 - p - q + 1` (Proposition 3.8, `q` here the number of sinks) and
   `m0 + floor((p + q)/2)` (Corollary 3.7); search found 11 at `p = q = 4`,
   `m0 = 16`.
3. **A chain with deficit `O(p + q)`.** Capacity rounding is the `m0` term
   (Proposition 3.8, where `alpha = beta = 0`). Rounding some capacities down
   (`floor(c / 2)` where `x_{f+1}` allows it) turns losses into gains; whether a
   choice keeps both small for all sets `A` is open. It would save a factor
   `m0 / (p + q)` in Theorem 5.1, nothing more.
4. **The last-stage block (most promising).** Conjecture: for PO-SL and every
   state, the block of stage `k - 1` does not decrease `nu0`, and its iteration
   from any state reaches `nu0 = k` after a number of updates bounded by a
   polynomial in `m` (in `m0` for transportation), independent of `F`.
   Evidence: Section 4.1. What is known: on `[0, tau_{nu0})` the block follows
   the stage-`nu0` update, so Theorem `thm:validity` applies there; beyond, the
   rate of `Psi` is still at least `k - nu(N(s)) >= 1` (Steps 1 to 3 of
   Theorem `thm:validity` with Lemma `lem:path`), but the argument of Step 4
   (an old base stays minimum) no longer applies once `nu(N(t))` exceeds `nu0`,
   so monotonicity is open. The
   deficit counts uncovered slots, which can be large while the dual is one
   update away (Proposition 3.6). A proof would remove the stage index and the
   scaling chain from the B1 circuit (an update count independent of `U`, the
   capacities entering only through the observer), and would simplify the
   schedule of Theorem `thm:C` itself.
5. **Polymatroids beyond networks** (Section 5.4, items (a) and (b)); network
   polymatroids, laminar ones included, are covered by Proposition 5.3.
6. **Formalization.** Lemma 3.2, Lemma 3.3 and Theorem 3.4 are elementary
   (a min-max formula and Lemma `lem:avoidable`) and are natural Lean targets
   once Proposition 4.1 is formalized.
