# Phase 2a: partition matroid + general matroid (2026-10-11)

Scope: the first case of Phase 2 (`research-direction-2026-10-11.md`, section 4),
one side a partition matroid. Everything here is either proved below or marked
as observed, with the script that observes it.

## 0. Summary

1. **Arborescences are already known.** Fomin, Grigoriev and Koshevoy (Found.
   Comput. Math. 16, 2016, arXiv:1307.8425) give polynomial subtraction-free
   circuits for the directed spanning tree polynomial; tropicalized, minimum-cost
   arborescence is polynomial over `(min,+,-)` and exponential over `(min,+)`.
   They state the gap for arborescences explicitly. The paper does not cite
   them; section 6 has a proposed sentence. Phase 2's first target that
   tropicalization does not reach is **rainbow spanning trees** (partition +
   graphic), which contain `Assign_n` (section 1.2).
2. **The natural matroid version of the paper's update fails.** Restricting the
   optimal-base matroid to small reduced costs (the "closure" filtration) gets
   stuck on 3 to 10 percent of random instances, because the restriction family
   never reaches `M` itself when `M` is connected.
3. **The exact generalization exists and works.** The paper's threshold graphs
   `{D <= t}` are the bases of `M` that stay optimal when weights move by at most
   `t/2` ("possibly optimal" bases). Using that family in the paper's update
   formula reaches the optimum on every instance tested (2,160 runs: partition,
   uniform, graphic as arborescences and as rainbow trees, binary), with gain
   exactly `(k-r) tau` at every application and never more than `r+1`
   applications in stage `r`, the bound of Theorem 4.10.
4. **Its observables are NP-hard in general.** Deciding whether the level-`t`
   family contains a rainbow spanning tree is NP-complete, by reduction from
   rainbow `s`-`t` path. Even on states the schedule reaches, the family has no
   Rado-type min-max (section 3.3).
5. **A matroidal superset removes the hardness and keeps validity.**
   Theorem 6 (section 4): for any monotone family of matroids that starts at the
   optimal-base matroid and contains the possibly optimal bases, the update
   gains exactly `(k-r) tau`, a fixed optimal base meeting `r` blocks stays
   optimal, and the rainbow rank never drops. Proved.
6. **PO-SL is such a family and is compilable.** Single linkage at scale `t`
   among the possibly optimal elements of each connected component. It is a
   matroid, reads only the threshold relation `{(e,f) : v_f - v_e <= t}` (so
   the update is continuous and of the compiler's form), and equals the
   paper's `{D <= t}` for bipartite matching. Its observables are matroid
   intersections, polynomial given a Boolean rank circuit. All hypotheses of
   Theorem 6 are proved for it (Proposition 7).
7. **Termination is proved.** The paper's strict progress dichotomy fails on
   45 of 982 applications, but a lexicographic potential (avoidable set, then
   pairs of a raised element at or below an unraised one) strictly grows at
   every application (Theorem 8), so a stage has at most `r (floor(m^2/4) + 1)`
   applications. The paper's `r + 1` per stage is not enough for PO-SL: stages
   of 4, 7 and 8 applications occur, and an `r + 1` schedule then returns a
   wrong value.
   **Corollary 9:** minimum-weight rainbow bases of any matroid with a
   polynomial Boolean rank circuit have polynomial-size uniform signed tropical
   circuits. This contains rainbow spanning trees, rainbow bases of linear
   matroids over `Q` or a finite field, and the paper's assignment theorem.
   An independent referee check (section 4.3) found no counterexample in
   1.4 million exhaustive states and five fixable gaps, all repaired here.
8. **Two general matroids follow.** Common bases of `M1, M2` are the rainbow
   bases of `M1 (+) M2*` with the blocks `{(e,1), (e,2)}`, so Corollary 9 gives
   polynomial-size signed circuits for weighted matroid intersection of any two
   matroids with polynomial Boolean rank circuits (Corollary 10), which is the
   Phase 2 target of the direction document.

## 1. Setting

`E` is split into blocks `R_1, ..., R_k`; `M` is a matroid of rank `k` on `E`;
`blk(e)` is the block of `e`.

```
Opt(w) = min { w(B) : B a base of M with |B cap R_b| = 1 for every b }.
```

### 1.1 Lagrangian state

The state is a block potential `p` only, `v = w - p[blk]`, and

```
Psi(p) = sum_b p_b + beta(v),    beta(v) = min-weight base of M under v.
```

`Psi(p) <= Opt(w)` for every `p` (a rainbow base meets each block once), and
`max_p Psi = Opt` by Edmonds' intersection theorem. For bipartite matching
(`M` = column partition) this is the paper's dual with `q_j` replaced by the
column minimum. `experiments/lagrangian_bipartite.py` runs the paper's schedule
in this form: optimal on 2000 of 2000 random supports, `Psi` monotone.

`N0(v)` denotes the optimal-base matroid of `v`, `nu0` its largest rainbow
independent set. The stage-`r` update fires when `nu0 = r`.

### 1.2 Rainbow spanning trees contain assignment

Given a bipartite graph with sides `L, R` and weights `w_ij`, let `G` have
vertices `{z} cup R` and, for each edge `ij`, an edge `zj` of color `i` and
weight `w_ij`. Spanning trees of `G` choose one edge `zj` per `j`; rainbow ones
are perfect matchings. So `Assign_n` is a special case, the rainbow spanning tree
polynomial of `G` is the permanent, and the paper's reason why tropicalization
is unavailable applies verbatim.

## 2. Three filtrations

Every candidate assigns each base `B` an entry level `theta(B) >= 0`, zero
exactly on the `v`-optimal bases, and applies the paper's formula

```
tau   = min { theta(B) : B meets >= r+1 blocks }
lam_b = min { theta(B) : B meets >= r blocks other than b }
a_b   = (tau - lam_b)_+ ,          p <- p + a.
```

| name | `theta(B)` | bipartite case |
|---|---|---|
| closure | `max_{e in B} rho_e` if `B` is optimal for `vhat = v - rho`, else `inf`; `rho_e = (v_e - lam_e)_+`, `lam_e` the closure level of `e` | `max D` over `B` |
| **local** | `max { v_f - v_e : e notin B, f in C(B,e) }_+` | `max D` over `B` |
| excess | `v(B) - beta(v)` | `sum D` over `B` |

Results (`experiments/rainbow_filtrations.py`, seed 5, 300 instances per family;
gain counted per application):

| family | closure optimal | local optimal | excess optimal | apps/stage (local) |
|---|---|---|---|---|
| bipartite | 300 | 300 | 300 | <= 3 |
| arborescence | 293 | 300 | 300 | <= 2 |
| rainbow tree | 278 | 300 | 300 | <= 2 |
| binary rainbow | 278 | 300 | 300 | <= 2 |

Under local and excess every application gains exactly `(k-r) tau`; under
closure, 21 applications gain less. `experiments/rainbow_local_stress.py`
repeats local on `U_{k,m}`, arborescences and rainbow trees on 6 vertices and
rank-5 binary matroids, generic and tied weights: 480 of 480 optimal, every gain
exact, at most 3 applications in a stage. A further 480 runs over all eight
families (seed 23) are optimal with no stage `r` using more than `r+1`
applications.

**Why closure fails.** Its top level is the optimal-base matroid of `vhat`,
which equals `M` only if `vhat` is constant on the components of `M`. On the
triangle with weights `(2,1,0)` (blocks `0,1,2`, coloops elsewhere) it never
contains `{0,1}`, the only rainbow pair; reaching it requires lowering blocks
`0` and `1` together past element `2`, a move no single-element reduced cost
records. Local has `theta({0,1}) = 2` and finds it.

**Why excess is not a candidate.** Its levels are values of bases, not
sublevel sets of a vector, so the compiler cannot evaluate it; at `r = k-1` its
`tau` is `Opt - Psi` itself.

## 3. The local family

Write `L_c = { e : v_e <= c }` and `Bt = { B : theta(B) <= t }`.

### 3.1 Characterizations

**Proposition 1.** For a base `B` and `t >= 0` the following are equivalent.

1. `theta(B) <= t`.
2. `B` is a minimum base for `v - t 1_B`.
3. `v(B) - v(B') <= t |B - B'|` for every base `B'`.
4. `e in cl(B cap L_{v_e + t})` for every `e in E`.
5. `B` is a minimum base for some `u` with `||u - v||_inf <= t/2`.

*Proof.* A base is minimum for `u` iff `u_f <= u_e` whenever `e notin B` and
`f in C(B,e)`.

- (1)<=>(2): for `u = v - t 1_B` that condition reads `v_f - t <= v_e`.
- (2)=>(3): `u(B) <= u(B')` reads `v(B) - tk <= v(B') - t|B cap B'|`.
- (3)=>(1): take `B' = B - f + e`.
- (1)<=>(4): for `e notin B`, `e in cl(B cap X)` iff `C(B,e) - e subseteq X`;
  for `e in B` it is trivial.
- (2)=>(5): `u = v - t 1_B + (t/2) 1` has the same minimum bases.
- (5)=>(1): `v_f - v_e <= (u_f - u_e) + t <= t`.

So `Bt` is the set of **possibly optimal bases** under interval weights
`[v - t/2, v + t/2]`. It grows with `t`, equals `N0(v)` at `t = 0` and all bases
for `t >= max v - min v`. For `M` the column partition, `C(B,e) = {e, B(col e)}`
and `theta(B) = max_{f in B} D_f`, so `Bt` is exactly the paper's `G_t`.

**Proposition 2.** `Bt` is not a matroid in general. On `U_{2,4}` with
`v = (0,1,2,3)` on `a,b,c,d` and `t = 2`, `Bt = {ab, ac, ad, bc}`, and `ad`, `bc`
violate basis exchange at `a`.

**Proposition 3 (the update path stays inside the family).** If
`0 <= y_b <= s` for every block, every minimum base of `v - y[blk]` lies in
`Bs`.

*Proof.* For an exchange pair, `v_f - y_{blk f} <= v_e - y_{blk e}`, so
`v_f - v_e <= y_{blk f} - y_{blk e} <= s`.

Along `v(s) = v - a(s)[blk]` with `a(s)_b = (s - lam_b)_+`, Proposition 3 gives
`nu0(v(s)) <= r` for `s < tau`.

**Proposition 4 (layer cake, one direction).** For every base `B`,

```
v(B) - beta(v)  >=  integral_0^inf dist(B, Bt) dt,   dist(B, F) = min_{B' in F} |B - B'|.
```

*Proof.* Let `B_0 = B`, and let `B_{i+1} = B_i - f + e` be an exchange of
largest gain, which is `theta(B_i)`; stop at the first `B_m` with
`theta(B_m) = 0`, a minimum base. For `t >= 0` put `j(t) = min{ i : theta(B_i) <= t }`.

- `B_{j(t)} in Bt` and `|B - B_{j(t)}| <= j(t)`, so `dist(B, Bt) <= j(t)`.
- Every `i < j(t)` has `theta(B_i) > t`, so `j(t) <= #{ i : theta(B_i) > t }`.
- `integral_0^inf #{ i : theta(B_i) > t } dt = sum_i theta(B_i) = v(B) - v(B_m)`.

Observed with **equality** for all 37,463 (base, state) pairs checked
(`experiments/rainbow_local_lemmas.py`). For bipartite matching both sides are
`sum_{f in B} D_f`.

### 3.2 Observed structure of the update

From `experiments/rainbow_local_lemmas.py` (166 applications, six families) and
`experiments/rainbow_local_path.py` (760 probes along update paths, seven
families):

| statement | observed |
|---|---|
| gain `Psi(p+a) - Psi(p) = (k-r) tau` | every application |
| along the path, `nu0(v(s)) = r` for `s < tau` | 760 of 760 |
| along the path, `d Psi/ds = |S_s| - r_{N0(v(s))}(E(S_s)) = k-r`, `S_s = {b : lam_b <= s}` | 760 of 760 |
| `S_s` equals the avoidable set of `N0(v(s))` | 752 of 760; otherwise a larger maximizer of the deficiency |
| Koenig-type bound `max_{B' in Bt} |B' cap E(S_t)| = |S_t| - (k-r)` | fails 3 times, on `U_{4,9}` and `U_{4,8}` |
| progress: `nu0` rises, or the avoidable set at level 0 strictly grows | every application |

So the local update moves `p` along a path of steepest-ascent rate `k-r` through
optimal-base matroids, as the bipartite update does. The failed Koenig-type
bound means the proof cannot go through `Bt` alone: some possibly optimal bases
carry too many elements in the raised blocks, but none of them is optimal at any
point of the path. The validity proof has to use optimality along the path.

Witnesses of `tau` and `lam_b` sit at exchange distance 1 to 3 from `N0(v)`
(`experiments/rainbow_witness.py`), as augmenting paths do.

### 3.3 Hardness of the observables

**Proposition 5.** Given a graph with colored, weighted edges and `t`,
deciding whether `Bt` contains a rainbow spanning tree is NP-complete.

*Proof.* Membership: `theta(T)` is computable from fundamental cycles.
Hardness, from rainbow `s`-`t` path, NP-complete by Chakraborty, Fischer,
Matsliah and Yuster (STACS 2009, Theorem 2.3). Let `H` have colors `C`,
`|C| = q`, `h = |V(H)| >= q` (pad with isolated vertices). Build `G` on
`V(H) cup {z, y}`:

- every edge of `H`, weight 5, its color;
- `e* = st`, weight 0, a new color `c*`;
- `f = ys`, weight 0, color `c*`, so `y` is a leaf;
- for every `x in V(H)` and every color in `C cup X`, an edge `zx` of weight 10,
  where `X` is a set of `h - q` new colors.

Then `k = |V(G)| - 1 = h + 1 = |C cup X cup {c*}|`; take `t = 5`.

- `=>`: `f` is a bridge, so a rainbow `T` contains `f` and not `e*`. The
  condition for `e*` puts every edge of the tree path from `s` to `t` at weight
  at most `0 + 5`, so the path avoids `z` and lies in `H`, and it is rainbow.
- `<=`: for a rainbow path `P`, take `P`, `f`, one star edge at each vertex of
  `V(H) - V(P)` and one at a vertex of `P`, colored by `(C cup X)` minus the
  colors of `P`; there are `h - |P|` star edges and `h - |P|` such colors. Every
  tree edge weighs at most 10 and the tree path between the ends of `e*` is `P`,
  so `v_f - v_e <= 5` for every exchange pair: for `e = e*` by the path, for `e`
  an `H` edge since `10 - 5 = 5`, for `e` a star edge since `10 - 10 = 0`.
  Hence `theta(T) <= 5`.

The reduction survives on a fixed graph: put parallel edges of every color
between all pairs of `V(H)`, give the copies that belong to `H` weight 5 and the
others weight 10. The others never enter the window of `e*`, and the argument is
unchanged. So on that fixed colored graph the stage-`(k-1)` quantity
`tau = min { theta(T) : T rainbow }`, read on weights in `{0, 5, 10}`, decides an
NP-complete problem, and has no polynomial-size signed circuit unless
`NP subseteq P/poly`, since on bounded integer inputs a signed circuit is
simulated by a Boolean circuit of polynomial size.

**What this does not settle.** The schedule applies stage `k-1` only to states
with `nu0 = k-1`, and in the instance above every minimum spanning tree repeats
colors inside `H`, so `nu0` is smaller. Every variant tried that keeps
`nu0 = k-1` either lets star edges into the window of `e*` or forces a full
spanning tree of `H`, and both make the instance easy. On reachable states the
family still has no Rado-type certificate: with `rho_t(A) = max_{B in Bt} |B cap A|`,
`nu(t) < min_S (rho_t(E_S) + k - |S|)` occurs at 6 of 504 reachable (state,
level) pairs, the smallest on 4 vertices with 3 colors
(`experiments/rainbow_rado_gap.py`, `experiments/rainbow_gap_examples.py`).
Section 4 avoids the question.

## 4. Matroidal supersets

### 4.1 The validity theorem

Fix a stage `r < k` and a state with `nu0(v) = r`. Let `N(t)`, `t >= 0`, be
matroids on `E` with

- (F1) `N(0) = N0(v)`;
- (F2) every base of `N(t)` is a base of `N(t')` for `t <= t'`;
- (F3) every base `B` with `theta(B) <= t` is a base of `N(t)`;
- (F4) `N(t)` has a rainbow base for `t` large.

Put `nu(t)` for the largest rainbow independent set of `N(t)`,
`tau = inf { t : nu(t) >= r+1 }`, `lam_b = inf { t : some base of N(t) meeting
exactly r blocks avoids b }`, `a_b = (tau - lam_b)_+`. For a general family the
infima need not be attained (take `N(t) = N0(v)` up to some `T0` and `M` after
it); the proof below only uses them up to a finite set of levels. PO-SL is
right-continuous, and there they are minima. Reading `lam_b` with "at least `r`
blocks other than `b`" gives the same `a`; reading it with "at most `r` blocks"
breaks item 1 (on `U_{3,6}`, blocks `[0,0,0,1,1,2]`, `v = (0,0,0,0,0,1)`, `r = 2`, the
gain is 0 instead of 1).

**Lemma R.** Let `N` be a matroid, `nu` its largest rainbow independent set, and
`A` the set of blocks avoided by some largest rainbow independent set. Then
`|A| - r_N(E_A) = k - nu`, and `|Q| - r_N(E_Q) <= k - nu` for every set of blocks
`Q`.

*Proof.* Step 1, the inequality: a rainbow independent set has at most
`r_N(E_Q)` elements in `E_Q` and at most `k - |Q|` outside.

Step 2, the exchange graph. Fix a largest rainbow independent set `I`. For
`x in I`, `y notin I` put an arc `y -> x` if `I - x + y` is independent in `N`,
and an arc `x -> y` if `blk(y) = blk(x)`. Sources are the elements of blocks
missed by `I`; sinks are the `y notin I` with `I + y` independent. Maximality of
`I` excludes a source-to-sink path. Let `R` be the set reachable from the
sources and `A'` the missed blocks together with `{ blk(x) : x in I cap R }`, so
`|A'| = (k - nu) + |I cap R|`.

Step 3, `A' subseteq A`: along a shortest path from a source to `x in I cap R`,
exchanging gives a rainbow independent set of size `nu` that meets the block of
the source and misses `blk(x)`; independence is the standard no-shortcut
exchange lemma of matroid intersection (Schrijver, Combinatorial
Optimization, the chapters on matroid intersection).

Step 4, `r_N(E_{A'}) <= |I cap R|`: every `y in E_{A'} - I` is reachable (a
source, or the target of an arc `x -> y` with `x in I cap R`), hence not a sink,
hence `y in cl_N(I)`; each `x'` on its circuit in `I + y` receives an arc
`y -> x'` and lies in `R`. So `E_{A'} subseteq cl_N(I cap R)`.

Step 5: Steps 2 and 4 give `|A'| - r_N(E_{A'}) >= k - nu`, and Step 1 gives
equality. If some `b in A - A'` were avoided by a largest `J`, then `J` has at
most `r_N(E_{A'}) = |A'| - (k - nu)` elements in `E_{A'}` and at most
`k - |A'| - 1` outside `E_{A'} cup R_b`, so `|J| <= nu - 1`. Hence `A = A'`.

**Theorem 6.** Under (F1) to (F4):

1. `Psi(p + a) = Psi(p) + (k - r) tau`;
2. every base `B*` of `N0(v)` meeting `r` blocks is a minimum base of
   `v - a[blk]`, so `nu0` does not drop.

*Proof.* Step 1, the path: for `s in [0, tau]` put `a(s)_b = (s - lam_b)_+`,
which lies in `[0, s]`, `v(s) = v - a(s)[blk]` and `phi(s) = Psi(p + a(s))`.
`phi` is Lipschitz, so `phi(tau) - phi(0)` is the integral of its derivative.

Step 2, the right derivative: off the finitely many `lam_b`, `a(s)' = 1_{S_s}`
with `S_s = { b : lam_b <= s }`, and
`phi'(s+) = |S_s| - max { |B cap E(S_s)| : B in N0(v(s)) }`.

Step 3, the sandwich: Proposition 3 and (F3) give `N0(v(s)) subseteq N(s)`.
For `s < tau`, (F1), (F2) and the choice of `tau` give `nu(N(s)) = r`, and by (F2)
`S_s` is the avoidable set of `N(s)`. Lemma R gives
`max_{B in N0(v(s))} |B cap E(S_s)| <= r_{N(s)}(E(S_s)) = |S_s| - (k - r)`, so
`phi'(s) >= k - r` and `Psi(p + a(s)) >= Psi(p) + (k - r) s`.

Step 4, the fixed base: `B*` misses `k - r` blocks, all in `S_0 subseteq S_s`, and
meets every other block, so `|B* cap E(S_s)| >= |S_s| - (k - r)`; `B*` is a base
of `N(s)` by (F2), so equality holds. Integrating,
`v(s)(B*) = beta(v) - sum_b a(s)_b + (k - r) s`, hence
`Psi(p + a(s)) <= sum_b (p_b + a(s)_b) + v(s)(B*) = Psi(p) + (k - r) s`.

Step 5: Steps 3 and 4 give equality for every `s in [0, tau]`, and `B*` attains
`beta(v(s))`. At `s = tau` these are items 1 and 2.

The possibly optimal family itself fails the hypothesis "matroid", which is
where its proof stalls (section 3.2, the Koenig-type failures).

### 4.2 PO-SL

For `t >= 0` let `PO(t) = { f : f notin cl{ g : v_g < v_f - t } }` (the possibly
optimal elements; equivalently `v_f - lam_f <= t` for the closure level
`lam_f`). In each connected component of `M`, cluster `PO(t)` by single linkage
at scale `t` (chains of pairs at distance at most `t`); clusters are intervals
of the values and are ordered. Put `u_t(e)` = cluster index for `e in PO(t)`,
`u_t(e) = +inf` otherwise, and `N(t)` = optimal-base matroid of `u_t`.

The inequalities are as written: strict `<` in `PO(t)`, non-strict `<= t` in the
linkage. With `<=` in `PO` or `< t` in the linkage, (F1) fails already on
`U_{1,3}` with `v = (0,0,1)`.

**Proposition 7.** `N(t)` satisfies (F1) to (F4). It is determined by the
relation `G_t = { (e,f) : v_f - v_e <= t }`. For `M` a column partition it is the
threshold graph `{D <= t}` of the Lagrangian slack
`D_ij = v_ij - min_{i'} v_{i'j}` of section 1.1, which is the paper's `G_t` along
the `q`-free trajectory (not along the paper's `(p, q)` trajectory, where `q_j`
can sit below the column minimum).

*Proof.* (F1): `PO(0)` is the set of elements of optimal bases and clusters at
scale 0 are ties, so every `v`-optimal base is `u_0`-optimal. Conversely let `B`
be `u_0`-optimal and `c` a value. An element `x in PO(0) - B` with `v_x <= c` has
its circuit in `B + x` inside `{ u_0 <= u_0(x) }`, hence inside `{ v <= c }`; an
element `x notin PO(0)` is spanned by strictly cheaper elements, and induction
on the value reduces it to the first case. So `B cap { v <= c }` spans
`{ v <= c }` for every `c`, and `B` is `v`-optimal.

(F3): let `theta(B) <= t`. Each `f in B` lies in a minimum base of `v - t 1_B`,
in which every `g` with `v_g < v_f - t` is cheaper than `f`, so `f in PO(t)`.
For an exchange pair `(e, f)` of `B`: if `e notin PO(t)` then `u_t(e) = +inf`;
if `v_f <= v_e` the cluster order gives `u_t(f) <= u_t(e)`; if
`0 < v_f - v_e <= t`, both are in `PO(t)`, in one component, and every
consecutive gap of `PO(t)` between them is at most `t`, so they share a
cluster. Local optimality gives `B` optimal for `u_t`.

(F2): let `t <= t'` and `B` optimal for `u_t`; check `u_{t'}(f) <= u_{t'}(e)` for an
exchange pair `(e, f)` of `B`.

- `e notin PO(t')`: `u_{t'}(e) = +inf`.
- `e in PO(t)`: clusters at `t'` are unions of clusters at `t` with new elements
  inserted, in the same order, so `u_t(f) <= u_t(e)` persists.
- `e in PO(t') - PO(t)` and `v_f <= v_e`: cluster order.
- `e in PO(t') - PO(t)` and `v_f > v_e`: let `K` be the component of `e`.
  `e notin PO(t)` gives `e in cl{ g in K : v_g <= lam_e }` with `lam_e < v_e - t`
  (closure splits over components). Every such `g` is spanned by elements of
  `B cap K` whose `u_t`-cluster is at most that of some `x_g in PO(t) cap K` with
  `v_{x_g} <= lam_e` (induction on the value, inside `K`: a `g in PO(t) - B` by
  local optimality, a `g notin PO(t)` by the definition of `PO(t)`). Let `x*` be
  the `x_g` with the largest `u_t`. The fundamental circuit of `e` lies in
  `{ h in B cap K : u_t(h) <= u_t(x*) }`, so `u_t(f) <= u_t(x*)` with
  `v_f > v_e > v_{x*}`, hence `x*` and `f` share a cluster at `t`. The gaps
  between them are at most `t`, inserting `e` only splits gaps, so `e` joins
  that cluster at `t'`.

(F4): for `t >= max v - min v`, `PO(t)` contains every non-loop and each
component is one cluster.

Determined by `G_t`: `v_g < v_f - t` iff `(g, f) notin G_t`; single linkage uses
`|v_e - v_f| <= t`; distinct clusters of one component differ by more than `t`,
so their order is read from `G_t`.

Column partition: the possibly optimal edges of column `j` are those with
`D <= t`, all within `t` of the column minimum, so they form one cluster.
Checked at 4,110 levels, with the resulting update equal to the paper's
`(tau - lambda_i)_+`.

**Compilation.** With `D+_{ef} = (v_f - v_e)_+` over ordered pairs, the
sublevel set of `D+` at level `t >= 0` is `G_t`, and
`a_b = C_{F_b}(D+)` for `F_b(G) = 1[nu(N_G) <= r] 1[b avoidable in N_G]`, which
vanishes at the full relation by (F4). `F_b` is a matroid intersection on
`N_G`, whose rank function is a sum of rank differences of `M` along the
clusters, so a Boolean rank circuit of size `s` gives an observer of size
polynomial in `m` and `s`, and the paper's compiler (ground set of size `m^2`)
gives a signed circuit for the update. Continuity is confirmed numerically:
`|a(v + eps xi) - a(v)| <= 2.3 eps` at `eps = 10^{-2}, 10^{-3}, 10^{-4}`
(`experiments/rainbow_posl_more.py`).

### 4.3 Termination

Fix a stage `r` and an application with `nu0(v) = r`, avoidable set `S` of
`N0(v)`, `E(S)` its elements, and

```
C(v, S) = { (y, g) : y in E(S), g notin E(S), v_y <= v_g }.
```

**Lemma R'.** The avoidable set of a matroid `N` is contained in every
maximizer of `Q -> |Q| - r_N(E_Q)`.

*Proof.* If `b in A - Q` is avoided by a largest rainbow independent `J`, then
`J` has at most `r_N(E_Q) = |Q| - (k - nu)` elements in `E_Q`, so at least
`k - |Q|` elements outside, one in each block outside `Q`, `b` included.

The pairs in `C` use `v_y <= v_g`, ties included. With strict `<`, item 3 below
fails on `M(K4)` (edges `01,02,03,12,13,23`, blocks `[0,0,0,0,1,2]`,
`v = (0,0,3,1,2,2)`, `r = 2`), where the only new pairs are ties.

**Theorem 8 (potential).** After the application, with `v' = v - a[blk]`:

1. if `nu0(v') = r`, the avoidable set `S'` of `N0(v')` contains `S`;
2. `C(v', S) contains C(v, S)`;
3. `C(v', S)` is strictly larger than `C(v, S)`.

Hence stage `r` ends after at most `r (floor(m^2/4) + 1)` applications.

*Proof.* Item 1: a block of `S` is avoided by a base of `N0(v)` meeting `r` blocks,
which stays optimal at `v'` by Theorem 6.

Item 2: blocks of `S` have `lam_b = 0` and move down by `tau`; every other
block moves down by `(tau - lam_b)_+ <= tau`.

Item 3, Step 1, the first event: let `delta` be the least `t` at which the
avoidable set of `N(t)` differs from `S` or `nu(N(t)) > r`; `0 < delta <= tau`,
and every block outside `S` has `lam_b >= delta`.

Step 2, a rank jump: `r_{N(delta)}(E(S)) > |S| - (k - r) = r_{N0}(E(S))`. If
`nu(N(delta)) > r`, Lemma R bounds the deficiency of `S` by `k - r - 1`. Otherwise
the avoidable set grew, and by Lemma R' `S` is no longer a maximizer, while
Lemma R puts the maximum at `k - r`.

Step 3, a tie across `S`: take `B in N0(v)` with `|B cap E(S)| = r_{N0}(E(S))`. It is
a base of `N(delta)` by (F2), and `B cap E(S)` does not span `E(S)` there, so some
`y in E(S) - B` has its circuit in `B + y` (in `N(delta)`) meeting some
`g in B - E(S)`. For the optimal-base matroid `N` of `u` and a `u`-optimal `B`,
the `N`-circuit of `y` in `B + y` is the `M`-circuit of `y` in `B + y` intersected
with the level `{ u = u(y) }`, because `B - g + y` is a base of `N` iff it is a base
of `M` of the same `u`-weight. So `g` lies on the `M`-circuit of `y` (one
component) and `u_delta(g) = u_delta(y)` (one cluster). Since `B` is minimum for
`v`, `v_g <= v_y`; equality would put `B - g + y` in `N0(v)` with one more element
of `E(S)`. So `v_g < v_y`.

Step 4, a crossing pair: the cluster is an interval with consecutive gaps at
most `delta`. Let `alpha` be the largest value below `v_y` of an element of the
cluster outside `E(S)` (`g` qualifies) and `beta` the least value above `alpha` of
an element of the cluster in `E(S)` (`y` qualifies). No element of the cluster
lies strictly between, so `0 < beta - alpha <= delta`; call the elements `z1`
(at `alpha`, outside `E(S)`) and `z2` (at `beta`, in `E(S)`).

Step 5: `v'_{z2} - v'_{z1} <= (beta - alpha) - tau + (tau - delta) <= 0`, so
`(z2, z1)` is in `C(v', S)` and was not in `C(v, S)`. Steps 1 to 5 use only the
state before the application, so item 3 holds unconditionally.

Counting: by Lemma R, `|S| - r_{N0}(E(S)) = k - r` and `r_{N0}(E) = k`, so
`k - r <= |S| <= k - 1`, and by item 1 `S` takes at most `r` values in a stage.
While `S` is fixed, item 3 raises `|C(., S)| <= |E(S)| |E - E(S)| <= floor(m^2/4)`
at every application, so at most `floor(m^2/4) + 1` applications start from a
state with that `S`.

**Corollary 9 (Phase 2a).** Let `M` have a Boolean circuit of size `s` that
outputs the binary digits of its rank. Then `Opt(w)` is computed at every `w`
(whenever a rainbow base exists) by a uniform signed tropical circuit of size
polynomial in `m` and `s`: run stages `r = 1, ..., k-1` with
`r (floor(m^2/4) + 1)` applications of the PO-SL update each (stage 0 is never
active, since `nu0 >= 1`; an application with `nu0 > r` is the identity, since
then `tau = 0`), and output `sum_b p_b + beta(w - p[blk])`, the last term through
Theorem A of Phase 1 as `beta(v) = -h_M(-v)`. At the end `nu0 = k` by Theorems 6
and 8, so a rainbow minimum base of `v` exists and `Psi(p) = Opt(w)`. Linear
matroids qualify when given by a matrix over `Q` or a finite field, as in
Corollary C of the direction document.

**The count is needed.** A schedule with `r + 1` applications per stage, as in
the paper, is wrong for PO-SL. On the multigraph with edges `01,02,03,12,13,13`,
colors `[0,1,1,1,2,0]` and `w = (3,1,0,3,3,2)`, stage 2 takes 4 applications and
the `r + 1` schedule outputs 6 against `Opt = 7`. On a 9-edge multigraph
(`experiments/rainbow_posl_longstage.py`) stage 2 takes 7 applications and the
`r + 1` schedule outputs 22 against 26. A hill-climbing search by the referee
reached 8 applications at `r = 3`, `m = 8` to 9, and plateaued at 6 for `k = 3`,
`m = 7` to 11. The exact family `Bt` needs 2 or 3 applications on the same
inputs.

**Independent check.** A referee with a separate implementation in exact
rationals ran 1,405,996 states over 15 small matroids exhaustively
(`U_{2,4}`, `U_{2,5}`, `U_{3,5}`, `U_{3,6}`, `U_{2,6}`, `U_{2,3}` with a loop and a
coloop, two direct sums, `M(K4)`, the whirl `W3`, `F7`, three graphic
multigraphs, a `GF(3)` `U_{2,4}`), every block assignment with a rainbow base and
every `v` in `{0..3}^m` (`{0,1,2}^7` for `F7`), checking (F1) to (F4), Theorems 6
and 8 (all 5,951,272 admissible `(B, y, g)` choices in Step 3) and the compiled
update; plus 6,200 random states and 300 full schedules over further classes,
non-representable sparse paving matroids included. No failure. The gaps it
found in the arguments are the ones repaired above: `inf` in Theorem 6, the
reverse inclusion in (F1), the component in (F2), the `M`-circuit in Step 3,
and the bipartite clause. Scripts and logs are archived in
`experiments/referee_phase2a/`.

### 4.3.1 Two general matroids

**Corollary 10 (weighted matroid intersection).** Let `M1`, `M2` be matroids on
`E`, `|E| = m`, with Boolean rank circuits of sizes `s1`, `s2`. The minimum weight
of a common base, and the maximum weight of a common independent set, have
uniform signed tropical circuits of size polynomial in `m`, `s1`, `s2`.

*Proof.* Step 1, the reduction: let `N = M1 (+) M2*` on `E x {1, 2}`, with blocks
`{(e,1), (e,2)}` and weight `w_e` on `(e,1)`, `0` on `(e,2)`. A rainbow set picks
one copy of each `e`; with `X` the elements whose first copy is picked, it is a
base of `N` iff `X` is a base of `M1` and `E - X` a base of `M2*`, iff `X` is a
base of `M1` and of `M2`. Its weight is `w(X)`.

Step 2, the rank circuit of `N`:
`r_N(A x {1} cup B x {2}) = r1(A) + |B| + r2(E - B) - r2(E)`, a popcount and two
binary additions on top of the two rank circuits.

Step 3: if `r1(E) != r2(E)` there is no common base; otherwise `N` has `m` blocks
and rank `m`, and Corollary 9 applies to `N`.

Step 4, common independent sets: the largest weight of a common independent
set of size `j` is the largest weight of a common base of the truncations to
rank `j` (rank circuit: `min(r(S), j)` on the binary output), computed with
negated weights; take the maximum over `j <= min(r1(E), r2(E))`.

Two partition matroids give the paper's Theorem 1.1 (with a weaker size
bound); a partition matroid and a graphic matroid give rainbow spanning trees
and arborescences; Phase 1 is `M2` free.

Checked end to end: for 59 random pairs of binary and graphic matroids
(`m <= 5`, ties and negative weights), the rainbow optimum of `N` equals the
brute-force minimum common base, and the PO-SL schedule on `N` returns it
(`experiments/matroid_intersection_reduction.py`).

### 4.3.2 Termination, observed

| check (`experiments/rainbow_posl*.py`) | result |
|---|---|
| optimal at the end of the schedule | 180 of 180 runs, six families incl. adversarial |
| (F1), (F2), (F3) at every level | 914 / 12,569 / 13,483 checks, no failure |
| gain exactly `(k-r) tau` | 223 of 223 applications |
| applications in stage `r` | at most `r+1` in those 180 runs and in 140 static-schedule runs, but up to 8 on searched inputs (see "The count is needed") |
| strict dichotomy (rank rises or avoidable set grows) | fails on 45 of 982 applications |
| potential: rank rises, or avoidable set grows, or it stays and `C = {(y,g) : y in E(S), g notin E(S), v_y <= v_g}` grows | 875 of 875 applications; the avoidable set never shrank |

The failures of the strict dichotomy have one mechanism: an element of a
raised block becomes possibly optimal relative to a circuit partner that is
itself in a raised block, both move down together, and the exchange is
realized one application later, after the partner has fallen below an
unraised element. Step 4 of Theorem 8 is that mechanism made exact.

### 4.4 The other families, for the record

| family | matroid | continuous | contains `Bt` | stage length |
|---|---|---|---|---|
| possibly optimal `Bt` | no | yes | equal | at most `r+1` observed |
| single linkage, whole ground set | yes | yes | yes | grows with loop padding |
| single linkage per component | yes | yes | yes | up to `r+4` observed |
| interval merge over exchange pairs of `Bt` | yes | **no** | yes | at most `r+1` observed |
| PO-SL | yes | yes | yes | at most `r (floor(m^2/4) + 1)` proved; 8 at `r = 3` found |

The interval-merge families jump by about 1 under perturbations of size
`10^{-4}` (`experiments/rainbow_continuity.py`), so no signed circuit computes
them.

## 5. Consequences for Phase 2

- An update computed by a signed circuit is continuous in the state, and the
  compiler evaluates an observable on one threshold set per level. If that set
  is `{ (e,f) : v_f - v_e <= t }`, the bases all of whose exchange pairs lie in
  it are exactly `Bt` (Proposition 1, item 1). Families that read the exact
  order of `v` at level `t > 0`, such as closure, are not of the compiler's
  form.
- For partition matroids `Bt` is a restriction of the column matroid, which is
  why the bipartite case closes with a matching observer. For graphic matroids
  it is a non-matroidal family whose rainbow question is NP-complete without
  the stage guard.
- The way out is not to compute `Bt` but to enlarge it to a matroid that is
  still read from `G_t` (Theorem 6, Proposition 7). Validity then costs
  nothing; what the enlargement can cost is progress per application, and the
  choice of enlargement decides it (section 4.4).
- The kill criterion of the direction document is not met: the pair slacks are
  intrinsic (not tied to a current solution), and the induced observable is a
  matroid intersection.

## 6. Proposed addition to the paper's related work

After the sentence on Hertrich and Sering, in the paragraph beginning "Enlarging
the gate set":

> Fomin, Grigoriev and Koshevoy~\cite{fgk16} give subtraction-free circuits of
> polynomial size for the generating polynomials of spanning trees and of
> directed spanning trees; tropicalized, minimum-cost arborescence becomes
> polynomial over $(\min,+,-)$ while it is exponential over $(\min,+)$.

with

```
@article{fgk16,
  author  = {Fomin, Sergey and Grigoriev, Dima and Koshevoy, Gleb},
  title   = {Subtraction-free complexity, cluster transformations, and spanning trees},
  journal = {Found. Comput. Math.},
  volume  = {16},
  pages   = {1--31},
  year    = {2016}
}
```

## 7. Next steps

1. **Formal proof of Theorems 6, 8, Proposition 7 and Lemma R.** The referee
   check is empirical plus a reading of the arguments; the arguments are short
   enough for Lean once Phase 1's compiler is in place.
2. **The stage bound.** `r + 1` is false for PO-SL. Open: whether
   `O(r m)` or a bound independent of `m` holds (searches plateau at 6 for
   `k = 3`), or whether another family satisfying (F1) to (F4) and read from
   `G_t` restores `r + 1`. Then write the explicit size (compiler on `m^2` pair
   coordinates, observer = one matroid intersection over the PO-SL matroid).
3. **Two general matroids** are done by Corollary 10; what remains there is a
   direct algorithm with a better size than the doubling reduction gives.
4. **Guarded complexity of `Bt`** is no longer on the critical path; it is a
   question about the exact bottleneck family only.
