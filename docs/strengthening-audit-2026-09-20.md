# Strengthening audit — `paper/signed_assignment.tex` (2026-09-20)

Twelve proposed directions, each verified independently before any verdict.
Companion to `docs/collision-audit-2026-09-20.md`.

## 0. Verdict table

| # | Direction | Verified? | Verdict |
|---|---|---|---|
| 1 | `eps < 1/4` to `eps < 1/2` | **yes, in full** | **implement.** It also *replaces* Lemma B.2 and shortens the appendix |
| 2 | threshold-integral compiler | **yes, in full** | **implement**, with mandatory attribution: this is the Lovász extension |
| 3 | `U_r` as `(tau, lambda, mu)` bottleneck transform | **yes, in full** | **implement.** Gives a four-line feasibility proof; reproduces Example 4.6 exactly |
| 4 | collapse a rank stage | **yes, and it has a precise obstruction** | **redirect.** One-shot exists classically but needs min-cost matching subvalues. See section 4 |
| 5 | continuous dual selector, no primal selector | **yes** | **implement.** Cheap and genuinely illuminating |
| 6 | optimal face by forced-inclusion gaps | **yes** | **implement as a corollary**, pairs with 5 |
| 7 | three-level separation | **yes**, JSS20 form confirmed | **implement**, plus a free sharpening: all weights in `{-1,0,1}` |
| 8 | NC depth corollary | **yes**, CGGRT confirmed | **implement as a remark**, hedged on a three-month-old result |
| 9 | positive-scalar tolerance | obstruction identified precisely | **state the obstruction**, do not attempt |
| 10 | one output subtraction | **yes** | **state as an open problem.** It is the tropical analogue of `vxc` |
| 11 | non-bipartite quotient | identity verified, plus a new supporting point | **record**, moonshot |
| 12 | min-cost flow ordering | nothing to verify | **record the kill criterion** |

Two findings are mine rather than yours, and both matter more than the exponent:

- **Direction 1 subsumes Lemma B.2 for both models.** The new probe family works at
  `eps = 0` without integrality, so it replaces the `3^n`-probe lemma outright.
  The appendix gets shorter *and* stronger.
- **Direction 4 is not an engineering gap, it is a structural one.** A one-shot
  rank stage exists and is classical, but it is the successive-shortest-path
  Hungarian phase, and its ingredients are min-cost matching values. The
  bottleneck transform is what the compiler of Direction 2 can produce, and the
  `r+1` applications are exactly the price of that restriction. This reframes
  `O(n^2)` updates from waste into a theorem, and it sharpens the open question.

---

## 1. `eps < 1/2`, and the lemma it replaces

**Verified in full, including every downstream constant.**

Probes: `0`, all-ones, all-twos, `u^M` (1 on `M`, 2 off `M`), and for each vertex
`v` the probe that is 2 on edges at `v` and 0 elsewhere.

With `P_M` the parse attaining the circuit minimum at `u^M`, and
`A = sum_{e in M} alpha_e`, `B = sum_{e not in M} alpha_e`:

```
Opt(u^M) = n                        (M' costs 2n - |M ∩ M'| >= n, equality iff M' = M)
(1)  kappa + A + 2B <= n + eps      (P_M is selected at u^M)
(2)  kappa + A + B  >= n - eps      (every parse, at all-ones)
(1)-(2):  B <= 2eps  ==> B = 0      (nonneg integer, eps < 1/2)
(3)  kappa + 2A >= 2n - eps         (all-twos)
(4)  kappa + A <= n + eps           (1) with B = 0
2(4)-(3): kappa <= 3eps
vertex probe: kappa + 2 deg_v(alpha) >= 2 - eps ==> deg_v(alpha) >= 1 - 2eps > 0
             ==> deg_v(alpha) >= 1  (integer)
alpha supported on M ==> alpha_{e_M(v)} >= 1 for every v ==> A >= n
zero probe: kappa >= -eps, so (4) gives A <= n + 2eps < n + 1 ==> A <= n
A = n and every M-coefficient >= 1  ==>  alpha = chi_M,  kappa in [-eps, eps].
```

**Downstream check, which is the part that decides the constant.** In
`thm:pure-full`:

- Step 3, cross constants: `kappa_Q <= 3eps`. No constraint.
- Step 4, cross degrees: `deg(alpha_Q) in [n - 2eps, n + 2eps]`, integer, needs
  `2eps < 1`, i.e. **`eps < 1/2`**.
- Step 5, canonical cross: needs `3eps < 2 - eps`, i.e. **`eps < 1/2`**, attained
  exactly at the boundary.

So all three binding constraints coincide at `1/2`. That is why the threshold is
natural: it is the point at which one unit of an integer exponent can no longer
be absorbed by the error. **Do not claim it optimal**; whether a circuit exists at
`eps = 1/2` is untested.

**The part you did not note.** Run the same probes at `eps = 0`:

```
B <= 0 ==> B = 0                    (nonnegativity alone, no integrality)
kappa <= 0 and kappa >= 0 ==> kappa = 0
deg_v(alpha) >= 1 ==> A >= n;  (4) gives A <= n  ==> A = n ==> alpha = chi_M
```

No integrality anywhere. So the new probe family **also serves the
positive-scalar model**, which is the only thing Lemma B.2 was still needed for.
Lemma B.2 and its `3^n`-probe family with the coordinatewise sign choice can be
deleted outright and replaced by this one lemma serving both models.

Net effect: appendix shorter, tolerance doubled, one fewer probe family.

---

## 2. The threshold integral is the Lovász extension

**Identity verified.** With `G_t(D) = {e : D_e <= t}` and `F : 2^E -> {0,1}`,
`F(E) = 0`:

```
C_F(D) := int_0^inf F(G_t(D)) dt = sum_{k=0}^{m-1} (s_{k+1} - s_k) F(G_k)
```

because `G_t` is constant on `[s_k, s_{k+1})` and the tail `t >= s_m` has
`G_t = E`, `F(E) = 0`. This is exactly the paper's gap sum.

**Lipschitz bound verified.** `G_t(D) != G_t(D')` requires `t` to lie between
`D_e` and `D'_e` for some `e`, so the set of such `t` has measure at most
`||D - D'||_1`, and the integrand is bounded by 1:

```
|C_F(D) - C_F(D')| <= ||D - D'||_1 .
```

Continuity now needs no tie analysis at all. The vanishing-amplitude argument of
Lemma 3.2 is the discrete shadow of this.

**Attribution, mandatory.** Substituting `g(S) := F(E \ S)` gives

```
C_F(D) = int_0^inf g({e : D_e >= t}) dt ,       g(empty) = F(E) = 0 ,
```

which is the **Lovász extension** of `g` evaluated at `D`, equivalently its
Choquet integral or layer-cake representation. The functional object is
classical and must be cited as such (Lovász 1983). Submodularity is not needed;
the layer-cake formula defines the extension of an arbitrary set function, and
ours is not submodular.

**What appears to be new is the compilation, not the object:**

> If `F` has a Boolean circuit of size `s`, then `C_F` has a `(max,+,-,0)` circuit
> of size `O(ms + m^2 + m log^2 m)`.

The collision audit found no such statement in this literature, but a targeted
search for "Lovász extension" plus "neural network size" or "tropical circuit"
has **not** been run and must be, before this is promoted to a named theorem.
Note that Brandenburg, Grillo and Hertrich already claim consequences "in the
theory of submodular functions", which is the nearest place a collision could
hide.

**Two free generalizations, both verified.**

1. Integer-valued observables. For `f : 2^E -> {0,1,...,N}` with `f(E) = 0`,
   write `f = sum_{u=1}^{N} 1[f >= u]` and apply the compiler `N` times:
   size `O(N(ms + m^2) + m log^2 m)`, Lipschitz constant `N`.
2. The filtration needs no graph structure. Any `m` real triggers and any
   `F : 2^{[m]} -> {0,1}` work.

**Fit.** The assignment update is `a_i = C_{F^L_{r,i}}(D)` with
`F^L_{r,i}(G) = 1[nu(G) <= r] 1[i in S(G)]`, and `F^L_{r,i}(E) = 0` because
`nu(E) = n > r`. Confirmed.

Recommendation: promote to the main proposition of Section 3 and state
assignment as its first nontrivial application. This is the change that makes
the paper reusable rather than single-purpose.

---

## 3. `U_r` is a bottleneck transform

**All five identities verified**, and checked numerically against the paper's own
Example 4.6.

```
tau     = min over (r+1)-matchings of max_{e in M} D_e
lambda_i = min over r-matchings avoiding i of max_{e in M} D_e
mu_j    = min_{i : ij in E} max(lambda_i, D_{ij})
a_i = (tau - lambda_i)_+ ,   c_j = (tau - mu_j)_+
D'_{ij} = D_{ij} - (tau - lambda_i)_+ + (tau - mu_j)_+
```

Derivation of `a_i`: the guard is on exactly for `t < tau`; on that range
`nu(G_t) = r`, so `i in S(G_t) <=> nu(G_t - i) = r`, which is monotone in `t`;
hence `{t < tau : i in S(G_t)} = [lambda_i, tau)`. Same for `mu_j` through
`T(G_t) = N_{G_t}(S(G_t))`.

**Example 4.6, first update** (`D = [[0,1],[1,3]]`, `r = 1`):
`lambda_1 = 1`, `lambda_2 = 0`, `tau = 1`, so `a = (0,1)`;
`mu_1 = mu_2 = 1`, so `c = (0,0)`. Matches the paper.
**Second update** (`D = [[0,1],[0,2]]`): `lambda = (0,0)`, `tau = 1`, `a = (1,1)`;
`mu_1 = 0`, `mu_2 = 1`, `c = (1,0)`. Matches the paper.

**Feasibility in four lines** instead of the current gap-by-gap argument. From
`mu_j <= max(lambda_i, D_{ij})`:

- `lambda_i >= D_{ij}`: then `mu_j <= lambda_i`, so `D' >= D_{ij} >= 0`.
- `lambda_i < D_{ij} <= tau`: `D' >= D_{ij} - (tau - lambda_i)_+ + (tau - D_{ij})_+ = min(tau, lambda_i) >= 0`.
- `lambda_i < D_{ij}`, `tau <= D_{ij}`: `D' >= D_{ij} - tau >= 0`.

Recommendation: state as a proposition giving the *semantics* of `U_r`, keep the
gap sum as the circuit realization, and replace the current feasibility proof.

---

## 4. Collapsing a rank stage: a one-shot update exists, and it is out of reach

This is the direction you ranked highest, and it is the one where the analysis
changed the picture.

**A one-shot update exists and is classical.** It is the shortest-augmenting-path
Hungarian phase. With `d_v` the shortest alternating-path distances from the free
left vertices, forward arcs `i -> j` of length `D_{ij}` and matched arcs
`j -> i` of length 0, and `delta = min{d_j : j free}`:

```
a_i = (delta - d_i)_+ ,   c_j = (delta - d_j)_+
```

- Matched edges stay at zero: `d_i = d_j` for `ij in M`, so `a_i = c_j`.
- Tight shortest-path edges become zero: `d_j = d_i + D_{ij}` gives `D' = 0`.
- Feasibility: `d_j <= d_i + D_{ij}` gives `D' >= 0` in all four sign cases.
- The shortest augmenting path to the nearest free right vertex becomes all-zero,
  so the rank rises. **One application per stage, `O(n)` total instead of `O(n^2)`.**

**Checked on Example 4.6.** `d_1 = 1`, `d_2 = 0`, `delta = 2`, `a = (1,2)`,
`d_{col} = (1,2)`, `c = (1,0)`, giving `D' = [[0,0],[0,1]]` in **one** update. The
bottleneck transform needs two to reach the same state. The two transforms are
genuinely different, and only the sum version collapses the stage.

**Why it is out of reach.** The ingredients are min-cost matching values:

```
d_i    = min cost of an r-matching avoiding i, in reduced costs D
delta  = A_{r+1}(D),  the min cost of an (r+1)-matching in reduced costs
```

(`A_r(D) = 0` because `M` is optimal at the current dual.) A min-cost
`r`-matching in a bipartite graph is a min-cost perfect matching after padding,
so computing `d_i` for all `i` at one stage is `n` assignment problems of the
same size. Doing this at every stage is `n^2` of them. The sizes do not shrink,
so there is no recursion. **The route is circular.**

**Why the bottleneck version escapes.** `tau` and `lambda_i` are thresholds of
*monotone Boolean predicates on a filtration*, `nu(G_t) >= k` and
`nu(G_t - i) = r`, which is exactly the class the Direction 2 compiler converts.
A shortest-path length is a sum along a path whose structure depends on `M`, and
it is not a threshold integral of anything.

**What this is worth.** Three things, all better than an exponent.

1. The `O(n^2)` update count stops being an apparent inefficiency and becomes the
   measured price of using a compiler that can only produce bottleneck data.
2. The open question sharpens from "can the schedule be collapsed?" to
   **"can shortest alternating distances be compiled?"**, which is a question
   about the compiler, not about matchings.
3. It predicts where a breakthrough would have to come from, and it is not the
   Dulmage-Mendelsohn decomposition. DM would reorganize the same bottleneck
   information; it does not produce path sums.

Your kill criterion was the right shape but aimed at the wrong object. The
correct one: **a one-shot stage exists iff `d_i` is compilable; anything that
only reorganizes `S`, `T` or the DM quotient cannot get there**, because those
are all threshold data and `d_i` is not.

The remaining honest avenue for the exponent is not the schedule but the
per-update cost. `a_i` is determined by the single number `lambda_i`, so the `m`
separate observer evaluations per update carry only `n` numbers of information.
Computing all `lambda_i` in one parametric pass, rather than `m` independent
observer calls, would cut a factor of `m` from each update. That is an
engineering improvement to Proposition A.2, not a new theorem.

---

## 5. Primal-dual asymmetry

**Both halves verified.**

No continuous primal selector, for `n >= 2`. On the open region where `M_1` is
the unique optimum, the optimal face is the single vertex `chi_{M_1}`, so any
exact optimal `x(W)`, even a fractional one, equals `chi_{M_1}` there; likewise
`chi_{M_2}` on a region where `M_2` is unique. The two regions have intersecting
closures, so `x` cannot be continuous.

A continuous dual selector of polynomial size exists: Theorem 1.2 outputs
`(p, q)` through a signed circuit, hence continuous and piecewise linear, and
dual-optimal by the complementary-slackness argument already in the paper.

**Gauge fixing verified.** `p'_i = p_i + q_1`, `q'_j = q_j - q_1` leaves every
slack and the objective unchanged and sets `q'_1 = 0`. Cost `2n` gates.

This is the right explanation of why Theorem 1.2 certifies with a dual rather
than a matching, and it upgrades a limitation into a theorem. Hertrich and Sering
observe the discrete-indicator half for spanning trees; the sharp dichotomy,
including the fractional case, seems worth stating for assignment.

---

## 6. The optimal face

**Verified**, including the step that is not automatic.

`gamma_{ij}(W) = w_{ij} + Assign_{n-1}(W_{hat i, hat j}) - Assign_n(W)` is the
excess of the best perfect matching through `ij`, so `gamma >= 0` and
`gamma_{ij} = 0` iff some optimal matching uses `ij`.

The non-automatic step: is `{X in B_n : X_{ij} = 0 whenever gamma_{ij} > 0}` the
optimal face, or merely a superset? It is the face. `gamma_{ij} = 0` implies `ij`
is tight at any optimal dual, so a perfect matching inside the `gamma = 0` graph
has all edges tight and is therefore optimal; conversely every optimal matching
lies in that graph. By Birkhoff applied to the `gamma = 0` subgraph, the doubly
stochastic matrices supported there are exactly the convex hull of those
matchings.

Exclusion gaps `eta_e = Opt(H \ e) - Opt(H)` likewise satisfy `eta_e > 0` iff `e`
is in every optimal matching.

Cost: `n^2` copies of an `(n-1)`-assignment circuit, `O(n^{10})` dense. Worth a
corollary, not a section, and it pairs with Direction 5: **no continuous primal
point can be selected, yet the entire optimal face has a continuous
polynomial-size encoding.**

---

## 7. Three levels, and a free sharpening

**Confirmed, including the exact form of the middle rung.** ECCC TR20-178
abstract: "the gain in circuit size is then always at most quadratic", over
`(min,+)` and `(max,+)` with reciprocal inputs `-x_1, ..., -x_n`. So
`size_without <= size_with^2`, and an exponential bound survives:
`size_with >= 2^{Omega(n)/2}`.

```
positive scalars anywhere        ->  2^{Omega(n)}    [ours; Hertrich-Stargalla]
negation only at the inputs      ->  2^{Omega(n)}    [Jukna-Seiwert-Sergeev]
negation on internal wires       ->  poly(n)         [Theorem 1.1]
```

Note our own machinery does **not** cover the middle rung: with `-w_e` available,
parse exponents live in `Z^E` rather than `Z_{>=0}^E` and the step `B <= 2eps
implies B = 0` fails. It must be cited, not reproved.

**Free sharpening.** `x - y = x + (0 - y)`, so the alphabet gains only the scalar
`-1`. Realized as a network, `max(x,y) = x + ReLU(y - x)` and the subtractions all
use coefficient `-1`, so **every weight in the construction lies in `{-1,0,1}`**.
The statement becomes: arbitrary positive scalars do not help, input negations do
not help exponentially, and the single internal scalar `-1` suffices.

---

## 8. Depth

**CGGRT confirmed**: Chatterjee, Ghosh, Gurjar, Raj, Thierauf, "Bipartite
Matching is in NC", ECCC TR26-100, June 2026; first deterministic NC algorithm
for bipartite matching, extending to weighted bipartite matching and weighted
linear matroid intersection.

**No collision.** Their model is the standard Boolean one with bounded integer
weights. Hertrich and Loho make the relevant point explicitly: a binary-model
construction is sensitive to single input bits and does not transform into an
exact real-valued network. Our statement is exact over all reals with no
comparison gate.

**The corollary works.** `nu(G)` in NC gives a poly-size polylog-depth Boolean
observer, and `S(G)`, `T(G)` follow by reachability, also NC. All `m` gaps run in
parallel, the sorting network is polylog depth, and the gap sum is a balanced
tree. Each `U_r` is polylog depth. Only the `O(n^2)` schedule stays sequential:

```
size n^{O(1)},   depth O(n^2 polylog n) .
```

Worth one remark, explicitly conditional on a three-month-old result, and worth
noting that a compilable `d_i` (Direction 4) would take the depth to
`O(n polylog n)`.

---

## 9. Positive-scalar tolerance: the obstruction, stated precisely

Your diagnosis was "no integrality". The obstruction is sharper than that, and
naming it correctly matters because it says what a fix would have to do.

At `eps = 0` the cross constants vanish **exactly**, which is what pins the
subtree scale: `kappa_Q = sigma_M(kappa^h_{M'} - kappa^h_M) >= 0` and its mirror
force `kappa^h_M = kappa^h_{M'}`. At `eps > 0` they are only `O(eps)`, and the
context scalar `sigma_M > 0` is unbounded, so dividing by it amplifies the slack
without limit. The quantity `beta_v = sigma_M deg_v(A^h_M)` stays in `[0,1]` and
avoids the division, but comparing `beta` across two matchings needs the ratio
`sigma_M / sigma_{M'}`, which nothing controls.

So the obstruction is **scale unidentifiability**, not the absence of integers:
inserting `x -> eta x -> eta^{-1} x` changes neither the function nor the gate
count while rescaling every subtree. Any tolerant scalar bound must use a
scale-invariant gate invariant. That is a genuinely new technique, and the
approximate-Minkowski-rectangle idea is a reasonable shape for it.

Do not attempt now. One sentence in the limitations.

---

## 10. One output subtraction: it is the tropical `vxc`

**Reduction verified.** In the constant-`0` model every pure `(max,+)` circuit
computes a positively homogeneous function, hence the support function of its
Newton polytope. So a circuit with a single subtraction at the output computes
`h_A - h_B`, and `h_P = h_A - h_B` forces `h_A = h_{P+B}`, that is `A = P + B`.
Therefore

```
MC(P) = min over polytopes B of ( Trop(B) + Trop(P+B) )
```

and one output subtraction suffices for `P` iff `MC(P)` is small.

**The calibration you should know before investing.** `MC(P)` is the exact
tropical analogue of Hertrich and Loho's virtual extension complexity
`vxc(P) = min{ xc(Q) + xc(R) : P + Q = R }`, with tropical circuit size in place
of extension complexity. They state that deriving useful lower bounds on `vxc`
is open, and their regular-matroid paper is the first example where `vxc` beats
the best known `xc`. So proving `MC(B_n) = 2^{Omega(n)}` is a lower bound of a
type that is currently open in the neighbouring measure.

That does not make it a bad problem. It makes it a *named* problem, which is
better than an unnamed one. State it in Section 7 with the `MC` definition and
the `vxc` analogy; do not attempt it here.

---

## 11. Non-bipartite quotient

**Identity (17) verified.** With `d_v = sum_{S ni v} z_S` and `t = sum_S z_S`,

```
sum_v d_v = sum_S |S| z_S ,   so   sum_S ((|S|-1)/2) z_S = (1/2)(sum_v d_v - t) .
```

Edge slacks depend on `z` only through `U_{uv} = sum_{S superset {u,v}} z_S`, so
both the slack semantics and the objective factor through `(y, U, d, t)`, which
is polynomial-dimensional. Your observation is correct.

**A supporting point you did not raise.** For a laminar family the sets
containing a fixed pair form a chain, so `U` is a cophenetic matrix of a weighted
hierarchy. Generically the laminar family is *recoverable from `U` by
thresholding*: the sets `{v : U_{uv} >= theta}` reconstruct the hierarchy as
`theta` decreases. That is itself a threshold filtration, which is exactly the
input format of the Direction 2 compiler. Degenerate `z_S = 0` collapse sets, and
those are precisely the places where a vanishing amplitude would have to absorb
the ambiguity.

So the moonshot is better aligned with the existing machinery than the current
Section 7 suggests. It remains a moonshot: recovering the laminar family is not
the same as driving the next blossom update, and blossom birth and death are
discrete events not yet expressed as threshold data.

Your `n <= 8` kill experiment is the right first step. Run it against the
thresholding reconstruction, not against raw collisions: the question is whether
two laminar states with the same `(U, d, t)` have different futures, and the
reconstruction says they generically do not.

---

## 12. Min-cost flow ordering

Nothing to verify; the reasoning is sound and the kill criterion is the right
one. Recorded: vertex cloning for `b`-matching gives size polynomial in
`B = sum_i b_i` rather than in `log B`, which is pseudo-polynomial and does not
answer Hertrich and Sering's min-cost-flow question. Any attempt must carry a
state and progress invariant that is `poly(n, m, log U)` or strongly polynomial.

---

## 13. Recommended order

Three passes, not twelve.

**Pass A, mechanical and already verified.** Directions 1, 3, 5, 7. Tolerance to
`eps < 1/2` with Lemma B.2 deleted; `U_r` stated as a bottleneck transform with
the short feasibility proof; the primal-dual dichotomy as a proposition; the
three-level picture with the `{-1,0,1}` sharpening. All of this shortens the
paper or leaves it the same length.

**Pass B, the restructure.** Direction 2, after the targeted novelty search on
"Lovász extension" plus "circuit size". Section 3 becomes a compiler theorem with
assignment as its first application, the Lipschitz bound replaces the tie
analysis, and the integer-valued extension is stated for reuse. Then Directions 6
and 8 as corollaries, and Directions 4, 9, 10, 11 as precisely stated open
problems in Section 7.

**Pass C, research.** Only Direction 4's sharpened question is worth opening:
can shortest alternating distances be compiled? Everything else in the table is
either an open problem to state or a second paper.

**What not to do.** Do not chase `n^8 -> n^7` through the schedule; Direction 4
shows the schedule is not where the slack is. If an exponent is wanted, the
`m`-fold observer repetition inside a single update is the only real slack, and
it is an implementation detail of Proposition A.2.

## 14. Passes A and B applied (2026-09-20)

23 pages, builds clean: exit 0, zero overfull boxes, zero undefined references,
zero undefined citations, zero multiply-defined labels, zero em-dashes, no claim
language, no pointer words.  20 cited keys, all resolved.  Repackaged at
`paper/signed-assignment-arxiv.tar.gz`.

Layout: 1 (p.1), 2 (p.4), 3 (p.5), 4 (p.7), 4.4 (p.10), 5 (p.11), 6 (p.14),
7 (p.14), references (p.16), A (p.17), B (p.19), C (p.23).

### 14.1 Pass A

**Direction 1.**  `lem:pin-full` is replaced by a five-probe lemma: zero,
all-ones, all-twos, `u^M`, and one probe per vertex.  It concludes
`alpha = chi_M` and `|kappa| <= eps` outright, so the `ell_1` estimate and the
`3^n`-probe family with the coordinatewise sign choice are gone.  Integrality is
used only in the pure model and only to turn `B <= 2eps`,
`deg_v >= 1 - 2eps` and `A <= N/2 + 2eps` into exact statements, each needing
`2eps < 1`.  Tolerance is now `eps < 1/2` in `thm:robust`, `thm:pure-full`,
`cor:families` and Section 7.  Sharpness is not claimed.

**Direction 3.**  `prop:bottleneck` states
`a_i = (tau - lambda_i)_+`, `c_j = (tau - mu_j)_+` with `tau`, `lambda`, `mu`
defined as bottleneck matching values, under the hypothesis `nu(G^0(D)) = r`,
which is the only case an active stage produces.  Feasibility is re-derived from
it in three cases inline.  The sorted values and the graphs `G_k` are now
explicitly a representation rather than part of the object.

**Direction 5.**  New Section 4.4 with `prop:selectors`: no continuous primal
optimal selector for `n >= 2`, even fractional; a continuous piecewise linear
dual selector of size `O(n^8)`, normalizable to `q_1 = 0` at `2n` further gates.
Hertrich-Sering's discrete-indicator observation is cited as the precedent.

**Direction 7.**  `eq:three-levels` in Section 5: positive scalars anywhere
exponential, negation at the inputs only exponential
(`jukna-seiwert-sergeev20`, with an explicit note that our own argument does not
reach that line because exponents would leave `Z_{>=0}^E`), negation on internal
wires polynomial.  Plus the sharpening that every weight of the construction
lies in `{-1,0,1}`.

### 14.2 Pass B

**Direction 2.**  Section 3 is now problem-independent and is titled "Compiling
Boolean observers on a threshold filtration".  It contains
`def:filtration`, `prop:two-readings` (gap sum, and the identification with the
Lovász extension of `g(S) = F(E \ S)`, cited to `lovasz83`),
`lem:lipschitz` (nonexpansive in `ell_1`, which replaces all tie analysis),
`lem:bit`, `lem:lift`, `thm:compiler`, and `cor:integer-observable`.
Matchings appear only in the closing remark.

**The compiler is vector-valued, and that is not cosmetic.**  A scalar version
would cost `O(Nms)` for `N` observables and push the schedule to `n^9`.  Sharing
one Boolean circuit across the `N = 2n` outputs keeps it at `O(ms + mN)`, and
the Section 4 size proof is now one application of `thm:compiler` with
`s = O(n^2 m)`, reproducing `O(n^6 m + n^2 m^2)` and `O(n^8)`.

**Direction 6.**  `cor:optimal-face`: the forced-inclusion gap
`gamma_ij = w_ij + Assign_{n-1}(W_hat) - Assign_n(W)` is continuous, piecewise
linear, computed at `O(n^10)`, and its zero set is exactly the set of edges used
by some optimal matching; the optimal face is the doubly stochastic matrices
supported there.  The step that is not automatic, that a perfect matching inside
`{gamma = 0}` is optimal, is proved through tightness.  Paired with
`prop:selectors`: no point of the optimal face can be selected continuously, yet
the whole face has a continuous polynomial-size encoding.

**Direction 8.**  A depth paragraph in Section 7: size `n^{O(1)}`, depth
`O(n^2 polylog n)`, conditional on `cgnc26` and explicitly flagged as a very
recent Boolean-model result used only for the observer.

**Open problems added to Section 7**, three of them, each with the reason it is
open rather than merely unattempted:

1. Compiling shortest alternating path distances.  The section states the
   one-shot update `a_i = (delta - d_i)_+` explicitly, and states that `delta`
   and `d_i` are minimum-cost matching values, which is why it is not a threshold
   integral.
2. `MC(P) = min_B (Trop(B) + Trop(P+B))`, the tropical analogue of virtual
   extension complexity, with the derivation that one output subtraction forces
   `A = P + B`.
3. A scale-invariant gate invariant for positive-scalar circuits, with the
   `x -> eta x -> eta^{-1} x` obstruction spelled out.

The non-bipartite paragraph now carries the `(U, d, t)` quotient, the identity
`sum_S ((|S|-1)/2) z_S = (1/2)(sum_v d_v - t)`, and the observation that `U` is
itself a filtration in the sense of `def:filtration`.

### 14.3 Novelty check run before Pass B

Searched for "Lovász extension" against neural network size and circuit
complexity.  The extension and its layer-cake form are classical and are cited.
The nearest observation in the literature runs the other way: `max{x-y,0}` is the
Lovász extension of the cut function of a single arc, and a feedforward network
is an iterated Lovász transformation.  No size bound of the form "Boolean
circuit for `F` yields a signed tropical circuit for its extension" was found.
The paper states the object as classical and only the size bound as new.

### 14.4 Not done, by instruction

Pass C, the research direction, is the user's.  The sharpened question is stated
as the first problem in Section 7.
