# Research direction after `signed_assignment.tex` (2026-10-11)

## 0. Decision

**Take the matroid line, in two phases, and formalize the compiler layer in
parallel.**

| Phase | Target | Confidence | Effort |
|---|---|---|---|
| 1 | Greedy without branching: polynomial-size signed circuits for weighted basis maximization of **every linear matroid**, and an exact complexity characterization for all matroids | near-certain; core identity verified | 1 to 2 weeks |
| 2 | **Weighted matroid intersection**: generalize Theorem 1.1 from two partition matroids to any two matroids with polynomial-size rank circuits | uncertain; both structural premises verified | 3 to 8 weeks |
| 3 | Options: min-cost flow with variable costs; general matching | low, exploratory | open |
| F | Lean: compiler layer now, the main theorem's heart after Phase 2's first milestone | high for Tier 1, laborious for Tier 2 | see section 7 |

The reason for this order: Phase 1 answers a question its closest competitors
named explicitly and said needs "entirely different proof techniques", using a
tool we already have. Phase 2 is the natural generalization of our main theorem,
and the obstruction that blocks general matching does not arise there.

## 1. Where we stand

Proven, in `paper/signed_assignment.tex`:

- bipartite min-weight perfect matching has uniform `O(n^8)` circuits over
  `max,+,-,0`, exact on all reals;
- a problem-independent compiler: a Boolean circuit of size `s` for `F` gives a
  signed circuit of size `O(ms + mN + m^2 + m log^2 m)` for its threshold
  integral, which is the Lovász extension of `F` read on complements;
- `Lat = Mon` exactly in the monotone case; `STrop` and `Bool` polynomially
  equivalent on compiled integrals, hence a barrier for lower bounds there;
- JSS Problems 3, 4, 5 answered; three-level hierarchy with one output
  subtraction sufficing.

The construction for assignment is the compiler plus a rank-staged schedule; the
compiler alone cannot reach assignment, because `Assign_2` is not linear on a
braid cone.

## 2. The open-problem map

| Problem | Source | Our leverage |
|---|---|---|
| Max-weight basis of **binary** matroids | Hertrich-Kober-Loho, IPCO 2026, "the natural next step", "would require entirely different proof techniques" | **Phase 1 answers it**, for all linear matroids |
| Is there a poly-time CPWL family needing super-poly networks? | Hertrich-Kober-Loho open problems; Hertrich-Loho | Answered **no** on the braid class (our equivalence); Phase 2 enlarges the "no" region past braid |
| Min-weight perfect matching, general graphs | Hertrich-Sering; JSS Problem 4 analogue | Phase 3 moonshot; blossom duals lack a fixed index set |
| Min-cost flow, costs or demands variable | Hertrich-Sering | Phase 2 then 3, with a pseudo-polynomial trap |
| Polynomial extension complexity of binary matroid base polytopes | Hertrich-Kober-Loho | Phase 1 gives polynomial **virtual** extension complexity |

## 3. Phase 1: greedy without branching

### 3.1 The obstruction, in the competitors' words

Hertrich, Kober and Loho, arXiv:2511.02406, verbatim:

> "These limitations prohibit the approach of simply implementing the greedy
> algorithm on a ReLU neural network."

> "already for binary matroids, which would be the natural next step to
> generalize Theorem 1.1, counting the bases is #P-hard"

> "it may be possible that Corollary 1 could be generalized to binary matroids,
> but this would require entirely different proof techniques"

Their route tropicalizes a small `(+,x,/)` circuit for the basis generating
polynomial, which exists for regular matroids through the matrix-tree theorem
and cannot exist for binary matroids unless counting bases is easy. Our compiler
needs only a Boolean circuit for the **rank**, which every linear matroid has. It
is precisely the tool that removes the branching they say prohibits greedy.

A search on 2026-10-11 found nothing beyond regular matroids.

### 3.2 Statements

Let `M` be a matroid on `E`, `|E| = m`, rank function `r`, `k = r(E)`.

**Theorem A (greedy compiled).** If a Boolean circuit of size `s` outputs `r(S)`
in binary from the indicator of `S`, then `h_M(w) = max_B w(B)` is computed at
every `w in R^E` by a uniform signed tropical circuit of size
`O(ms + m log k + m^2 + m log^2 m)`.

*Proof.* `h_M` is the Lovász extension of `r` (greedy). With `mu = min_e w_e`,
`h_M(w) = mu k + C_F(w - mu 1)` for `F(S) = r(E \ S)`, `F(E) = r(empty) = 0`.
Apply the Horner corollary with `L = ceil(log2(k+1))`; `mu k` costs `O(log k)`
gates by doubling.

**Theorem B (the converse).** A signed circuit of size `S` for `h_M` yields a
Boolean circuit of size `O(S^2)` for `r`, since `h_M(1_T) = r(T)` and every wire
on `{0,1}` inputs is an integer of magnitude at most `2^S`.

So **the signed tropical complexity of matroid optimization is polynomially
equivalent to the Boolean circuit complexity of the rank function.**

**Corollary C (classes).** Polynomial-size uniform signed circuits for weighted
basis maximization of: linear matroids with a fixed representation over any
finite field or over `Q` (all binary matroids included, via Gaussian
elimination, `s = O(mk^2)`, total `O(m^2 k^2)`); graphic and cographic;
transversal (rank is a bipartite matching size); gammoids (rank is a Menger
number); unions of these.

**Corollary D (counting).** Most matroids on `m` elements need signed circuits of
size `2^{Omega(m)}`: there are `2^{2^m / poly(m)}` matroids and `2^{O(s log s)}`
Boolean circuits of size `s`, and Theorem B transfers the bound. Greedy with a
rank oracle solves all of them; small exact networks exist for exactly those
with small rank circuits.

**Corollary E (virtual extension complexity).** Hertrich and Loho prove
`vxc(P) <= O(nnc(P))`. So every linear matroid base polytope has polynomial
virtual extension complexity. Their question whether binary matroid base
polytopes have polynomial ordinary extension complexity stays open; if the answer
is no for some binary matroid, this gives an exponential `vxc` against `xc` gap.

**Corollary F (the subtraction-free side).** For max-weight basis,
`Mon(Span_M) <= Size_{min,+,max} <= sum_{u <= k} Mon(1[r >= u]) + k - 1`, the
lower bound by JSS Proposition 2 through the min-weight form, the upper bound by
the lattice theorem applied to each threshold, whose Sugeno form holds on all of
`R^E`. So subtraction-free complexity is governed by the **monotone** complexity
of the rank thresholds and signed complexity by their **general** complexity.
For graphic matroids both are polynomial, which matches Jukna-Seiwert's sorting
speed-up for MST.

### 3.3 Verification done

`experiments/matroid_check.py`: the formula `mu k + C_F(w - mu 1)` against
brute-force max-weight basis on **3000 random binary matroids**, exact rational
weights with ties and negatives. All equal.

### 3.4 Open sub-question worth one afternoon

Is there an explicit binary matroid whose spanning predicate has super-polynomial
monotone circuit complexity? If so, Corollary F gives an exponential
`(min,+,max)` against `(min,+,-)` separation for a **greedy-solvable** problem.
The known monotone-hard functions in this family (odd factor, `Z_2`-SAT) are
closure predicates `p in cl(S)`, whose optimization version is a min-weight
circuit and not a basis problem, so they do not transfer directly.

### 3.5 Deliverable and risk

A short paper or a new section: "Greedy without branching". Risk is low and lies
in positioning: the identity is classical, the compiler is ours, and the
consequence beyond regular matroids is new. Writing and a careful related-work
paragraph against Hertrich-Kober-Loho are the whole cost.

## 4. Phase 2: weighted matroid intersection

### 4.1 Target

> For matroids `M1, M2` on `m` elements whose rank functions have polynomial-size
> Boolean circuits, the maximum weight of a common independent set, and of a
> common base, has a polynomial-size uniform signed tropical circuit.

Subsumes Theorem 1.1 (two partition matroids), arborescences (graphic and
partition), rainbow spanning trees, bipartite **simple** `b`-matching
(capacitated partition matroids, rank polynomial in `log b`), and Phase 1 (take
`M2` free).

**Correction (2026-10-11, later).** Arborescences are not new: Fomin, Grigoriev
and Koshevoy (Found. Comput. Math. 2016) tropicalize a polynomial
subtraction-free circuit for the directed spanning tree polynomial. The first
case beyond tropicalization is rainbow spanning trees, which contain `Assign_n`.
Findings on the partition-plus-general case are in
`phase2a-rainbow-2026-10-11.md`.

### 4.2 Why this one and not general matching

The obstruction recorded in Section 7 of the paper is that blossom duals have no
fixed index set. Matroid intersection does. Its LP dual, after uncrossing, is

```
max common independent weight
  = min { L1(u1) + L2(u2) : u1 + u2 >= w, u1, u2 >= 0 },
```

with `Li` the Lovász extension of `ri`. The variables are indexed by the ground
set, the slack `D_e = u1(e) + u2(e) - w(e) >= 0` is per element and independent
of any current solution, exactly like `D_ij = w_ij - p_i - q_j` in the paper.

**Verified:** `experiments/splitting_check.py`, primal against this dual on **1500
random matroid pairs**, binary and capacitated partition mixed, all equal.

### 4.3 Architecture

**Phase 2 = Phase 1 + a branch-free algorithm for an optimal splitting.** If a
fixed sequence of threshold-integral updates drives `(u1, u2)` to optimality,
the answer is `L1(u1) + L2(u2)`, two Lovász extensions computed by Theorem A.
The analogue of Proposition 4.14(2) says a continuous optimal-dual selector
should exist.

### 4.4 What carries over, and what is new

| Paper ingredient | Matroid analogue | Status |
|---|---|---|
| slack `D >= 0` on fixed edges | `D_e = u1 + u2 - w >= 0` on fixed elements | verified above |
| zero graph `G^0(D)` | tight elements, plus greedy-optimality of a candidate set for `u1` in `M1` and `u2` in `M2` | **new**: partition matroids make the second condition automatic because their duals are constant on blocks |
| `nu(G)`, rank stages | rank of the tight intersection | matroid intersection is in P |
| canonical `S(G)`, matching-independent | minimal minimizer of `A -> r1(A) + r2(E \ A)` on tight structure; minimizers form a distributive lattice | canonical by submodularity |
| bottleneck semantics `(tau, lambda, mu)` | bottleneck closure levels: how far `u_i(e)` must move before `e` becomes tight, determined by the filtration of `u_i` | braid-compatible in `u_i` |
| progress: rank rises or `S` grows | same, via exchange-graph reachability | to prove |

The one genuinely new difficulty is row two: in the general case an update must
preserve greedy-optimality with respect to the level-set structure of `u1` and
`u2`, which partition matroids never exercise.

### 4.5 De-risking plan, compute-heavy by design

1. **Rewrite Theorem 1.1 in splitting language** for two partition matroids and
   mark every step that uses block-constancy. One to two days. This produces the
   exact list of lemmas that must be generalized.
2. **Prototype** the generalized update in Python with exact rationals for binary,
   graphic and capacitated-partition pairs, `m <= 10`.
3. **Search for counterexamples** to the generalized feasibility, progress and
   termination lemmas: exhaustive over small matroids, randomized beyond. This is
   where compute pays.

**Kill criterion.** If every candidate update either breaks greedy-optimality of
the tight structure or needs per-element slacks defined on exchange-graph arcs,
which depend on the current solution and are not braid-compatible, stop and
write the obstruction up as a result.

### 4.6 A unifying hypothesis to keep in view, not to chase

The duals of assignment, matroid intersection and min-cost flow are all
L-convex in Murota's sense, and steepest descent for L-convex functions moves
along canonical minimizers of a submodular function. Our update looks like a
continuous steepest descent whose step lengths are threshold integrals. If that
reading is right, Phase 2's proof is an instance of a general branch-free
steepest-descent theorem. The trap is the step count: for flows with capacities
it is pseudo-polynomial, and only a combinatorial potential, as rank was for
assignment, keeps it polynomial.

## 5. Phase 3, options only

- **Min-cost flow with variable costs.** Polymatroid intersection would cover
  transportation, but rank stages run up to the total flow, which is
  pseudo-polynomial in the capacities. Needs a scaling or contraction idea to be
  strongly polynomial. Do not start before Phase 2 settles.
- **Min-cost flow with variable demands.** The other side of duality, closer to
  Hertrich-Sering's max-flow technique than to ours. Includes exact earth mover's
  distance on a fixed metric as a function of the two measures, which would
  interest a wider audience. A separate track.
- **General matching.** The `(y, U, t)` quotient stays the right first
  experiment. Weighted matroid parity, which contains it, is far harder than
  Phase 2. Exploratory only.
- **Lower bounds for signed circuits.** Any super-polynomial bound for a
  polynomial-time CPWL function must use the function at unboundedly many
  scales, since restricted to any grid of bounded bit-length a signed circuit is
  simulated by a polynomial Boolean circuit. A remark, not a project.

## 6. Not doing

- Chasing `n^8` downward through the schedule; Remark 4.11 shows the schedule is
  tight for `U_r`.
- A tolerant positive-scalar lower bound; it needs a scale-invariant gate
  invariant that nobody has.
- A lower bound for one output subtraction; Proposition 5.4 already answers it.

## 7. Formalization

### 7.1 What Lean and Mathlib provide here

Lean `v4.32.0` through elan, with toolchains up to `v4.34.0-rc2` installed.
`lakefile.toml` pins Mathlib `v4.32.0`, commit `81a5d257`; the sources are not
checked out locally, so `lake exe cache get` is the first step.

Checked against that commit:

| Needed | In Mathlib `v4.32` |
|---|---|
| reals, finite sums, sorting, lattice homomorphisms | yes |
| matchings, perfect matchings, alternating structures, symmetric differences | yes, `SimpleGraph/Matching.lean` |
| Tutte's theorem | yes, `SimpleGraph/Tutte.lean` |
| Hall's theorem | yes |
| vertex covers | definitions only, `SimpleGraph/VertexCover.lean` |
| **König's theorem** | **no** |
| **Berge's lemma for maximum, non-perfect matchings** | **no** |
| **Dulmage-Mendelsohn canonical sets** | **no** |
| matroids: bases, closure, duality, minors, rank `eRk` | yes, `Combinatorics/Matroid/`, but `Set`-based, `ℕ∞`-valued, infinite ground sets allowed |
| greedy algorithm for matroids | not found |
| circuits, Boolean or arithmetic, as DAGs | no |
| Lovász extension | no |

### 7.2 Tiers

| Tier | Content | Lean-friendliness | Size estimate |
|---|---|---|---|
| **1** | circuit datatype; `±` normal form; lattice-to-monotone-Boolean exact equivalence (thresholding is a lattice homomorphism `ℝ -> Prop`, and evaluation commutes with it); amplitude lifting; gap-sum compiler with size accounting; Lovász extension basics | **high** | 2 to 4 thousand lines |
| **1+** | Phase 1 theorem: finite matroid bridge, greedy optimality as a Lovász extension of rank, then Tier 1 | medium | plus 1 to 2 thousand |
| **2** | the main theorem's heart: feasibility, bottleneck semantics, progress dichotomy, termination, optimality at the end, with the Boolean observer behind an explicit interface | **laborious**: König, Berge and the canonical sets must be built first | 6 to 10 thousand |
| 2' | the observer itself, a matching algorithm as a Boolean circuit | low value for the cost | 3 thousand or more |
| 3 | Appendix B lower bounds, parse trees | not recommended | 4 to 6 thousand |

### 7.3 Recommendation

- **Start Tier 1 now.** It is the reusable core, it is what Phase 1 needs, and it
  is the part a referee would most like machine-checked because it is where the
  vanishing-amplitude argument lives.
- **Use a fresh Lake package**, for example `formal/`, separate from the abandoned
  `Daishu/` layer, and check whether current Mathlib master has added König or
  Berge before writing them.
- **For Tier 2, avoid `SimpleGraph`.** A bipartite graph as `Finset (Fin n × Fin
  n)` and a matching as an injective partial map is far more convenient for the
  alternating-reachability arguments than Mathlib's single-vertex-type graphs.
- **Decide Tier 2 after Phase 2's first milestone.** If matroid intersection
  works, formalizing its heart may be no harder than assignment's and is worth
  more.
- **Do not formalize the observer or the lower bounds.** State the observer as a
  hypothesis with a precise interface.

The earlier Lean attempt was abandoned for the companion paper's lower-bound
machinery. This paper's core is algebraic and combinatorial and fits Lean
markedly better; only the matching-theory substrate is expensive.

## 8. First two weeks

1. Phase 1: write Theorems A and B with full proofs and Corollaries C to F;
   related work against Hertrich-Kober-Loho with the verbatim quotes above.
2. Phase 2, step 1: the splitting-language rewrite of Theorem 1.1 with every
   block-constancy use marked.
3. Phase 2, step 2: the exact-arithmetic prototype and the counterexample search
   harness.
4. Tier 1: Lake package, Mathlib cache, circuit datatype, normal form, lattice
   equivalence.

Phase 1 and Tier 1 reinforce each other; Phase 2 decides what Tier 2 should
formalize.
