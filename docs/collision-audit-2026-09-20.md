# Collision Audit — `paper/signed_assignment.tex` (2026-09-20)

Scope: does any existing theorem collide with, or already imply, Theorem 1.1
(polynomial-size `(max,+,-)`-circuit for the exact bipartite minimum-weight
perfect matching value at all real weights)?

The previous audit is archived at `archive/docs/novelty-audit-2026-09.md`.  Its
literature findings for `extension_invariance_focs_v4.tex` remain valid for that
file; this document does not depend on it.

## 0. Verdict

**No collision found.**  Three independent sources, two of them from 2026,
state the question Theorem 1.1 answers as open.  The nearest work is in the same
model and by the same group, but on a disjoint problem class.

One item was upgraded from "supporting" to "load-bearing": the paper should now
claim that it answers an explicitly posed open question of Hertrich and Sering,
not only Jukna's Problem 3.

One new corollary became available: combined with Hertrich-Stargalla's monotone
lower bound, Theorem 1.1 completes an exponential monotone-versus-general
separation **for bipartite perfect matching**, which they could only obtain for
directed spanning trees.

## 1. Method and coverage

Abstract-first screening, full text only on a serious collision candidate.  Full
text was pulled for arXiv:2411.03006 (five pages read directly), arXiv:2511.02406,
arXiv:2607.11540, arXiv:2102.06635 and arXiv:2410.04907.

Coverage claimed: Jukna's monograph and its tropical-circuit citing line; the
complete 2024 to 2026 output of Hertrich, Loho, Sering and Stargalla as listed on
Hertrich's own publication page; Jukna's own publication list from 2019; and the
CPWL representation and decomposition line.  Residual gaps are in section 6.

## 2. Track A — Jukna's Problem 3 and what cites it

`Tropical Circuit Complexity: Limits of Pure Dynamic Programming`, Springer
Briefs 2023.  **Problem 3 lives in Chapter 6, "Extended Tropical Circuits."**
That chapter's own abstract begins: "In this chapter, we first show that just one
division (/) gate as the output gate can exponentially decrease the size of
monotone arithmetic (+,x) circuits," with the tropical analogue that one
subtraction gate at the output can exponentially decrease `(min,+)` circuit size.

**Collision candidate, resolved.**  If that chapter's witness function were the
assignment or permanent function, Theorem 1.1 would be largely pre-empted.  The
chapter text is paywalled and was not read.  It is nonetheless ruled out by
internal consistency: Problem 3 is posed in that same chapter, and
Hertrich-Stargalla (July 2026) still record the question as open.  A chapter does
not pose as open a question it has just answered.  Recorded as resolved by
consistency, not by reading.

Two further results from the same chapter are relevant and were confirmed:

- `(min,max,+)` circuits can be exponentially smaller than `(min,+)` circuits.
  A **monotone** extension, so it does not touch our model.
- Whether reciprocal inputs help `(min,max,+)` circuits is open.

Citing line, screened:

| Work | Relation |
|---|---|
| Hertrich-Stargalla, arXiv:2607.11540 | see section 3 |
| Hertrich-Loho, arXiv:2411.03006 | see section 3 |
| Hertrich-Kober-Loho, arXiv:2511.02406 | see section 3 |
| Kluk-Nederlof, ICALP 2026, pathwidth TSP `2^{Omega(k log log k)}` | pure model, parameterized, no overlap; already cited |
| "Tropical Attention", arXiv:2505.17190 | ML architecture that approximates tropical circuits; approximation, not exact circuits; no overlap |
| Jukna, "Tropical Complexity, Sidon Sets and Dynamic Programming" | pure model lower bounds; no overlap |

## 3. Track B — Hertrich, Loho, Sering, Stargalla, 2024 to 2026

Complete list from Hertrich's publication page, with the screen result.

| Work | Year | Screen |
|---|---|---|
| **Hertrich, Sering**, ReLU NNs of polynomial size for exact maximum flow, Math. Prog. 2025 (IPCO 2023, arXiv:2102.06635) | 2025 | **load-bearing, see below** |
| **Hertrich, Loho**, Neural networks and (virtual) extended formulations, arXiv:2411.03006v4 (28 May 2026) | 2026 | **load-bearing, see below** |
| **Hertrich, Kober, Loho**, Arithmetic circuits and neural networks for regular matroids, IPCO 2026, arXiv:2511.02406 | 2026 | **nearest precedent, see below** |
| **Hertrich, Stargalla**, Tropical circuits with scalar multiplication gates, arXiv:2607.11540 (13 Jul 2026) | 2026 | **load-bearing, see below** |
| Brandenburg, Grillo, Hertrich, Decomposition polyhedra of PWL functions, ICLR 2025, arXiv:2410.04907 | 2025 | fast-reject; see section 4 |
| Bakaev, Brunck, Hertrich, Stade, Yehudayoff, Better NN expressivity: subdividing the simplex, STOC 2026, arXiv:2505.14338 | 2026 | fast-reject; expressivity, no combinatorial value function |
| Bakaev, Brunck, Hertrich, Reichman, Yehudayoff, On the depth of monotone ReLU NNs and ICNNs, arXiv:2505.06169 | 2025 | fast-reject; monotone, and about depth |
| Grillo, Hertrich, Loho, Depth-bounds via the braid arrangement, NeurIPS 2025, arXiv:2502.09324 | 2025 | fast-reject; depth lower bounds |
| Hertrich, Stargalla, Reichman, Counting linear regions in ReLU NNs, NeurIPS 2025, arXiv:2505.16716 | 2025 | fast-reject; counting complexity |
| Froese, Grillo, Hertrich, Stargalla, Parameterized hardness of zonotope containment, ICLR 2026, arXiv:2509.22849 | 2026 | fast-reject; verification hardness |
| Rueß, Averkov, Brunck, Grillo, Hertrich, Loho, Stade, Stargalla, Sun, Winter, Shallower ReLU representations via exact linear algebra, arXiv:2607.21651 | 2026 | fast-reject; depth reduction |
| Cole, Hertrich, Tao, Végh; and Hertrich, Tao, Végh | 2025 | fast-reject; LP first-order method, auction design |

### 3.1 Hertrich and Sering — the open question we actually answer

Section 1.2 of arXiv:2102.06635 asks, verbatim:

> "Can they, for instance, compute the weight of a minimum weight perfect
> matching in (bipartite) graphs?"

and, next to it:

> "Can they compute the cost of a minimum cost flow from either node demands or
> arc costs, while the other of the two quantities is considered to be fixed?"

**This is Theorem 1.1, posed as an open question in a Mathematical Programming
paper, in the same model.**  Their Max-Affine Arithmetic Program is a pseudo-code
language permitting affine maps, `max`, `min`, and loops of fixed length, with
**no comparison-based branching and no if-statements**, proven equivalent to
neural networks in their Proposition 3.  That is our Section 2's obstruction,
stated independently.

Their results, confirmed: minimum spanning tree at size `O(n^3)`, value only;
maximum flow at size `O(m^2 n^2)`, with the flow itself.  They note a ReLU network
cannot output a discrete indicator vector, which is why MST is value-only.  Our
Theorem 1.2 outputs a dual certificate rather than a matching, for the same
reason, and should say so.

**Manuscript correction.**  The current text credits them with max flow only.
That was an over-correction made when the metadata was uncertain.  Restore the
minimum spanning tree result, and fix the bib entry to Mathematical Programming,
2025, DOI 10.1007/s10107-024-02096-x.

### 3.2 Hertrich and Stargalla — the current state, in their words

Section 1.3, Outlook, of arXiv:2607.11540 (13 July 2026), verbatim:

> "In the context of bipartite perfect matchings, we also obtain an exponential
> lower bound on mnnc(P_PERM), but it remains unknown whether nnc(P_PERM) is
> polynomial."

> "Closely related, [Juk23] explicitly states the open problem whether there are
> polynomial-size (max,+,-)-circuits to compute f_PERM."

Their abstract confirms the quoted bound is for "maximum weight directed spanning
trees and maximum weight bipartite perfect matchings", which fixes our Theorem
1.3(2) at the right strength.

**Their monotone-versus-general separation corollary uses directed spanning
trees for the upper-bound side, citing [FGK16], not matching.**  They could not
use matching because the upper bound was missing.  This was the single most
dangerous check in the audit and it came out clean.

**New corollary available to us.**  Their exponential lower bound on
`mnnc(P_PERM)` plus our `nnc(P_PERM) = O(n^8)` gives an exponential separation
between monotone or input-convex networks and general networks **on the bipartite
perfect matching polytope**.  That is a separation they explicitly could not
complete.  Worth stating as a corollary in Section 5.

### 3.3 Hertrich and Loho — the framework our result lands in

arXiv:2411.03006v4, 28 May 2026.  Definitions: `nnc(P)` is the minimum number of
neurons of a maxout network representing the support function `f_P`; `mnnc(P)` the
same for monotone networks and ICNNs; `xc(P)` extension complexity;
`vxc(P) = min { xc(Q) + xc(R) : P + Q = R }` virtual extension complexity, with
`vxc(P) <= xc(P)`.

Results: `xc(P) <= mnnc(P)`, `vxc(P) <= O(nnc(P))`.  Figure 3 marks the arcs
between `xc(P)` and `nnc(P)` with "?" in both directions, with the caption "It
remains an open question whether xc(P) and nnc(P) can be related this way."

Three things matter for us.

1. **They name subtraction as the obstruction, in the same words we do.**  Page 2:
   "It turns out, however, that there is one feature of neural networks that seems
   to make the 'dream result' difficult to obtain or maybe even wrong: namely the
   ability to use subtraction."  Our Theorem 1.1 is a concrete instance of exactly
   that.  This is a positioning citation, not a collision.

2. **Their matching lower bound is for general graphs, not bipartite.**  Page 2
   cites Rothvoss 2017 for the matching polytope having exponential extension
   complexity "even though the algorithm by Edmonds (1965) can be used to find the
   maximum weight matching or minimum weight perfect matching in polynomial time."
   Since `xc(Birkhoff) = O(n^2)`, their `xc`-based machinery yields nothing for the
   bipartite case.  No collision.

3. **Our result is a positive data point on their open arc.**  `xc(P_PERM) = O(n^2)`
   and Theorem 1.1 gives `nnc(P_PERM) = O(n^8)`, in the sub-model with unit
   coefficients.  Their Figure 3 asks whether `nnc` can be polynomially bounded by
   `xc` in general; we supply one polytope where it can.  Worth one sentence.

Also from page 1, the standing framing question: "To the best of our knowledge, it
is an open question whether there exists a family of CPWL functions, which we can
evaluate in polynomial time, but which cannot be represented by polynomial-size
neural networks."  The assignment value function was a natural candidate for such
a family.  Theorem 1.1 removes it from the candidate list.

### 3.4 Hertrich, Kober and Loho — nearest precedent, disjoint problem

IPCO 2026, arXiv:2511.02406.  Abstract: "there exist uniform `(+,x,/)`-circuits of
size `O(n^3)` to compute the basis generating polynomial of regular matroids on `n`
elements.  By tropicalization, this implies that there exist uniform
`(max,+,-)`-circuits and ReLU neural networks of the same size for weighted basis
maximization of regular matroids."

**Same model as ours, same shape of result, different problem.**  Regular matroid
basis maximization does not include bipartite perfect matching: bipartite matching
is the intersection of two partition matroids, not the basis family of one
matroid.  Confirmed no mention of matching, assignment, permanent or matroid
intersection.

**The difference sentence for related work.**  Their route is to build a small
`(+,x,/)` arithmetic circuit for the basis generating polynomial and tropicalize
it, division becoming subtraction.  That route is unavailable for bipartite
perfect matching, because the corresponding generating polynomial is the
permanent.  Our construction is not a tropicalization of an arithmetic circuit;
its subtractions come from potential updates, not from divisions.  This is a clean
and checkable distinction and should go in the paper.

Their paper is also the first example with `vxc(P)` provably below the best known
`xc(P)` bound, which is why Hertrich-Loho cite it.

## 4. Track C — does any theorem de facto imply assignment?

The question was whether some representation theorem already yields a
polynomial-size network for assignment without the authors saying so.  **No.**
The structural reason is short and worth keeping:

`Assign_n` is CPWL with `n!` distinct linear pieces.  Every general representation
theorem in this literature is parameterized either by the input dimension with a
width that is not polynomially controlled, or by the number of linear pieces or
regions.  The first gives no size bound; the second gives `n!`.  A theorem giving
polynomial size in the dimension unconditionally would contradict counting.  So a
de facto implication can only come from a **problem-specific** construction.

The complete list of problem-specific constructions in this model, as of today:

| Problem | Source | Covers assignment? |
|---|---|---|
| Minimum spanning tree, `O(n^3)` | Hertrich-Sering | no |
| Maximum flow, `O(m^2 n^2)` | Hertrich-Sering | no |
| Regular matroid basis maximization, `O(n^3)` | Hertrich-Kober-Loho | no |
| Knapsack, with integrality assumptions | Hertrich-Skutella 2023 | no |
| Minimum cost flow | **none; open, per Hertrich-Sering section 1.2** | would have, if it existed |

Minimum cost flow is the one entry that would have subsumed assignment.  It is
explicitly open in the same paragraph as the matching question.

Two further fast-rejects worth recording because they look closer than they are:

- Brandenburg, Grillo, Hertrich, arXiv:2410.04907, on decomposing a CPWL function
  into a difference of two convex CPWL functions.  The objective there is to
  minimize the **number of linear pieces**, under a fixed polyhedral complex.  No
  bound polynomial in the dimension, no combinatorial value function.  It also
  **disproves** the approach of Tran and Wang, "Minimal representations of
  tropical rational functions," Algebraic Statistics 15(1):27-59, 2024.  So the
  tropical-rational minimal-representation route is not merely unhelpful here, it
  is actively known to be broken.
- Zhang-Naitzat-Lim style results identifying ReLU networks with tropical rational
  functions are representation statements without size control, so they cannot
  imply a polynomial-size construction.

## 5. Actions for the manuscript

Nothing here changes any theorem.  All of it is citation, framing and one new
corollary.

1. **Add** Hertrich-Kober-Loho IPCO 2026 as the nearest precedent in the same
   model, with the tropicalization-versus-permanent difference sentence (3.4).
2. **Add** Hertrich-Loho arXiv:2411.03006: the `nnc`/`mnnc`/`xc`/`vxc` framework,
   their identification of subtraction as the obstruction, and one sentence that
   Theorem 1.1 supplies a polytope where `nnc` is polynomially bounded by `xc`.
3. **Upgrade** the open-problem citation.  We currently cite only Jukna's Problem
   3.  Add the Hertrich-Sering question verbatim and the Hertrich-Stargalla
   "remains unknown whether `nnc(P_PERM)` is polynomial."  Three sources, two
   from 2026.
4. **Restore** the minimum spanning tree half of Hertrich-Sering's credit and fix
   the bib entry to Math. Prog. 2025, DOI 10.1007/s10107-024-02096-x.
5. **Add a corollary** in Section 5: monotone or input-convex versus general, on
   the bipartite perfect matching polytope, exponential, from their `mnnc` lower
   bound plus our `O(n^8)`.  Attribute the lower half to them.
6. **Add** Jukna, Seiwert and Sergeev, "Reciprocal inputs in arithmetic and
   tropical circuits," ECCC TR20-178, 2020: allowing `-x_1, ..., -x_n` as inputs
   reduces `(min,+)` circuit size by at most a quadratic factor.  Our subtractions
   are interior, not at the inputs, and this is the sharpest available statement
   that the placement is what matters.
7. **Add** Jukna and Seiwert, "Sorting can exponentially speed up pure dynamic
   programming," IPL 159-160, 2020, at the sorting network in Section 3.  It
   legitimizes sorting as a primitive in this model, and its witness is MST, not
   matching.
8. **Note** that Jukna's Problem 3 sits in Chapter 6, whose own first result is
   that a single output subtraction can already give an exponential saving.  Our
   construction uses `Theta(n^8)` interior subtractions, and one output
   subtraction is not known to suffice for this function.
9. Consider noting, in Section 2 or 7, that Hertrich-Sering's Max-Affine
   Arithmetic Program independently formalizes the same no-branching restriction,
   and that our Section 2 obstruction is theirs.

## 6. Residual gaps

- Chapter 6 of the monograph was not read; the paywall blocked it.  The witness
  function for its one-output-subtraction result is unidentified.  Ruled out by
  consistency with Problem 3 and with Hertrich-Stargalla, not by inspection.  If
  a copy becomes available, check which function it is.
- The citing list of the monograph was screened through search rather than
  enumerated from a citation index.  A Semantic Scholar or Google Scholar
  citation export would close this properly.
- Hertrich-Skutella 2023 on knapsack was taken from Hertrich-Loho's description
  and not read directly.  Knapsack cannot cover assignment, so the risk is nil.
- Loho's and Sering's solo or other-group output was screened only through
  Hertrich's coauthored list and search.  A separate sweep of their pages would
  close this.

## 7. Applied to the manuscript (2026-09-20)

Actions 1, 2, 3, 4, 6, 7 and 8 of section 5 are in `paper/signed_assignment.tex`.
19 pages, builds clean, 19 cited keys all resolved, repackaged.

**Introduction, the open problem.** Now three sources. Hertrich-Sering's own
question is stated in their terms, Jukna's Problem 3 stays, and Hertrich-Stargalla
is credited with recording both as open. Their minimum spanning tree result is
restored alongside max flow, with sizes `O(n^3)` and `O(m^2 n^2)`.

**Related work, five paragraphs down to three**, in the "they did / we do" form.

1. Pure model: Jerrum-Snir, Jukna's two surveys, Jukna-Seiwert, Kluk-Nederlof.
   We do the same under an additive error on `{0,1,2}`.
2. Enlarging the gate set: Hertrich-Sering, Hertrich-Kober-Loho,
   Hertrich-Stargalla, Hertrich-Loho. We add subtraction for assignment and show
   the positive-scalar barrier survives on a finite cost set. Two difference
   sentences, both needed: tropicalization is unavailable because the generating
   polynomial is the permanent, and placement matters because
   Jukna-Seiwert-Sergeev show input-side subtraction buys at most a quadratic
   factor.
3. Decomposition technique and the two algorithms.

**Dropped:** the code width paragraph (Forney, Kashyap, Hlineny-Whittle,
Hicks-McMurray, trellis). It was already marked "not used here", and with
Appendix C gone the paper has no code content at all. Those keys stay in the
shared `references.bib` because focs_v4 cites them; eight entries are now
uncited there, which is harmless.

**Section 3:** Jukna-Seiwert's sorting speed-up is cited at the sorting network,
where it belongs.

**Bibliography:** `hertrich-sering23` renamed `hertrich-sering25` with correct
metadata (Mathematical Programming 2025, IPCO 2023 extended abstract,
doi:10.1007/s10107-024-02096-x). Added `hertrich-kober-loho26`,
`hertrich-loho26`, `jukna-seiwert-sergeev20`, `jukna-seiwert-sorting20`.

### Not yet applied

**Action 5, the new corollary.** Hertrich-Stargalla's exponential lower bound on
`mnnc(P_PERM)` together with Theorem 1.1's `nnc(P_PERM) = O(n^8)` gives an
exponential separation between monotone or input-convex networks and general
networks on the bipartite perfect matching polytope. They obtained that
separation only for directed spanning trees, because the matching upper bound was
missing. This belongs in Section 5 and changes its structure, so it was left for
a separate pass.

**Action 9**, noting that Hertrich-Sering's Max-Affine Arithmetic Program
independently formalizes the no-branching restriction of Section 2, was also left
out; Section 2 currently derives the obstruction without attributing the
formalization.

Chapter 6 of the monograph remains unread and unreadable without purchase. The
consistency argument in section 2 stands as the resolution.
