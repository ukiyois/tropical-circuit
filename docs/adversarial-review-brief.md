# Adversarial review brief

Purpose: before posting, try to break Theorem 1.1. The ask is one sentence, not a request for feedback.

## The ask (paste this)

> We claim a polynomial-size circuit over `{max, +, -, 0}` computing the exact
> bipartite minimum-weight perfect matching value at every real weight vector,
> `O(n^8)` gates, uniform. This is Theorem 1.1, stated in full on page 1.
> We are not asking whether it is interesting. We are asking you to find the
> error. The load-bearing links are listed below; an attack on any one of them
> is worth more to us than a reading of the whole paper.

Send the PDF, not the repository. The code is corroboration, and the proof does
not depend on it.

## Who

Ranked by adjacency to the actual boundary, not by seniority.

1. **Christoph Hertrich.** Closest living neighbour to this result on both
   sides: the positive-scalar tropical lower bound for the Birkhoff support
   function that our separation quotes, and the subtraction-based max-flow
   construction that is the precedent for what we do. If Theorem 1.1 is wrong,
   he is the likeliest person to see it first.
2. **Moritz Stargalla.** Coauthor of the positive-scalar bound. Best placed to
   check that we quote it at the right strength and that our `K_{n,n}` and
   `K_{2n}` bounds do not silently reprove or contradict it.
3. **Stasys Jukna.** The monograph and the open problem. Best placed to say
   whether our reading of the question matches the one he posed, and to attack
   the parse formalism in Appendix B, which is his technique.
4. **Leon Sering.** Coauthor on the max-flow construction. Best placed to
   attack the uniformity and gate-count accounting, which is where that line of
   work has had to be careful.
5. **Georg Loho.** Tropical geometry and max-affine expressivity. Best placed to
   attack the claim that the three gate sets form a diamond rather than a chain,
   and the integer-slope argument behind it.

Optional sixth if the first round is quiet: **Amitabh Basu**, for the
max-affine representation side.

## Load-bearing links, in the order we would attack them

### 1. Theorem 4.4, Steps 4 to 6 (the progress dichotomy)

The whole construction reduces to this. Specific things to try:

- Step 0 claims that for every active gap `nu(G_k) = r` and `S_0 subset S(G_k)`.
  The second half does **not** follow from monotonicity of `S` in the graph,
  which is false. It is derived from `S(G) = {i : nu(G-i) = nu(G)}` plus the
  fact that a maximum matching of `G^0(D)` stays maximum in `G_k` below `tau`.
  Attack the case where `nu(G_k)` is not constant below `tau`.
- Step 4 claims `delta <= tau` from the existence of an augmenting path at level
  `tau`. Attack the case where that path's first edge leaving `S_0 u T_0` does
  not run from `S_0` to `R \ T_0`.
- Step 5 computes `a_i = tau`, `c_j = tau - delta`, `D'_ij = 0` by splitting the
  active gaps at `delta`. Attack repeated slack values at exactly `delta` or
  exactly `tau`.
- Step 6 concludes that the rank rises or `S` strictly grows. Attack the second
  branch: it needs `M` to remain maximum in `G^0(U_r D)` and the old alternating
  paths to remain at slack zero.

### 2. Lemma 3.2 and the degenerate amplitude

The lifted Boolean observer may compute the **wrong** predicate when
`Delta_k = 0`, and we survive that only because every wire of the lifted circuit
is then `0`. Attack:

- whether any wire of the lifted observer can be nonzero when all its inputs are
  `0`, given our AND/OR/NOT encodings;
- whether `Delta_k` itself can be negative, which would break the AND encoding;
- whether the membership values of Lemma 3.1 can fall outside `{0, Delta_k}`.

### 3. Uniformity and the fixed schedule

Theorem 4.5 gives `r+1` applications at stage `r` and the schedule is
`U_0^1 ... U_{n-1}^n`. Attack:

- the induction that the zero rank entering stage `r` is at least `r`;
- whether every selection inside the Boolean observer (the "least such `j`", the
  "least neighbour") is genuinely a function of the input bits and not of an
  execution order;
- whether any gate count or wire index depends on the weight vector.

### 4. Appendix B, the vertex scope

New in this version, and the part with the least mileage on it. Attack:

- Step 6 of Theorem B.5 and Step 4 of Theorem B.6, which claim the scope `V_h`
  is determined by the circuit gate rather than by the parse occurrence;
- Step 5 of Theorem B.6, which claims the subtree exponent is supported exactly
  on `M[V_h]`;
- the constant `eps < 1/4`, which comes from `4 eps < 1`, `2 eps < 1` and
  `eps < 1/2`.

## Our own position

We ran this list ourselves before sending it. We do not currently disbelieve any
of the four. Two fixes were made while writing: Step 0 of Theorem 4.4 replaced a
false monotonicity appeal, and Step 4 replaced a circular derivation of
`delta <= tau`. Both are in the current text.

If a round of this produces no load-bearing failure, the plan is to post to
arXiv (cs.CC primary, cs.DS secondary) rather than wait for a conference cycle.
