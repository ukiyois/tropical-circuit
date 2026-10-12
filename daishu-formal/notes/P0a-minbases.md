# P0a: minimum bases (Lemma `lem:minbases`(1) to (3), equation `eq:rank-mu`)

Natural-language companion of `SignedTropical/Rainbow/MinBases.lean`, namespace
`SignedTropical.Rainbow`.  Source: `daishu/paper/greedy_intersection.tex`, Lemma
`lem:minbases` items 1 to 3 and equation `eq:rank-mu`:

> Let `u ∈ ℝ^E`.
> 1. A base `B` is minimum for `u` if and only if `u_f ≤ u_e` whenever `e ∉ B` and
>    `f ∈ C(B, e)`.
> 2. A base `B` is minimum for `u` if and only if `B ∩ {u ≤ c}` spans `{u ≤ c}` for every
>    `c ∈ ℝ`.
> 3. The minimum bases of `u` are the bases of a matroid `M^u`.  For a minimum base `B` and
>    `e ∉ B`, the base `B - f + e` is minimum if and only if `f ∈ C(B, e)` and `u_f = u_e`, so
>    the circuit of `e` in `B + e` in `M^u` is `{e} ∪ {f ∈ C(B, e) : u_f = u_e}`.
>
> If `ℓ_1 < ... < ℓ_q` are the values of `u` and `U_i = {u ≤ ℓ_i}`, `U_0 = ∅`, then
> `r_{M^u}(A) = Σ_{i=1}^{q} (r(U_{i-1} ∪ (A ∩ {u = ℓ_i})) - r(U_{i-1}))`.

The module also carries the basic API of the shared definitions of `Rainbow/Defs.lean`
(`minBaseWeight`, `nu`, `Av`, `IsRainbowBase`, `Opt`, `blockSet`, `blocksMet`).  Item 4 of the
lemma (connected components) is the module `Rainbow/Connectivity.lean` of agent P0b.

Build status: `lake build SignedTropical.Rainbow.MinBases` succeeds with no error and no
warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`
or `opaque`.  Every theorem listed below depends only on `propext`, `Classical.choice` and
`Quot.sound` (checked with `#print axioms`).

Notation.  `E = {0, ..., m-1}` (Lean `Fin m`), `M` is a matroid on `E` (Mathlib
`Matroid (Fin m)`), and "`M` has ground set `E`" is the hypothesis `hE : M.E = Set.univ`.
Sets of elements are `Finset (Fin m)`, coerced to sets for Mathlib.  For `u ∈ ℝ^E` and
`S ⊆ E`, `u(S) = Σ_{e ∈ S} u_e`, `{u ≤ c} = {e : u_e ≤ c}`, and similarly for `<` and `=`.
`r` is the rank of `M` as a natural number (`rk M`, Phase 1), `r(M) = rank M`, and `cl` is
Mathlib's `M.closure`.  `B - f + e` is `insert e (B.erase f)`.  From `Rainbow/Defs.lean`:

* `IsMinBase M u B`: `B` is a base of `M` and `u(B) ≤ u(B')` for every base `B'` of `M`;
* `minBaseWeight M u`: `β_M(u) = min_B u(B)`, the infimum of the base weights;
* `levelPiece M u ℓ`: the matroid `L_ℓ = (M ↾ {u ≤ ℓ}) / {u < ℓ}`, whose ground set is
  `{u = ℓ}`;
* `minBases M u`: the matroid `M^u`, the direct sum of the level pieces `L_ℓ` over `ℓ ∈ ℝ`
  (only the values of `u` give nonempty pieces);
* `connRel M e f`: `e = f`, or some circuit of `M` contains `e` and `f`;
* blocks: `blk : Fin m → Fin k` sends `e` to its block; `S` is rainbow (`IsRainbow blk S`) if
  `blk` is injective on `S`; `blocksMet blk S` is the set of blocks met by `S`;
  `IsRainbowIndep N blk I`: `I` is independent in `N` and rainbow; `nu N blk = ν(N)`, the
  largest size of a rainbow independent set of `N`; `Av N blk = Av(N)`, the blocks missed by
  some rainbow independent set of size `ν(N)`; `IsRainbowBase N blk B`: `B` is a base of `N`
  and rainbow; `Opt N blk w`: the infimum of the weights `w(B)` of the rainbow bases `B`.

`C(B, e)` is Mathlib's `M.fundCircuit e B`.  For a base `B` and `e ∉ B` it is the unique
circuit in `B + e`; it is `{e}` when `e ∈ B`.  For any `I` with `e ∈ cl(I)` it equals
`{e} ∪ ⋂{J ⊆ I : e ∈ cl(J)}` (Mathlib's `fundCircuit_eq_sInter`).


## 1. Results

### 1.1 The least base weight

**Proposition 1.**  `isLeast_minBaseWeight`, `minBaseWeight_le`, `isMinBase_iff_sum_eq`,
`IsMinBase.sum_eq`, `exists_isMinBase`.  For every matroid `M` on `E` and `u ∈ ℝ^E`:
`β_M(u)` is the least element of the set of base weights `{u(B) : B a base}`; `β_M(u) ≤ u(B)`
for every base `B`; a set `B` is a minimum base if and only if `B` is a base and
`u(B) = β_M(u)`; minimum bases exist.

*Proof.*  Step 1, the set of base weights is finite and nonempty (Phase 1,
`basisWeights_finite`, `basisWeights_nonempty`), so its infimum belongs to it and is a lower
bound.  Step 2, if `B` is minimum, `u(B) ≤ u(B₀)` for a base `B₀` with `u(B₀) = β_M(u)`, and
`β_M(u) ≤ u(B)`; conversely `u(B) = β_M(u) ≤ u(B')` for every base `B'`.  Step 3, the base
`B₀` of Step 2 is minimum.

**Proposition 2.**  `minBaseWeight_eq_neg_maxBasisWeight`.  `β_M(u) = -h_M(-u)`, where
`h_M(w) = max_B w(B)` (Phase 1, `maxBasisWeight`).

*Proof.*  `-β_M(u) = -u(B₀)` is a weight of `-u`, and `-u(B') ≤ -β_M(u)` for every base
`B'`, so `-β_M(u)` is the greatest weight of `-u` (Phase 1, `maxBasisWeight_eq_of_isGreatest`).

### 1.2 Single exchanges

**Lemma 3.**  `sum_exchange`.  For `e ∉ B` and `f ∈ B`, `u(B - f + e) = u(B) - u_f + u_e`.

**Lemma 4.**  `isBase_exchange_iff`.  Let `N` be a matroid with ground set `E`, `B` a base of
`N`, `e ∉ B` and `f ∈ B`.  Then `B - f + e` is a base of `N` if and only if
`f ∈ C_N(B, e)`.

*Proof.*  Step 1, `e ∈ cl_N(B) = E`, so by Mathlib's `Indep.mem_fundCircuit_iff`,
`f ∈ C_N(B, e)` if and only if `(B + e) - f = B - f + e` is independent (`e ≠ f` since
`f ∈ B`).  Step 2, a base is independent, and an independent set of the form `B - f + e`
is a base (Mathlib's `IsBase.exchange_isBase_of_indep`).

### 1.3 Lemma `lem:minbases`(1) and (2)

**Theorem 5 (Lemma `lem:minbases`(1)).**  This is `Conn.isMinBase_iff_fundCircuit` of
`Rainbow/Connectivity.lean` (agent P0b), reused here and not proved again: for every matroid
`M` on `E`, `u ∈ ℝ^E` and `B ⊆ E`, `B` is a minimum base of `u` if and only if `B` is a base
and `u_f ≤ u_e` whenever `e ∉ B` and `f ∈ C(B, e)`.  Its two halves are
`Conn.le_of_mem_fundCircuit` and `Conn.isMinBase_of_forall_fundCircuit`; see
`notes/P0b-connectivity.md` for the proof.

**Lemma 6.**  `fundCircuit_subset_insert_of_mem_closure`.  For `J ⊆ I ⊆ E` and `e ∈ cl(J)`,
`C(I, e) ⊆ J + e`.

*Proof.*  `e ∈ cl(J) ⊆ cl(I)`, so `C(I, e) = {e} ∪ ⋂{J' ⊆ I : e ∈ cl(J')}`, and `J` is one
of the sets `J'`.

The *pointwise condition* for a set `B` is: `e ∈ cl(B ∩ {u ≤ u_e})` for every `e ∈ E`.

**Lemma 7.**  `isMinBase_of_forall_mem_closure`.  A base `B` that satisfies the pointwise
condition is a minimum base of `u`.

*Proof.*  Step 1, let `e ∉ B` and `f ∈ C(B, e)`.  Lemma 6 with `I = B` and
`J = B ∩ {u ≤ u_e}` gives `f = e` or `u_f ≤ u_e`; in both cases `u_f ≤ u_e`.  Step 2,
Theorem 5 makes `B` minimum.

**Lemma 8.**  `mem_closure_of_forall_fundCircuit`, `IsMinBase.mem_closure`.  Let `M` have
ground set `E`.  A base `B` with `u_f ≤ u_e` whenever `e ∉ B` and `f ∈ C(B, e)` satisfies the
pointwise condition; in particular every minimum base does.

*Proof.*  Step 1, if `e ∈ B`, then `e ∈ B ∩ {u ≤ u_e} ⊆ cl(B ∩ {u ≤ u_e})`.  Step 2, if
`e ∉ B`, then `C = C(B, e)` is a circuit containing `e` (Mathlib's
`IsBase.fundCircuit_isCircuit`), so `e ∈ cl(C - e)`.  Every `f ∈ C - e` lies in `B` (as
`C ⊆ B + e`) and has `u_f ≤ u_e` by hypothesis, so `C - e ⊆ B ∩ {u ≤ u_e}`.  Step 3, a
minimum base satisfies the hypothesis by Theorem 5.

**Theorem 9 (Lemma `lem:minbases`(2)).**  `isMinBase_iff_forall_subset_closure`.  Let `M` be
a matroid with ground set `E`, `u ∈ ℝ^E` and `B ⊆ E`.  Then `B` is a minimum base of `u` if
and only if `B` is a base of `M` and `{u ≤ c} ⊆ cl(B ∩ {u ≤ c})` for every `c ∈ ℝ`.

*Proof.*  Step 1, "only if" (`IsMinBase.subset_closure_le`): for `u_e ≤ c`, Lemma 8 gives
`e ∈ cl(B ∩ {u ≤ u_e})`, and `B ∩ {u ≤ u_e} ⊆ B ∩ {u ≤ c}`.  Step 2, "if": taking `c = u_e`
for each `e` gives the pointwise condition, and Lemma 7 applies.

**Corollary 10.**  `IsMinBase.isBasis_le`, `IsMinBase.isBasis_lt`.  Let `M` have ground set
`E` and `B` be a minimum base of `u`.  For every `c ∈ ℝ`, `B ∩ {u ≤ c}` is a basis of
`{u ≤ c}` and `B ∩ {u < c}` is a basis of `{u < c}`.

*Proof.*  Both sets are independent, as subsets of `B`.  They span: the first by Theorem 9;
for the second, if `u_e < c`, Lemma 8 gives `e ∈ cl(B ∩ {u ≤ u_e})` and
`B ∩ {u ≤ u_e} ⊆ B ∩ {u < c}`.

### 1.4 The level pieces

**Lemma 11.**  `levelPiece_isBasis_iff`, `levelPiece_isBase_iff`.  Let `M` have ground set
`E`, `ℓ ∈ ℝ`, and `J` a basis of `{u < ℓ}` in `M`.
(a) For `X ⊆ {u = ℓ}` and `I ⊆ X`: `I` is a basis of `X` in `L_ℓ` if and only if `I ∪ J` is
a basis of `X ∪ {u < ℓ}` in `M`.
(b) For `K ⊆ {u = ℓ}`: `K` is a base of `L_ℓ` if and only if `K ∪ J` is a basis of
`{u ≤ ℓ}` in `M`.

*Proof.*  Write `R = {u ≤ ℓ}` and `C = {u < ℓ}`, so `C ⊆ R`, `X ⊆ R` and `X ∩ C = ∅`.
Step 1, independence: `J` is also a basis of `C` in `M ↾ R`, so `I` is independent in
`L_ℓ = (M ↾ R) / C` if and only if `I ∪ J` is independent in `M`, `I ∪ J ⊆ R`, and `I` is
disjoint from `C` (Mathlib's `IsBasis.contract_indep_iff`, `restrict_indep_iff`).  Step 2,
closure: `cl_{L_ℓ}(I) = (cl(I ∪ C) ∩ R) \ C` (Mathlib's `contract_closure_eq`,
`restrict_closure_eq`), and `cl(I ∪ C) = cl(I ∪ J)` because `cl(C) = cl(J)`.  Step 3, `I` is
a basis of `X` in `L_ℓ` if and only if `I` is independent in `L_ℓ`, `I ⊆ X` and
`X ⊆ cl_{L_ℓ}(I)`.  If this holds, `I ∪ J` is independent in `M`, contained in `X ∪ C`, and
spans `X ∪ C`: `X ⊆ cl(I ∪ J)` by Step 2 and `C ⊆ cl(J)`.  Conversely, if `I ∪ J` is a basis
of `X ∪ C`, then `I ∪ J ⊆ R`, `I ⊆ X` misses `C`, and every `x ∈ X` lies in `cl(I ∪ J)`, in
`R` and outside `C`.  Step 4, (b) is (a) with `X = {u = ℓ}`, the ground set of `L_ℓ`, since
`{u = ℓ} ∪ {u < ℓ} = {u ≤ ℓ}` (`setOf_eq_union_lt`).

### 1.5 Lemma `lem:minbases`(3): the matroid `M^u`

`M^u` has ground set `E` (`Conn.minBases_ground` of `Rainbow/Connectivity.lean`, reused).  A
set `X` is a base of the direct sum `M^u` if and only if `X ∩ {u = ℓ}` is a base of `L_ℓ` for
every `ℓ ∈ ℝ` (`isBase_minBases_iff_levelPiece`, from Mathlib's
`disjointSigma_isBase_iff`).

**Lemma 12.**  `IsMinBase.isBase_minBases`.  Let `M` have ground set `E`.  Every minimum base
of `u` is a base of `M^u`.

*Proof.*  Fix `ℓ`.  By Corollary 10, `J = B ∩ {u < ℓ}` is a basis of `{u < ℓ}`, and
`(B ∩ {u = ℓ}) ∪ J = B ∩ {u ≤ ℓ}` is a basis of `{u ≤ ℓ}`.  Lemma 11(b) makes
`B ∩ {u = ℓ}` a base of `L_ℓ`.

**Lemma 13.**  `isMinBase_of_isBase_minBases`.  Let `M` have ground set `E`.  Every base of
`M^u` is a minimum base of `u`.

*Proof.*  Let `B` be a base of `M^u`.
Step 1, the pointwise condition, by strong induction on `n_e = |{x : u_x < u_e}|`.  Fix `e`
and a basis `J` of `{u < u_e}` in `M`.  Since `B ∩ {u = u_e}` is a base of `L_{u_e}`,
Lemma 11(b) makes `(B ∩ {u = u_e}) ∪ J` a basis of `{u ≤ u_e}`, so
`e ∈ cl((B ∩ {u = u_e}) ∪ J)`.  It suffices that `(B ∩ {u = u_e}) ∪ J ⊆ cl(B ∩ {u ≤ u_e})`.
The elements of `B ∩ {u = u_e}` lie in `B ∩ {u ≤ u_e}`.  An element `x ∈ J` has `u_x < u_e`,
so `{u < u_x}` is a proper subset of `{u < u_e}` (it misses `x`), `n_x < n_e`, and the
induction hypothesis gives `x ∈ cl(B ∩ {u ≤ u_x}) ⊆ cl(B ∩ {u ≤ u_e})`.
Step 2, `B` spans `M`, since every `e` lies in `cl(B ∩ {u ≤ u_e}) ⊆ cl(B)`; so `B` contains a
base `B₁` of `M`.
Step 3, `|B₁| = |B₀|` for a minimum base `B₀` (Proposition 1), both being bases of `M`, and
`|B₀| = |B|`, both being bases of `M^u` (Lemma 12).  Hence `B₁ ⊆ B` and `|B| ≤ |B₁|` give
`B₁ = B`, so `B` is a base of `M`.
Step 4, Lemma 7 makes `B` minimum.

**Theorem 14 (Lemma `lem:minbases`(3), first sentence).**  `isBase_minBases_iff`.  Let `M`
be a matroid with ground set `E` and `u ∈ ℝ^E`.  For every `B ⊆ E`, `B` is a base of `M^u`
if and only if `B` is a minimum base of `u`.  The ground set of `M^u` is `E`
(`Conn.minBases_ground`).

*Proof.*  Lemmas 12 and 13.

**Theorem 15 (Lemma `lem:minbases`(3), exchanges).**  `IsMinBase.isMinBase_exchange_iff`.
Let `M` have ground set `E`, `B` a minimum base of `u`, `e ∉ B` and `f ∈ B`.  Then
`B - f + e` is a minimum base of `u` if and only if `f ∈ C(B, e)` and `u_f = u_e`.

*Proof.*  Step 1, by Lemma 4, `B - f + e` is a base if and only if `f ∈ C(B, e)`, and by
Lemma 3, `u(B - f + e) = u(B) - u_f + u_e`.  Step 2, "only if": `B` and `B - f + e` are both
minimum, so `u(B) ≤ u(B - f + e)` and `u(B - f + e) ≤ u(B)`, which give `u_f = u_e`.
Step 3, "if": `B - f + e` is a base of weight `u(B)`, and `u(B) ≤ u(B')` for every base
`B'`.

**Theorem 16 (Lemma `lem:minbases`(3), circuits).**  `IsMinBase.fundCircuit_minBases`,
`IsMinBase.isCircuit_minBases`.  Let `M` have ground set `E`, `B` a minimum base of `u` and
`e ∉ B`.  The fundamental circuit of `e` with respect to `B` in `M^u` (the unique circuit of
`M^u` in `B + e`) is `{e} ∪ {f ∈ C(B, e) : u_f = u_e}`; in particular this set is a circuit
of `M^u`.

*Proof.*  `B` is a base of `M^u` (Lemma 12) and `M^u` has ground set `E`.  Fix `x`.
Step 1, `x = e` lies in both sets.  Step 2, for `x ∈ B`: by Lemma 4 in `M^u`, `x` lies in the
fundamental circuit in `M^u` if and only if `B - x + e` is a base of `M^u`, that is (Theorem
14) a minimum base of `u`, that is (Theorem 15) `x ∈ C(B, e)` and `u_x = u_e`.  Step 3, for
`x ∉ B + e`: `x` lies in neither set, since both fundamental circuits lie in `B + e`.
Step 4, the fundamental circuit of a base and an element outside it is a circuit (Mathlib's
`IsBase.fundCircuit_isCircuit`).

**Corollary 17.**  `isBase_of_isBase_minBases`, `card_of_isBase_minBases`, `rank_minBases`.
Let `M` have ground set `E`.  Every base of `M^u` is a base of `M` and has `r(M)` elements,
and `M^u` has rank `r(M)`.

*Proof.*  Theorem 14, and every base of `M` has `r(M)` elements (Phase 1, `card_base`).

**Corollary 18.**  `minBases_congr`, `minBases_congr_of_le_iff`, `minBases_eq_self`,
`minBases_eq_self_of_forall_eq`.  Let `M` have ground set `E` and `u, u' ∈ ℝ^E`.
(a) If `u_e ≤ u_f ⇔ u'_e ≤ u'_f` for all `e, f` with `connRel M e f` (`e = f` or `e` and `f`
on a common circuit, equivalently `e` and `f` in one component), then `M^u = M^{u'}`.
(b) If `u_e ≤ u_f ⇔ u'_e ≤ u'_f` for all `e, f`, then `M^u = M^{u'}`.
(c) If `u_e = u_f` whenever `connRel M e f`, then `M^u = M`.
(d) If `u` is constant, then `M^u = M`; so the bases of `M^u` are the bases of `M`.

*Proof.*  Step 1, (a) and (c) are `Conn.minBases_congr` and `Conn.minBases_eq_self` of
`Rainbow/Connectivity.lean`, whose hypotheses "the bases of `M^u` (and `M^{u'}`) are the
minimum bases" are Theorem 14.  Step 2, (b) and (d) are the special cases of (a) and (c) in
which the hypothesis holds for all pairs.

### 1.6 Equation `eq:rank-mu`

**Theorem 19 (equation `eq:rank-mu`).**  `rk_minBases`.  Let `M` be a matroid with ground
set `E`, `u ∈ ℝ^E` and `A ⊆ E`.  Then
`r_{M^u}(A) = Σ_{ℓ ∈ u(E)} (r({u < ℓ} ∪ (A ∩ {u = ℓ})) - r({u < ℓ}))`,
the sum over the set `u(E)` of values of `u`.  The subtraction is that of natural numbers;
every subtrahend is at most its minuend, since `r` is monotone, so each term is the exact
difference.  With the paper's notation, if `ℓ = ℓ_i` then `{u < ℓ_i} = {u ≤ ℓ_{i-1}} = U_{i-1}`
(and `{u < ℓ_1} = ∅ = U_0`), so the sum is the paper's sum.

*Proof.*  Step 1, let `I` be a basis of `A` in `M^u`; then `r_{M^u}(A) = |I|`, and
`|I| = Σ_{ℓ ∈ u(E)} |I ∩ {u = ℓ}|`.  Step 2, a basis of the direct sum meets each piece in a
basis (Mathlib's `disjointSigma_isBasis_iff`): `I ∩ {u = ℓ}` is a basis of `A ∩ {u = ℓ}` in
`L_ℓ`.  Step 3, fix `ℓ` and a basis `J` of `{u < ℓ}` in `M`.  Lemma 11(a) makes
`(I ∩ {u = ℓ}) ∪ J` a basis of `{u < ℓ} ∪ (A ∩ {u = ℓ})` in `M`; the two parts are disjoint,
so `r({u < ℓ} ∪ (A ∩ {u = ℓ})) = |I ∩ {u = ℓ}| + |J|`, while `r({u < ℓ}) = |J|`.  Subtracting
gives the `ℓ`-th term `|I ∩ {u = ℓ}|`.

### 1.7 Rainbow sets, `ν`, `Av` and `Opt`

Here `N` is any matroid on `E`, `blk : E → [k]` gives the blocks, and nothing is assumed on
the ground set of `N`.

**Lemma 20.**  `mem_blockSet`, `mem_blocksMet`, `IsRainbow.subset`, `IsRainbow.card_blocksMet`,
`IsRainbowIndep.subset`.  `e ∈ E_Q` if and only if `blk(e) ∈ Q`; `S` meets the block `b` if
and only if some `e ∈ S` has `blk(e) = b`; subsets of rainbow (independent) sets are rainbow
(independent); a rainbow set `S` meets exactly `|S|` blocks.

**Proposition 21.**  `IsRainbowIndep.card_le_nu`, `exists_isRainbowIndep_card_eq_nu`,
`nu_le`, `nu_le_rank`.  Every rainbow independent set of `N` has at most `ν(N)` elements;
some rainbow independent set has exactly `ν(N)` elements; `ν(N) ≤ k` and `ν(N) ≤ r(N)`.

*Proof.*  Step 1, `ν(N)` is the maximum of `|I|` over the finite family of rainbow
independent sets, which contains `∅`; so the maximum bounds every member and is attained.
Step 2, a rainbow set `I` of size `ν(N)` meets `|I|` distinct blocks among `k`.  Step 3, an
independent set has at most `r(E) ≤ r(N)` elements (Phase 1, `card_le_rk`, `rk_le_rank`).

**Proposition 22.**  `card_blocksMet_le_nu`, `nu_mono`.  (a) An independent set `I` of `N`
meets at most `ν(N)` blocks.  (b) If every base of `N` is a base of `N'` (the relation of
(F2)), then `ν(N) ≤ ν(N')`.

*Proof.*  (a) Choosing one element of `I` in each block that `I` meets gives a rainbow subset
`J ⊆ I`, independent, with as many elements as `I` meets blocks (Mathlib's
`Finset.exists_subset_injOn_image_eq_of_surjOn`); Proposition 21 bounds `|J|`.  (b) A rainbow
independent set `I` of `N` with `|I| = ν(N)` lies in a base of `N`, which is a base of `N'`,
so `I` is rainbow independent in `N'` and `ν(N) = |I| ≤ ν(N')`.

**Lemma 23.**  `mem_Av`.  `b ∈ Av(N)` if and only if some rainbow independent set `I` of `N`
with `|I| = ν(N)` misses the block `b`.

**Proposition 24.**  `IsRainbowBase.blocksMet_eq_univ`, `IsRainbowBase.existsUnique`,
`IsRainbowBase.sum_comp_blk`.  Let `N` have rank `k` and `B` be a rainbow base of `N`.  Then
`B` meets every block exactly once, and `Σ_{e ∈ B} p_{blk(e)} = Σ_{b=1}^{k} p_b` for every
`p` (with values in any commutative additive monoid).

*Proof.*  Step 1, `B` meets `|B| = r(N) = k` distinct blocks (Lemma 20), hence all `k`.
Step 2, two elements of `B` in one block coincide, as `B` is rainbow.  Step 3, `blk` maps `B`
bijectively onto the set of blocks, so the sums agree.

**Proposition 25.**  `nu_eq_rank_iff`, `nu_eq_iff`.  `ν(N) = r(N)` if and only if `N` has a
rainbow base.  If `N` has rank `k`, then `ν(N) = k` if and only if `N` has a rainbow base.

*Proof.*  Step 1, a rainbow base has `r(N)` elements, so `r(N) ≤ ν(N) ≤ r(N)`.  Step 2, if
`ν(N) = r(N)`, a rainbow independent set of size `ν(N)` is independent with `r(N)` elements,
hence a base (Mathlib's `Indep.isBase_of_eRk_ge`).  Step 3, the second statement is the
first with `r(N) = k`.

**Proposition 26.**  `finite_rainbowBaseWeights`, `Opt_le`, `exists_isRainbowBase_sum_eq_Opt`.
For `w ∈ ℝ^E`: the set of weights `w(B)` of the rainbow bases `B` of `N` is finite;
`Opt(w) ≤ w(B)` for every rainbow base `B`; and if `N` has a rainbow base, then
`Opt(w) = w(B)` for some rainbow base `B`.

*Proof.*  The set is contained in the finite image of all subsets of `E`; a finite set of
reals is bounded below, and a nonempty finite set contains its infimum.


## 2. Correspondence

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `β_M(u)` is the least base weight; minimum bases exist and attain it | `isLeast_minBaseWeight`, `minBaseWeight_le`, `isMinBase_iff_sum_eq`, `IsMinBase.sum_eq`, `exists_isMinBase` | `Rainbow/MinBases.lean` | proved |
| `β_M(u) = -h_M(-u)` | `minBaseWeight_eq_neg_maxBasisWeight` | same | proved |
| single exchanges | `sum_exchange`, `isBase_exchange_iff` | same | proved |
| `lem:minbases`(1) | `Conn.isMinBase_iff_fundCircuit` (halves `Conn.le_of_mem_fundCircuit`, `Conn.isMinBase_of_forall_fundCircuit`) | `Rainbow/Connectivity.lean` (P0b) | proved there, reused |
| pointwise condition `e ∈ cl(B ∩ {u ≤ u_e})` | `fundCircuit_subset_insert_of_mem_closure`, `isMinBase_of_forall_mem_closure`, `mem_closure_of_forall_fundCircuit`, `IsMinBase.mem_closure` | `Rainbow/MinBases.lean` | proved |
| `lem:minbases`(2) | `isMinBase_iff_forall_subset_closure` (with `IsMinBase.subset_closure_le`) | same | proved |
| `B ∩ {u ≤ c}`, `B ∩ {u < c}` are bases of the level sets | `IsMinBase.isBasis_le`, `IsMinBase.isBasis_lt` | same | proved |
| level pieces | `levelPiece_isBasis_iff`, `levelPiece_isBase_iff`, `isBase_minBases_iff_levelPiece` | same | proved |
| `lem:minbases`(3), "the minimum bases of `u` are the bases of a matroid `M^u`" | `isBase_minBases_iff` (with `IsMinBase.isBase_minBases`, `isMinBase_of_isBase_minBases`); ground set `Conn.minBases_ground` | same | proved |
| `lem:minbases`(3), "`B - f + e` is minimum iff `f ∈ C(B, e)` and `u_f = u_e`" | `IsMinBase.isMinBase_exchange_iff` | same | proved, with `f ∈ B` explicit (Section 3) |
| `lem:minbases`(3), "the circuit of `e` in `B + e` in `M^u` is `{e} ∪ {f ∈ C(B, e) : u_f = u_e}`" | `IsMinBase.fundCircuit_minBases`, `IsMinBase.isCircuit_minBases` | same | proved |
| bases of `M^u` are bases of `M` with `r(M)` elements | `isBase_of_isBase_minBases`, `card_of_isBase_minBases`, `rank_minBases` | same | proved |
| `M^u` depends only on comparisons within components; only on the order of `u`; `M^u = M` for `u` constant (on components) | `minBases_congr`, `minBases_congr_of_le_iff`, `minBases_eq_self`, `minBases_eq_self_of_forall_eq` | same | proved (unconditional forms of `Conn.minBases_congr`, `Conn.minBases_eq_self`) |
| `eq:rank-mu` | `rk_minBases` | same | proved |
| blocks, rainbow sets | `mem_blockSet`, `mem_blocksMet`, `IsRainbow.subset`, `IsRainbow.card_blocksMet`, `IsRainbowIndep.subset` | same | proved |
| `ν(N)`: attained, `ν ≤ k`, `ν ≤ r`, monotone under (F2), bounds the blocks met by an independent set | `IsRainbowIndep.card_le_nu`, `exists_isRainbowIndep_card_eq_nu`, `nu_le`, `nu_le_rank`, `nu_mono`, `card_blocksMet_le_nu` | same | proved |
| `Av(N)` unfolded | `mem_Av` | same | proved |
| a rainbow base of a rank-`k` matroid meets every block once (Lemma `lem:duality`, Step 1) | `IsRainbowBase.blocksMet_eq_univ`, `IsRainbowBase.existsUnique`, `IsRainbowBase.sum_comp_blk` | same | proved |
| `ν = r` (`ν = k` at rank `k`) iff a rainbow base exists | `nu_eq_rank_iff`, `nu_eq_iff` | same | proved |
| `Opt(w)` is a lower bound, attained when a rainbow base exists | `finite_rainbowBaseWeights`, `Opt_le`, `exists_isRainbowBase_sum_eq_Opt` | same | proved |


## 3. Differences from the paper

1. **`f ∈ B` in item 3.**  The paper writes "the base `B - f + e` is minimum if and only if
   `f ∈ C(B, e)` and `u_f = u_e`" with `f` unquantified.  The statement needs `f ∈ B`: for
   `f = e` the right-hand side holds (`e ∈ C(B, e)`), while `B - e + e = B + e` is not a
   base.  Lean: `IsMinBase.isMinBase_exchange_iff` assumes `e ∉ B` and `f ∈ B`.  Proposed
   wording: "For a minimum base `B`, `e ∉ B` and `f ∈ B`, the set `B - f + e` is a minimum
   base if and only if `f ∈ C(B, e)` and `u_f = u_e`, so the circuit of `e` in `B + e` in
   `M^u` is `{e} ∪ {f ∈ C(B, e) : u_f = u_e}`."
2. **The matroid `M^u` is concrete.**  The paper asserts that the minimum bases are the bases
   of "a matroid `M^u`", and reads the rank function of `M^u` along the level sets of `u`.
   `Rainbow/Defs.lean` fixes `M^u` as the direct sum over the values `ℓ` of the level pieces
   `(M ↾ {u ≤ ℓ}) / {u < ℓ}`; Theorem 14 shows that its bases are the minimum bases, and
   Theorem 19 is then the rank formula of this direct sum.  A matroid is determined by its
   bases, so any matroid on `E` whose bases are the minimum bases equals this one.  Optional wording
   for the paper, after item 3: "Explicitly, `M^u` is the direct sum over the values `ℓ` of
   `u` of the matroids `(M | {u ≤ ℓ}) / {u < ℓ}` on the level sets `{u = ℓ}`."
3. **The sets `U_{i-1}` of `eq:rank-mu`.**  Lean writes `{u < ℓ}` for `U_{i-1}` when
   `ℓ = ℓ_i`; the two sets are equal, so the formula is the paper's.  The subtraction in Lean
   is that of natural numbers; it is exact because `r` is monotone (Theorem 19).  No change
   to the paper is needed.
4. **Item 1 is P0b's theorem.**  Lemma `lem:minbases`(1) is proved in
   `Rainbow/Connectivity.lean` as `Conn.isMinBase_iff_fundCircuit`, for every matroid on
   `E` without a ground-set hypothesis; this module reuses it (Lemma 7, Lemma 8) instead of a
   second proof.  The unconditional forms of P0b's `Conn.minBases_congr` and
   `Conn.minBases_eq_self` are Corollary 18 (a) and (c).
5. **Ground set.**  Lemma `lem:minbases`(2), (3) and `eq:rank-mu` carry the hypothesis that
   `M` has ground set `E` (`M.E = Set.univ`), the paper's standing convention.  Item 2 is
   false without it (an element outside the ground set lies in no closure).
6. **`Opt` without rainbow bases.**  `Opt` in `Rainbow/Defs.lean` is an infimum, which Lean
   sets to `0` when there is no rainbow base.  The paper assumes that `M` has a rainbow base,
   and `exists_isRainbowBase_sum_eq_Opt` carries that assumption.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/MinBases.lean` | 516 |


## 5. Not done

* Lemma `lem:minbases`(4) (connected components) is the module `Rainbow/Connectivity.lean` of
  agent P0b, by assignment.
* The rank formula `eq:rank-mu` applied within components (Lemma `lem:observer`, Step 3) is
  not stated separately; it follows from Theorem 19, Corollary 18 and P0b's
  `Conn.isMinBase_iff_comp`, and belongs to the observer.
* Item 1 is not proved a second time (Section 3, item 4).
