# Truncations

Module: `SignedTropical/Rainbow/Truncation.lean` (namespace `SignedTropical.Rainbow.Trunc`).
Paper: `greedy_intersection.tex`, proof of Theorem `thm:D`, Step 4, where the padded matroid
`M_i'` is the truncation at `m` of the direct sum of `M_i` and the free matroid on `m` new
elements (`TheoremD.pad`, notes/P8-theoremD.md).  Mathlib has no truncation.

## 1. Results

### 1.1 The truncation (`truncate`, `indep_truncate_iff`)

Definition.  The truncation of `M` at `j` is the matroid whose independent sets are the
independent sets of `M` with at most `j` elements.

Proof that it is a matroid.  Step 1.  The empty set qualifies and subsets of qualifying sets
qualify.  Step 2, augmentation.  If `I, J` qualify and `|I| < |J|`, augmentation in `M` gives
`e ∈ J ∖ I` with `I + e` independent in `M`, and `|I + e| = |I| + 1 ≤ |J| ≤ j`.

### 1.2 Rank (`rk_truncate`, `rank_truncate`)

Statement.  `r_j(S) = min(r(S), j)`; in particular the truncation at `j ≤ r(M)` has rank `j`.

Proof.  Step 1, upper bound.  A basis of `S` in the truncation is independent in `M` inside `S`,
so it has at most `r(S)` elements, and at most `j` by definition.  Step 2, lower bound.  A basis
`I` of `S` in `M` has `r(S)` elements; a subset of `I` with `min(r(S), j)` elements is independent
in the truncation.

### 1.3 Bases (`isBase_truncate_iff`)

Statement.  For `j ≤ r(M)`, the bases of the truncation at `j` are the independent sets of `M`
with `j` elements.

Proof.  Step 1.  A base of the truncation is independent in `M` and has as many elements as the
rank `j` (1.2).  Step 2.  Conversely an independent set of the truncation with `j` elements
reaches the rank, so it is a base.

## 2. Correspondence

| Paper | Lean | Status |
|---|---|---|
| `thm:D`, Step 4, the truncation at `m` in the padded matroids: rank function and bases | `truncate`, `rk_truncate`, `rank_truncate`, `isBase_truncate_iff` | proved |

## 3. Module size

`Truncation.lean`: 80 lines.
