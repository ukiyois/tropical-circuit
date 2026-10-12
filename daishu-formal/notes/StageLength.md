# The stage length (Theorem `thm:stagelength`)

Module: `SignedTropical/Rainbow/StageLength.lean` (namespace `SignedTropical.Rainbow.StageLength`),
written by the coordinator.  Paper: `greedy_intersection.tex`, Section 4.6, Theorem
`thm:stagelength` and its proof, Steps 1 to 5.

Setting.  `M : Matroid (Fin m)` has ground set `univ`, rank `k` and a rainbow base; the blocks are
the fibres of `blk : Fin m → Fin k`.  At a state `v` with `ν₀ = ν(M^v) = r < k`, `S = Av(M^v)`,
`X = E_S`, `ρ = |S| - (k - r)`, `N` is the PO-SL family, `a` its update, `v' = v - a_blk`, and `δ`
is the first event of Step 3 of Theorem `thm:potential` (`Potential.exists_first_event`).

## 1. Results

### 1.1 Bases meeting `r` blocks (`card_inter_eq_rk`)

Statement.  A base `B` of `M^v` meeting exactly `r` blocks has `|B ∩ X| = r_{M^v}(X)`.

Proof.  Step 1.  `|S| + r = k + r_{M^v}(X)` (Lemma `lem:avoidable`(2),
`Exchange.card_av_add_nu`).  Step 2.  `|B ∩ X| ≤ r_{M^v}(X)`, as `B ∩ X` is independent in `M^v`.
Step 3.  The `k - r` blocks missed by `B` include `S \ blocksMet(B)`, so `B ∩ X` meets at least
`|S| - (k - r)` blocks, and `|B ∩ X|` is at least the number of blocks it meets.

### 1.2 The crossing pair (`exists_pair`)

Statement.  Let `ν₀ = r`, `B` a base of `M^v` meeting `r` blocks, and `δ ≥ 0` with
`r_{N(δ)}(X) > r_{M^v}(X)`.  Then some `x ∈ X` and `z ∉ X` in one component of `M`, one of them
in `B`, have `0 < v_x - v_z ≤ δ`.

Proof.  Step 1.  By 1.1, Step 5 of Theorem `thm:potential` applies to `B`
(`Potential.exists_tie_of_isBase`): `g ∈ B \ X`, `y ∈ X \ B` in one cluster `C` at scale `δ`,
`v_g < v_y`.  Its last argument (`Potential.lt_of_mem_fundCircuit`): for `f ∈ X \ B` and
`b ∈ C(B, f) \ X`, `v_b < v_f`.  Step 2.  `z₂` has the least value above `v_g` in `C ∩ X`, `z₁`
the largest value below `v_{z₂}` in `C \ X`; no value of `C` lies strictly between, so
`v_{z₂} - v_{z₁} ≤ δ` (`POSL.SameCluster.sub_le`).  Step 3.  If `z₂ ∈ B`: `(z₂, z₁)`.  Step 4.
Otherwise `z₂ ∈ PO_δ` gives `b ∈ C(B, z₂) - z₂` with `v_{z₂} - δ ≤ v_b ≤ v_{z₂}`; `b ∈ B ⊆ PO_δ`
and `b` is linked to `z₂`, so `b ∈ C`.  If `b ∉ X`: `v_b < v_{z₂}` by Step 1, take `(z₂, b)`.  If
`b ∈ X` and `v_b = v_{z₂}`: `(b, z₁)`.  If `b ∈ X` and `v_b < v_{z₂}`: `v_b ≤ v_g` by the choice of
`z₂`, take `(z₂, g)`.  Every pair lies in the cluster `C`, hence in one component
(`POSL.SameCluster.conn`).

### 1.3 Every update makes a pair cross (`exists_crossing_pair`, `crossPairs_ssubset`)

Theorem `thm:stagelength`(1) is `exists_crossing_pair`: the pair of 1.2 at the first event has
`v'_x ≤ v'_z` after the update.

Definition.  `crossPairs blk S B v` is the set of pairs `(x, z)` with `x ∈ X`, `z ∉ X`,
`x ∈ B` or `z ∈ B`, and `v_z < v_x`.  It has at most `|B| m` elements (`card_crossPairs_le`): a
pair has its first element in `B ∩ X` or its second in `B \ X`.

Statement.  Let `ν₀ = r < k` and `B` a base of `M^v` meeting `r` blocks.  Then the pairs at `v'`,
formed with the same `S` and `B`, are a proper subset of the pairs at `v`.

Proof.  Step 1.  `a_b = τ` for `b ∈ S` and `a_b ≤ τ` otherwise, so `v'_z < v'_x` implies
`v_z < v_x`.  Step 2.  The pair `(x, z)` of 1.2 at the first event `δ` (`rk_lt_rk` gives the rank
jump) lies at `v`, and `a_{blk z} ≤ τ - δ` gives `v'_x - v'_z ≤ (v_x - v_z) - δ ≤ 0`.

### 1.4 The least number of pairs (`minCross`, `minCross_bounds`, `minCross_lt`)

Definition.  `minCross M blk v = Q(v)`, the least `|crossPairs blk S B v|` over the bases `B` of
`M^v` meeting `ν(M^v)` blocks (`exists_minCross_eq`, `minCross_le`).

Statements.  At a state of stage `r < k`, `1 ≤ Q(v) ≤ k m`.  If `ν₀(v') = r` and
`Av(M^{v'}) = S`, then `Q(v') < Q(v)`.

Proof.  Bounds: a base attaining `Q(v)` has a pair by 1.3, and `|B| = k`.  Decrease: a base `B`
attaining `Q(v)` is a base of `M^{v'}` meeting `r` blocks (Theorem `thm:validity`(2),
`isMinBase_update`), so `Q(v') ≤ |crossPairs(B, v')| < |crossPairs(B, v)| = Q(v)` by 1.3.

### 1.5 An epoch with `ρ = 0` takes one update (`av_ne_of_rk_eq_zero`)

Statement.  Let `ν₀ = r < k` and `r_{M^v}(X) = 0`.  If `ν(M^{v'}) = r`, then `Av(M^{v'}) ≠ S`.

Proof.  Step 1.  At `δ`, `r_{N(δ)}(X) > 0`, so some `y ∈ X` lies in a base of `N(δ)`, hence in
`PO_δ` (`POSL.subset_PO_of_isBase_N`).  Step 2.  If `Av(M^{v'}) = S`, then
`r_{M^{v'}}(X) = 0` by Lemma `lem:avoidable`(2), and a minimum base `B'` of `v'` misses `X`.
Step 3.  For `f ∈ C(B', y) - y`, `v'_f < v'_y` (`lt_of_mem_fundCircuit` at `v'` and `B'`),
`v'_y = v_y - τ` and `v'_f ≥ v_f - (τ - δ)`, so `v_f < v_y - δ`, and `y` lies in the closure of
`{f : v_f < v_y - δ}`, against `y ∈ PO_δ`.

### 1.6 The potential and the stage bound (`Phi₂`, `lt_of_nu_iterate_eq`)

Definition.  `phiVal ρ K Q = 0` for `ρ = 0` and `ρ K + 1 - Q` otherwise;
`Phi₂ M blk w r p = phiVal (|S| + r - k) (k m) (Q(w - p_blk))`.

Statements.  At a state of stage `r < k`, `Φ₂ < 1 + (r - 1) k m` (`Phi₂_lt`).  If `ν₀ = r` before
and after the stage map, `Φ₂` grows (`Phi₂_lt_Phi₂_stageMap`).  Hence from `ν₀(p) ≥ r`, an iterate
`n` with `ν₀ = r` has `n ≤ Φ₂ < 1 + (r - 1) k m` (`le_Phi₂_iterate`, `lt_of_nu_iterate_eq`).

Proof.  Bound: `k - r ≤ |S| ≤ k - 1` (`Potential.card_av_bounds`), so `ρ ≤ r - 1`, and
`Φ₂ ≤ ρ k m` as `Q ≥ 1`.  Growth: `S` grows or stays (`av_subset_av_update`).  If it stays, then
`ρ ≠ 0` by 1.5, and `Q` decreases by 1.4.  If it grows, `ρ` grows, and `Φ₂` passes from at most
`ρ k m` to at least `(ρ + 1) k m + 1 - k m` (as `Q ≤ k m`).

### 1.7 Components of rank one (`Rainbow/RankOne.lean`, Corollary `cor:rankone`)

Hypothesis `hpar`: every circuit of `M` has at most two elements, that is every component has
rank at most one (the assignment problem is the case of a partition matroid with unit
capacities).

Statement (`av_ne_av`).  At `ν₀ = r < k`, if `ν(M^{v'}) = r`, then `Av(M^{v'}) ≠ S`.  Consequently
(`card_av_lt`, `le_card_av_iterate`, `lt_of_nu_iterate_eq`) the iterates of the stage-`r` map
with `ν₀ = r` have index `n < r`: stage `r` ends after at most `r` updates
(`Schedule.validLength_rankOne`).

Proof.  Step 1.  The pair `(x, z)` of `exists_crossing_pair` lies in one component and `x ≠ z`, so
`{x, z}` is a circuit (`isCircuit_pair`).  Step 2.  If `x ∈ B`, then `z ∉ B`,
`C(B, z) = {x, z}` (`IsCircuit.eq_fundCircuit_of_subset`) and `v_x ≤ v_z`
(`Conn.le_of_mem_fundCircuit`), against `v_z < v_x`.  So `z ∈ B` and `z ∈ C(B, x)`.  Step 3.  `B`
is a minimum base of `v'` (`isMinBase_update`), and if `Av(M^{v'}) = S` then
`|B ∩ X| = r_{M^{v'}}(X)` (both `|S| + r - k`), so `Potential.lt_of_mem_fundCircuit` at `v'` gives
`v'_z < v'_x`, against `v'_x ≤ v'_z`.  Step 4.  `|S₀|` grows strictly at every update of the
stage (`av_subset_av_update`), and `k - r ≤ |S₀| ≤ k - 1` (`card_av_bounds`), so
`n ≤ |S₀| + r - k ≤ r - 1`.

## 2. Correspondence

| Paper | Lean | Status |
|---|---|---|
| `thm:stagelength`, Step 1 | `card_inter_eq_rk`, `Potential.exists_tie_of_isBase`, `Potential.lt_of_mem_fundCircuit` | proved |
| `thm:stagelength`, Step 2 | `exists_pair` | proved |
| `thm:stagelength`(1), Step 3 | `exists_crossing_pair`, `crossPairs_ssubset` | proved |
| `cor:rankone` | `RankOne.isCircuit_pair`, `RankOne.av_ne_av`, `RankOne.lt_of_nu_iterate_eq`, `Schedule.validLength_rankOne` | proved |
| `thm:stagelength`(2), Step 4 | `av_ne_of_rk_eq_zero` | proved |
| `thm:stagelength`, Step 5 (counting) | `card_crossPairs_le`, `minCross_bounds`, `minCross_lt`, `Phi₂_lt`, `Phi₂_lt_Phi₂_stageMap`, `lt_of_nu_iterate_eq`, `Schedule.stage_bound` | proved |

The paper counts epochs; the proof here packs the epochs and the pairs into one potential, as
`Potential.lean` does for Theorem `thm:potential`.

## 3. Module size

`StageLength.lean`: 430 lines; `RankOne.lean`: 137 lines.
