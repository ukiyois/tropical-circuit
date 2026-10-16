# P1 core: the Lagrangian and possibly optimal bases

Modules: `SignedTropical/Rainbow/PossiblyOptimal.lean`, `SignedTropical/Rainbow/Lagrangian.lean`
(namespace `SignedTropical.Rainbow.Pos`), written by the coordinator.  Paper:
`greedy_intersection.tex`, Sections 4.1 and 4.2.  Throughout, `M` is a matroid on
`E = {0, ..., m-1}` (Mathlib's `Matroid (Fin m)` with ground set `univ`), `C(B, e)` is Mathlib's
fundamental circuit `M.fundCircuit e B`, and `v - t 1_B` is `tilt v t B`.

## 1. Results

### 1.1 `θ` read through single exchanges (`theta_le_iff`, `theta_nonneg`)

Statement.  For a set `B` and `t ∈ ℝ`, `θ(B) ≤ t` if and only if `0 ≤ t` and `v_f - v_e ≤ t`
whenever `e ∉ B` and `f ∈ C(B, e)`.  In particular `θ(B) ≥ 0`.

Proof.  Step 1, the definition.  `θ(B)` is the largest of `0` and the numbers `v_f - v_e` over
the pairs with `e ∉ B` and `f ∈ C(B, e)`.  Step 2.  A maximum of finitely many numbers is at most
`t` exactly when each of them is.

### 1.2 Proposition `prop:pos` (`tfae_pos`, `theta_le_iff_isMinBase`)

Statement.  Let `B` be a base and `t ≥ 0`.  The following are equivalent.
1. `θ(B) ≤ t`.
2. `B` is a minimum base for `v - t 1_B`.
3. `v(B) - v(B') ≤ t |B ∖ B'|` for every base `B'`.
4. `e ∈ cl(B ∩ {g : v_g ≤ v_e + t})` for every `e ∈ E`.
5. `B` is a minimum base for some `u` with `|u_e - v_e| ≤ t/2` for every `e`.

Proof.  All five are read through Lemma `lem:minbases`(1) (`Conn.isMinBase_iff_fundCircuit`):
a base `B` is minimum for `u` iff `u_f ≤ u_e` whenever `e ∉ B` and `f ∈ C(B, e)`.

Step 1, (1) iff (2).  Let `u = v - t 1_B`, `e ∉ B` and `f ∈ C(B, e)`.  If `f = e` both sides
hold, the first because `t ≥ 0`.  Otherwise `f ∈ B`, so `u_f = v_f - t` and `u_e = v_e`, and
`u_f ≤ u_e` reads `v_f - v_e ≤ t`.

Step 2, (2) implies (3).  For every set `S`, `u(S) = v(S) - t |S ∩ B|` (`sum_tilt`).  So
`u(B) ≤ u(B')` reads `v(B) - t|B| ≤ v(B') - t|B' ∩ B|`, and `|B| - |B ∩ B'| = |B ∖ B'|`.

Step 3, (3) implies (1).  Let `e ∉ B` and `f ∈ C(B, e)`.  If `f = e`, then `v_f - v_e = 0 ≤ t`.
Otherwise `f ∈ B`, `B' = B - f + e` is a base (`isBase_exchange_iff`), `B ∖ B' = {f}`, and
`v(B) - v(B') = v_f - v_e`, so (3) gives `v_f - v_e ≤ t`.

Step 4, (2) iff (4).  By `lem:minbases`, a base `B` is minimum for `u` iff
`e ∈ cl(B ∩ {x : u_x ≤ u_e})` for every `e` (`IsMinBase.mem_closure`,
`isMinBase_of_forall_mem_closure`).  For `e ∈ B` both this condition and the condition of (4) at
`e` hold, since `e` belongs to both sets (for (4), because `t ≥ 0`).  For `e ∉ B` the two sets
coincide: for `x ∈ B`, `u_x ≤ u_e` reads `v_x - t ≤ v_e`.

Step 5, (2) implies (5).  `u' = v - t 1_B + (t/2) 1` has the same comparisons as `v - t 1_B`,
hence the same minimum bases (`Conn.isMinBase_congr`), and `|u'_e - v_e| = t/2` for every `e`.

Step 6, (5) implies (1).  For `e ∉ B` and `f ∈ C(B, e)`, `u_f ≤ u_e`, so
`v_f - v_e ≤ (u_f + t/2) - (u_e - t/2) ≤ t`.

### 1.3 The remark after Proposition `prop:pos` (`pos_mono`, `mem_pos_zero`, `mem_pos_iff_isBase`)

Statement.  `P_t ⊆ P_{t'}` for `t ≤ t'`; `P_0` is the set of bases of `M^v`; and for `t ≥ 0`
with `v_f - v_e ≤ t` for all `e, f` (that is, `t ≥ max v - min v`), `P_t` is the set of all
bases of `M`.

Proof.  Step 1.  `P_t` is cut out by `θ(B) ≤ t`, which is monotone in `t`.  Step 2.  At `t = 0`,
`v - 0·1_B = v`, so Step 1 of 1.2 makes `P_0` the minimum bases of `v`, which are the bases of
`M^v` by `lem:minbases`(3) (`isBase_minBases_iff`).  Step 3.  If every difference `v_f - v_e` is
at most `t`, every base satisfies the condition of 1.1.

### 1.4 Lemma `lem:path` (`mem_pos_of_isMinBase_shift`)

Statement.  Let `s ≥ 0` and `y ∈ [0, s]^k`.  Every minimum base of `v - y_blk` lies in `P_s`.

Proof.  Step 1.  For `e ∉ B` and `f ∈ C(B, e)`, `lem:minbases`(1) gives
`v_f - y_{blk(f)} ≤ v_e - y_{blk(e)}`.  Step 2.  So `v_f - v_e ≤ y_{blk(f)} - y_{blk(e)} ≤ s - 0`,
and 1.1 applies.

### 1.5 Lemma `lem:duality` (`psi_le_opt`, `psi_eq_opt`, `sum_eq_add_shift`)

Statement.  Let `M` have rank `k`, with blocks `R_1, ..., R_k`, and `v = w - p_blk`.
(a) If `M` has a rainbow base, then `Ψ(p) ≤ Opt(w)` for every `p`.
(b) If `ν₀ = ν(M^v) = k`, then `Ψ(p) = Opt(w)`.

Proof.  Step 1.  A rainbow base `B` meets every block once (`IsRainbowBase.sum_comp_blk`), so
`w(B) = Σ_b p_b + v(B) ≥ Σ_b p_b + β_M(v) = Ψ(p)`.  Applied to a rainbow base of weight
`Opt(w)` (`exists_isRainbowBase_sum_eq_Opt`) this is (a).  Step 2.  If `ν(M^v) = k`, the
matroid `M^v` of rank `k` (`rank_minBases`) has a rainbow base `B` (`nu_eq_iff`), which is a
minimum base of `v` (`isBase_minBases_iff`) and a rainbow base of `M`.  Step 1 holds with
equality for it, so `Opt(w) ≤ w(B) = Ψ(p) ≤ Opt(w)`.

## 2. Correspondence

| Paper | Lean | Module | Status |
|---|---|---|---|
| Definition `def:theta`, read through exchanges | `theta_le_iff`, `theta_nonneg` | `PossiblyOptimal.lean` | proved |
| Proposition `prop:pos` | `tfae_pos`, `theta_le_iff_isMinBase` | `PossiblyOptimal.lean` | proved |
| Remark after `prop:pos` | `pos_mono`, `mem_pos_zero`, `mem_pos_iff_isBase` | `PossiblyOptimal.lean` | proved |
| Lemma `lem:path` | `mem_pos_of_isMinBase_shift` | `PossiblyOptimal.lean` | proved |
| Lemma `lem:duality` | `psi_le_opt`, `psi_eq_opt` | `Lagrangian.lean` | proved |

## 3. Differences from the paper

1. Lemma `lem:path` assumes `s ≥ 0` explicitly.  The paper's hypothesis `y ∈ [0, s]^k`
   presupposes it, but for `k = 0` it would not imply it, and `θ ≥ 0` makes the conclusion false
   for `s < 0`.  No change to the paper is needed; the paper applies the lemma with `s ∈ [0, τ]`.
2. The remark "`P_t` is all of `Bases(M)` for `t ≥ max v - min v`" is stated with the
   hypotheses `t ≥ 0` and `v_f - v_e ≤ t` for all `e, f`, which is `t ≥ max v - min v` when
   `m ≥ 1`.
3. The reading "`P_t` is the family of bases that are possibly optimal for the interval weights
   `[v - t/2, v + t/2]`" is item 5 of Proposition `prop:pos`.

## 4. Module sizes

`PossiblyOptimal.lean` 144 lines, `Lagrangian.lean` 50 lines.

## 5. Not done here

Proposition `prop:notmatroid` and Lemma `lem:doubling` are in `NotMatroid.lean` and
`Doubling.lean` (notes/P1x-partition-doubling.md).
