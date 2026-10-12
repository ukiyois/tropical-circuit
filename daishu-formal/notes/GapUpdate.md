# The update as a gap sum over pairs

Module: `SignedTropical/Rainbow/GapUpdate.lean` (namespace `SignedTropical.Rainbow.GapUpdate`),
written by the coordinator.  Paper: `greedy_intersection.tex`, Lemma `lem:oneupdate`, Step 2.

## 1. Definitions

* The ordered pairs `(e, f)` are indexed by `Fin (m * m)` through `finProdFinEquiv`
  (`pairOf`); `relOf S` is the relation read from a set of pair indices.
* `Dplus v`: `D⁺_{ef} = max(v_f - v_e, 0)`.
* `obs M blk r b S`: the observable `F_b(G) = [ν(N_G) ≤ r] ∧ [b ∈ Av(N_G)]` of Lemma
  `lem:observer`, at `G = relOf S`, as `1` or `0`.

## 2. Results

### 2.1 Sublevel sets (`relOf_sublevel`, `relOf_univ`)

Statement.  For `t ≥ 0` the sublevel set `{(e, f) : D⁺_{ef} ≤ t}` is `G_t`.

Proof.  `max(v_f - v_e, 0) ≤ t` iff `v_f - v_e ≤ t`, since `0 ≤ t`.

### 2.2 The top level (`obs_univ`)

Statement.  If `M` has rank `k`, a rainbow base, and `r < k`, then `F_b(E × E) = 0`.

Proof.  `N_{E×E} = M` (`POSL.NG_univ`), and `ν(M) = k > r` because `M` has a rainbow base.

### 2.3 Gap sums read only sublevel sets (`gapSum_congr_sublevel`)

Statement.  For `D ≥ 0`, two observables that agree on every sublevel set `{D ≤ t}` with
`t ≥ 0` have the same gap sum.

Proof.  The gap sum evaluates `F` only at `G_k = {D ≤ s_k}`, and `s_k ≥ s_0 = 0`.

This is what lets the compiler run with an observer that is correct only on the relations `G_t`:
the observable computed by the circuit agrees with `F_b` on every sublevel set of `D⁺`.

### 2.4 Lemma `lem:oneupdate`, Step 2 (`update_eq_gapSum`)

Statement.  Let `M` have rank `k` and a rainbow base, `v` a weight, `r ≤ ν(M^v)` and `r < k`.
For every block `b`, the PO-SL update satisfies `a_b = C_{F_b}(D⁺)`.

Proof.  Step 1.  By `eq:update-integral` (`Validity.update_eq_integral`, applied to the
admissible family `POSL.N`), `a_b = ∫_{t>0} [ν(N(t)) ≤ r]·[b ∈ Av(N(t))] dt`.  Step 2.  By 2.2
and the integral reading of the gap sum (`Integral.gapSum_eq_integral_Ioi`),
`C_{F_b}(D⁺) = ∫_{t>0} F_b(G_t(D⁺)) dt`.  Step 3.  For `t > 0`, 2.1 and Proposition `prop:posl`
(`POSL.N_eq_NG`) identify the integrands.

## 3. Correspondence

| Paper | Lean | Status |
|---|---|---|
| `lem:oneupdate`, Step 1 (`D⁺` and its sublevel sets) | `Dplus`, `relOf_sublevel` | proved |
| `lem:oneupdate`, Step 2 | `update_eq_gapSum`, `obs_univ`, `gapSum_congr_sublevel` | proved |

## 4. Module size

`GapUpdate.lean`: 86 lines.
