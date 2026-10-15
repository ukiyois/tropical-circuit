# The schedule of Theorem C

Module: `SignedTropical/Rainbow/Schedule.lean` (namespace `SignedTropical.Rainbow.Schedule`),
written by the coordinator.  Paper: `greedy_intersection.tex`, proof of Theorem `thm:C`, Steps 1,
2 and 4, and the use of Lemma `lem:duality` in Step 3.

## 1. Definitions

* `ValidLength M blk L`: stage lengths `L : ℕ → ℕ` are valid if, at every weight `w`, every stage
  `r < k` ends within `L r` updates: from every `p` with `ν₀(p) ≥ r`, `L r` iterations of the
  stage-`r` map reach `ν₀ ≥ r + 1`.
* `stageLength k m r = min(r(⌊m²/4⌋ + 1), 1 + (r - 1) k m, 1 + k (2m - k - 1))`: the smallest of
  the bounds of Theorems `thm:potential` and `thm:stagelength`.
* `schedule L M blk w j p`: stages `1, …, j` in order, stage `r` applying the PO-SL stage map
  `Potential.stageMap M blk w r` (that is `p ↦ p + a(p)`) `L r` times.
* `rounds k m = Σ_{r<k} stageLength k m r`, the number of updates of the general schedule.

## 2. Results

### 2.1 Valid stage lengths (`validLength_of_lt`, `validLength_stageLength`, `validLength_rankOne`)

Statement.  Let `M` have ground set `E`, rank `k` and a rainbow base.  Stage lengths `L` are valid
as soon as every iterate of the stage-`r` map with `ν₀ = r`, from a state with `ν₀ ≥ r`, has
index below `L r`.  So `stageLength k m` is valid, and `L r = r` is valid when every component
of `M` has rank at most one (`hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1`).

Proof.  Step 1.  `ν₀` does not decrease along the iterates (`Potential.le_nu_iterate`); if the
iterate `n = L r` had `ν₀ = r`, then `n < L r = n`.  Step 2.  For `stageLength`, an iterate with
`ν₀ = r` has `n < r(⌊m²/4⌋ + 1)` (`Potential.lt_of_nu_iterate_eq`), `n < 1 + (r - 1) k m`
(`StageLength.lt_of_nu_iterate_eq`) and `n < 1 + k (2m - k - 1)`
(`StageLength.lt_of_nu_iterate_eq_fixed`), so `n < min(…)`.  Step 3.  For components of rank one,
`n < r` (`RankOne.lt_of_nu_iterate_eq`, Corollary `cor:rankone`).

### 2.2 `ν₀ ≥ 1` at the start (`one_le_nu`)

Statement.  If `M` has rank `k ≥ 1`, then `ν(M^u) ≥ 1` for every weight `u`.

Proof.  A minimum base of `u` has `k ≥ 1` elements; one of them is a rainbow independent set of
`M^u`.

### 2.3 The invariant (`le_nu_schedule`)

Statement.  Let `L` be valid and `ν₀(p) ≥ 1`.  For `j < k`, after stages `1, …, j` the state
satisfies `ν₀ ≥ j + 1`.

Proof.  Induction on `j`: stage `j + 1 < k` starts with `ν₀ ≥ j + 1`, and validity gives
`ν₀ ≥ j + 2` after `L (j + 1)` updates.

### 2.4 The output is the optimum (`psi_schedule`)

Statement.  Let `M` have rank `k` and a rainbow base, and `L` valid.  After the schedule from
`p = 0`, that is `p = schedule L M blk w (k - 1) 0`, `Ψ(p) = Opt(w)`.

Proof.  Step 1.  `ν₀ ≤ k` always (`nu_le`), and 2.2 and 2.3 with `j = k - 1` give `ν₀ ≥ k` (for
`k = 0` there is nothing to show).  Step 2.  Lemma `lem:duality` (`Pos.psi_eq_opt`) turns
`ν₀ = k` into `Ψ(p) = Opt(w)`.

### 2.5 The number of updates (`rounds_le_potential`, `rounds_le`, `sum_range_id_le`)

Statement.  `rounds k m ≤ (⌊m²/4⌋ + 1) k(k-1)/2`, and `rounds k m ≤ 2 k² m` for `k ≤ m`.  With
`L r = r`, `Σ_{r<k} r ≤ k²`.

Proof.  Step 1.  Each term is at most `r(⌊m²/4⌋ + 1)`, and `Σ_{r<k} r = k(k-1)/2`.  Step 2.  For
`k = j + 1 ≥ 1`, the term `r = 0` is `0` and each term `r = 1, …, j` is at most
`1 + k (2m - k - 1) ≤ 1 + 2(j+1)m`, so `rounds ≤ j(1 + 2(j+1)m) ≤ 2(j+1)²m`, as
`j ≤ 2(j+1)m` for `m ≥ 1`.  Step 3.  `k(k-1)/2 ≤ k(k-1) ≤ k²`.

### 2.6 The weighted number of updates (`sum_stageLength_mul_le`, `sum_range_mul_le`)

The observer of stage `r` has `r + 1` rounds of augmentation, so the size of Theorem C weighs
stage `r` by `r + 2` (notes/P7-theoremC.md, Theorem 13).

Statement.  For `k ≤ m`, `40 Σ_{r<k} stageLength k m r · (r + 2) ≤ 49 k³ m`.  With `L r = r`,
`2 Σ_{r<k} r (r + 2) ≤ k³`.

Proof.  Step 1.  For `k ≤ 1` the sum has only the term `r = 0`, which is `0`.  Step 2.  For
`k = j + 2`, put `2m = a + j + 3` (`m ≥ k`).  Stage `0` is empty, stage `1` has
`stageLength ≤ 1 + (1 - 1) k m = 1`, and each stage `r = 2, …, k - 1` has
`stageLength ≤ 1 + k (2m - k - 1) = 1 + (j + 2) a =: A`, so the sum is at most
`3 + A Σ_{r<j} (r + 4)`, and `2 Σ_{r<j} (r + 4) = j² + 7j`.  Step 3.  In `ℤ`,
`49 (j+2)³ (a + j + 3) - 40 A (j² + 7j) - 240 = (j+2) a (3j - 14)² + 49j⁴ + 441j³ + 1430j² +
1876j + 936 ≥ 0`, so `80 · (sum) ≤ 40 A (j² + 7j) + 240 ≤ 49 (j+2)³ · 2m`.  Step 4, `L r = r`:
induction on `k`, with `2k(k + 2) ≤ (k + 1)³ - k³` since `k ≤ k² + 1`.

## 3. Correspondence

| Paper | Lean | Status |
|---|---|---|
| `thm:C`, Step 1, the schedule | `ValidLength`, `stageLength`, `schedule`, `one_le_nu` | proved |
| `thm:C`, Step 2, the invariant | `validLength_stageLength`, `le_nu_schedule` | proved |
| `thm:C`, Step 3, the output (mathematical part) | `psi_schedule` | proved |
| `thm:C`, Step 4, the number of updates | `rounds`, `rounds_le_potential`, `rounds_le` | proved |
| `cor:rankone` in the schedule (`ℓ_r = r`) | `validLength_rankOne`, `sum_range_id_le` | proved |
| `thm:C`, Step 4, the stages weighted by the rounds of their observers | `sum_stageLength_mul_le`, `sum_range_mul_le` | proved |

The circuit that realizes the schedule, and its size, belong to Theorem C proper
(`notes/P7-theoremC.md`).

## 4. Module size

`Schedule.lean`: 208 lines.
