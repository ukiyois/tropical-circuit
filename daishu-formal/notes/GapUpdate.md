# The update as a gap sum over the event levels

Module: `SignedTropical/Rainbow/GapUpdate.lean` (namespace `SignedTropical.Rainbow.GapUpdate`).
Paper: `greedy_intersection.tex`, Lemma `lem:oneupdate`, Step 3.

## 1. Notation

`Λ = lev M v` are the `2m` event levels and `Q = Qv M v` the `m + 2m²` query values of
`Rainbow/Events.lean` (notes/P6d-events.md); `s_0 = 0 ≤ s_1 ≤ ⋯ ≤ s_{2m}` are the sorted
levels and `Δ_i = s_{i+1} - s_i`.  The bits at `t` are `[Q_j ≤ t]`.

## 2. Results

### 2.1 The bits read from the sublevel sets (`bits_sublevel`)

Statement.  For `t ≥ 0`, `[Q_j ≤ t] = [Q_j = 0 ∨ ∃ i, Λ_i ≤ t ∧ Λ_i = Q_j]`.

Proof.  Every `Q_j` is `0` or a level (`Events.Qv_inLev`).

### 2.2 Lemma `lem:oneupdate`, Step 3 (`update_eq_levSum`)

Statement.  Let `M` have rank `k` and a rainbow base, `r ≤ ν(M^v)` and `r < k`, and let a Boolean
function `F_b` of the bits satisfy `F_b([Q ≤ t]) = [ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]` for every
`t ≥ 0`.  Then `a_b = Σ_{i < 2m} Δ_i F_b([Q ≤ s_i])`.

Proof.  Step 1, put `Φ(S) = F_b([Q_j = 0 ∨ ∃ i ∈ S, Λ_i = Q_j])` on the subsets `S` of the level
indices; by 2.1, `Φ(G_t(Λ)) = [ν(N(t)) ≤ r]·[b ∈ Av(N(t))]` for `t ≥ 0`.  Step 2, at
`T = Σ_i Λ_i + Σ_{e,f} |v_f - v_e|`, every level is at most `T`, so `G_T(Λ) = E`, and every
`v_f - v_e ≤ T`, so `N(T) = M` (`POSL.N_eq_self`) and `ν(M) = k > r`; hence `Φ(E) = 0`.  Step 3,
by `eq:update-integral` (`Validity.update_eq_integral`) and the integral reading of the gap sum
(`Integral.gapSum_eq_integral_Ioi`), `a_b = ∫_{t>0} Φ(G_t(Λ)) dt = C_Φ(Λ)`.  Step 4, the gap sum
`C_Φ(Λ)` evaluates `Φ` at `G_{s_i}(Λ)`, where 2.1 gives `F_b([Q ≤ s_i])`.

## 3. Correspondence

| Paper | Lean | Status |
|---|---|---|
| `lem:oneupdate`, Step 3 | `bits_sublevel`, `update_eq_levSum` | proved |

## 4. Module size

`GapUpdate.lean`: 91 lines.
