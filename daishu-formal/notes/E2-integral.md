# E2: the threshold integral as an integral, and the Lipschitz bound

Module: `SignedTropical/Integral.lean`, namespace `SignedTropical.Integral`.

Sources: `greedy_intersection.tex`, Definition `def:ti` and the remark after it;
`signed_assignment.tex`, Proposition `prop:two-readings` (`eq:gap-sum`, `eq:lovasz`), Lemma
`lem:lipschitz`, and the Lipschitz statement of Corollary `cor:integer-observable`.

## Conventions

* `E = Fin m`. A set function is `F : Finset (Fin m) → ℝ`, a vector is `D : Fin m → ℝ`, and
  `D ≥ 0` is the hypothesis `∀ e, 0 ≤ D e`.
* As in Phase 1 (`GapSum.lean`): `0 = s_0 ≤ s_1 ≤ ⋯ ≤ s_m` are the entries of `D` sorted with a
  zero prepended (`sortedVal D k`), `Δ_k = s_{k+1} - s_k`, `G_k = {e : D_e ≤ s_k}`
  (`threshSet D k`), and the threshold integral is the gap sum
  `C_F(D) = ∑_{k<m} Δ_k F(G_k)` (`gapSum F D`).
* New here: the sublevel set `G_t(D) = {e : D_e ≤ t}` for real `t` (`sublevel D t`, with the
  simp lemma `mem_sublevel : e ∈ sublevel D t ↔ D e ≤ t`).
* `‖D - D'‖₁ = ∑_e |D_e - D'_e|`, written `∑ e, |D e - D' e|`.
* Integrals are against Lebesgue measure on `ℝ`. "Integrable on `[a, b]`" is Mathlib's
  `IntervalIntegrable f volume a b`, and `∫_a^b` is the interval integral `∫ t in a..b`, which
  for `a ≤ b` is the integral over `(a, b]`. "Integrable on `(0, ∞)`" is
  `IntegrableOn f (Set.Ioi 0)` (Lebesgue integrability), and `∫_0^∞` is `∫ t in Set.Ioi 0`.
  Single points are null sets, so these are the integrals the paper writes.

## 1. Results and proofs

### 1.1 The integrand is a step function

**Lemma E2.1.** Let `D ≥ 0`.

1. `G_k = G_{s_k}(D)` for every `k` (`threshSet_eq_sublevel`, true by definition).
2. If `k < m` and `s_k ≤ t < s_{k+1}`, then `G_t(D) = G_k` (`sublevel_eq_threshSet`).
3. `D_e ≤ s_m` for every `e` (`le_sortedVal_last`). Hence `G_t(D) = E` for every `t ≥ s_m`
   (`sublevel_eq_univ`).
4. `s_m = max_e D_e`, read as `0` when `m = 0` (`sortedVal_last_eq_iSup`). In Lean the right
   side is `⨆ e, D e`, and Mathlib's supremum of an empty family of reals is `0`.

*Proof.*
*Step 1, item 2.* Every entry satisfies `D_e ≤ s_k` or `D_e ≥ s_{k+1}` (Phase 1,
`le_or_succ_le`). In the first case `e ∈ G_k`, and `e ∈ G_t(D)` because `s_k ≤ t`. In the
second case `e ∉ G_t(D)` because `D_e ≥ s_{k+1} > t`, and `e ∉ G_k` because `D_e ≤ s_k` would
give `s_{k+1} ≤ D_e ≤ s_k ≤ t < s_{k+1}`.
*Step 2, item 3.* `D_e = s_j` for some `1 ≤ j ≤ m` (`exists_sortedVal_eq`), and `s_j ≤ s_m`
(`sortedVal_mono`). For `t ≥ s_m` every `e` therefore lies in `G_t(D)`.
*Step 3, item 4.* If `m = 0`, both sides are `0`. If `m > 0`, then `s_m = D_{e₀}` for some `e₀`
(`exists_eq_sortedVal`), and `D_e ≤ s_m` for every `e` by item 3, so `s_m` is the largest
entry. ∎

**Lemma E2.2 (one gap).**

1. If `a ≤ b` and `f(t) = c` for `a < t < b`, then `f` is integrable on `[a, b]` and
   `∫_a^b f = (b - a) c` (`intervalIntegral_of_eqOn_Ioo`).
2. For `D ≥ 0`, `F : 2^E → ℝ` and `k < m`, the function `t ↦ F(G_t(D))` is integrable on
   `[s_k, s_{k+1}]` and `∫_{s_k}^{s_{k+1}} F(G_t(D)) dt = Δ_k F(G_k)` (`intervalIntegral_gap`).

*Proof.*
*Step 1, item 1.* `f` agrees with the constant `c` on `(a, b)`, hence almost everywhere on
`(a, b]`. Mathlib transfers integrability (`IntervalIntegrable.congr_uIoo`) and the integral
(`intervalIntegral.integral_congr_Ioo_of_le`) from the constant, whose integral is `(b - a) c`.
*Step 2, item 2.* `s_k ≤ s_{k+1}` (`sortedVal_mono`), and on `(s_k, s_{k+1})` the integrand is
the constant `F(G_k)` by Lemma E2.1(2); apply item 1. ∎

### 1.2 Definition `def:ti`

**Theorem E2.3 (Definition `def:ti`).** For `D ≥ 0` and every `F : 2^E → ℝ`, the function
`t ↦ F(G_t(D))` is integrable on `[0, s_m]` and
`C_F(D) = ∑_{k<m} Δ_k F(G_k) = ∫_0^{s_m} F(G_t(D)) dt`,
where `s_m = max_e D_e` by Lemma E2.1(4) (`gapSum_eq_intervalIntegral`).

*Proof.*
*Step 1, integrability.* The `m` intervals `[s_k, s_{k+1}]` are adjacent and run from `s_0 = 0`
to `s_m`. Integrability on each of them (Lemma E2.2) gives integrability on `[0, s_m]`
(`IntervalIntegrable.trans_iterate`).
*Step 2, splitting.* `∫_{s_0}^{s_m} = ∑_{k<m} ∫_{s_k}^{s_{k+1}}`
(`intervalIntegral.sum_integral_adjacent_intervals`), and `s_0 = 0`.
*Step 3.* The `k`-th term is `Δ_k F(G_k)` by Lemma E2.2, and these terms sum to `C_F(D)`. ∎

### 1.3 Proposition `prop:two-readings`

**Theorem E2.4 (`eq:gap-sum`, and the remark after `def:ti`).** For `D ≥ 0` and
`F : 2^E → ℝ` with `F(E) = 0`, the function `t ↦ F(G_t(D))` is Lebesgue integrable on `(0, ∞)`
and `C_F(D) = ∫_0^∞ F(G_t(D)) dt` (`gapSum_eq_integral_Ioi`).

*Proof.*
*Step 1.* `s_m ≥ 0`. If `t > 0` and `t ∉ (0, s_m]`, then `t > s_m`, so `G_t(D) = E`
(Lemma E2.1(3)) and `F(G_t(D)) = F(E) = 0`.
*Step 2, integrability.* The integrand is integrable on `(0, s_m]` (Theorem E2.3) and vanishes
on `(0, ∞) \ (0, s_m]` (Step 1), so it is integrable on `(0, ∞)`
(`IntegrableOn.of_forall_sdiff_eq_zero`).
*Step 3, value.* For the same reason the integral over `(0, ∞)` equals the integral over
`(0, s_m]` (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`), which is
`∫_0^{s_m} F(G_t(D)) dt = C_F(D)` by Theorem E2.3. ∎

**Theorem E2.5 (`eq:lovasz`).** Let `D ≥ 0`, let `F : 2^E → ℝ` satisfy `F(E) = 0`, and let
`g : 2^E → ℝ` satisfy `g(S) = F(E \ S)` for every `S`. Then `t ↦ g({e : D_e ≥ t})` is Lebesgue
integrable on `(0, ∞)` and `C_F(D) = ∫_0^∞ g({e : D_e ≥ t}) dt` (`gapSum_eq_integral_lovasz`).

Started from `g`: if `g : 2^E → ℝ` satisfies `g(∅) = 0`, then `t ↦ g({e : D_e ≥ t})` is
Lebesgue integrable on `(0, ∞)` and `C_F(D) = ∫_0^∞ g({e : D_e ≥ t}) dt` for
`F(S) = g(E \ S)` (`gapSum_compl_eq_integral`).

*Proof.*
*Step 1.* If `t` is not an entry of `D`, then `E \ {e : D_e ≥ t} = {e : D_e < t} = G_t(D)`, so
`g({e : D_e ≥ t}) = F(G_t(D))`.
*Step 2.* The entries of `D` form a finite set, which is Lebesgue null
(`Set.Countable.ae_notMem`), so the two integrands agree almost everywhere on `(0, ∞)`.
Theorem E2.4 then gives integrability (`IntegrableOn.congr_fun_ae`) and the value
(`setIntegral_congr_ae`).
*Step 3, the form started from `g`.* `F(S) = g(E \ S)` satisfies `F(E) = g(∅) = 0` and
`F(E \ S) = g(E \ (E \ S)) = g(S)`; apply the first part. ∎

### 1.4 The Lipschitz bound

**Lemma E2.6 (the value `F(E)` does not enter `C_F`).** For `D ≥ 0` and `F : 2^E → ℝ`, let
`F'(E) = 0` and `F'(S) = F(S)` for `S ≠ E`. Then `C_{F'}(D) = C_F(D)` (`gapSum_ite_univ`).

*Proof.*
*Step 1.* Compare the two sums term by term, for `k < m`. If `G_k ≠ E`, the terms are equal.
*Step 2.* If `G_k = E`, then `s_{k+1} = D_e` for some `e` (`exists_eq_sortedVal`, since
`1 ≤ k + 1 ≤ m`), and `e ∈ G_k` gives `D_e ≤ s_k`. With `s_k ≤ s_{k+1}` this forces
`Δ_k = 0`, and both terms vanish. ∎

**Theorem E2.7 (Lipschitz bound for bounded nonnegative observables).** Let `c ∈ ℝ` and
`F : 2^E → ℝ` with `0 ≤ F(S) ≤ c` for every `S`. Then for all `D, D' ≥ 0`,
`|C_F(D) - C_F(D')| ≤ c ‖D - D'‖₁` (`abs_gapSum_sub_le`; with the additional hypothesis
`F(E) = 0` this is `abs_gapSum_sub_le_of_univ`).

*Proof.*
*Step 1, reduction to `F(E) = 0`.* By Lemma E2.6 both gap sums are unchanged when `F` is
replaced by `F'`, and `F'` satisfies `0 ≤ F' ≤ c` (because `c ≥ F(∅) ≥ 0`) and `F'(E) = 0`.
So assume `F(E) = 0`.
*Step 2, integral form.* Put `φ(t) = F(G_t(D))` and `φ'(t) = F(G_t(D'))`. By Theorem E2.4
both are integrable on `(0, ∞)`, and `C_F(D) - C_F(D') = ∫_0^∞ (φ - φ')`.
*Step 3, pointwise bound.* Let `I_e = [min(D_e, D'_e), max(D_e, D'_e))`. For every real `t`,
`|φ(t) - φ'(t)| ≤ ∑_e c·1_{I_e}(t)`. If `G_t(D) = G_t(D')`, the left side is `0` and the right
side is nonnegative. Otherwise some `e` satisfies exactly one of `D_e ≤ t` and `D'_e ≤ t`; then
`min(D_e, D'_e) ≤ t < max(D_e, D'_e)`, so `t ∈ I_e` and the right side is at least `c`, while
the left side is at most `c` because `φ(t)` and `φ'(t)` lie in `[0, c]`.
*Step 4, integration.* Each `c·1_{I_e}` is integrable on `ℝ` with integral
`c (max(D_e, D'_e) - min(D_e, D'_e)) = c |D_e - D'_e|` (`integral_indicator_const`,
`Real.volume_real_Ico_of_le`). Hence
`|∫_0^∞ (φ - φ')| ≤ ∫_0^∞ |φ - φ'| ≤ ∫_0^∞ ∑_e c·1_{I_e} ≤ ∫_ℝ ∑_e c·1_{I_e} = c ‖D - D'‖₁`,
where the third inequality uses that the integrand is nonnegative
(`setIntegral_le_integral`). ∎

**Lemma E2.8 (Lemma `lem:lipschitz`).** For every Boolean observable `F : 2^E → {0, 1}` and all
`D, D' ≥ 0`, `|C_F(D) - C_F(D')| ≤ ‖D - D'‖₁`. No hypothesis on `F(E)` is needed
(`lipschitz`). In Lean `F : Finset (Fin m) → Bool` and the observable is
`S ↦ if F S then 1 else 0`, as in Phase 1's `thm_compiler`.

*Proof.* *Step 1.* The observable takes values in `[0, 1]`; apply Theorem E2.7 with
`c = 1`. ∎

**Corollary E2.9 (Corollary `cor:integer-observable`, the Lipschitz bound).** For every
`f : 2^E → ℕ` and all `D, D' ≥ 0`, `|C_f(D) - C_f(D')| ≤ (max_S f(S)) ‖D - D'‖₁`, where
`max_S f(S)` is `univ.sup f`. No hypothesis on `f(E)` is needed
(`integer_observable_lipschitz`).

*Proof.* *Step 1.* `0 ≤ f(S) ≤ max_S f(S)` for every `S` (`Finset.le_sup`); apply
Theorem E2.7 with `c = max_S f(S)`. ∎

## 2. Correspondence table

| Paper label | Lean names | Module | Status |
|--|--|--|--|
| `def:ti` (`greedy_intersection.tex`) | `gapSum_eq_intervalIntegral`, `sortedVal_last_eq_iSup` | `SignedTropical/Integral.lean` | proved |
| remark after `def:ti` (`G_t(D) = E` for `t ≥ s_m`; upper limit `∞` when `F(E) = 0`) | `sublevel_eq_univ`, `gapSum_eq_integral_Ioi` | `SignedTropical/Integral.lean` | proved |
| `prop:two-readings`, `eq:gap-sum` | `gapSum_eq_integral_Ioi` | `SignedTropical/Integral.lean` | proved, for every real `F` with `F(E) = 0` |
| `prop:two-readings`, `eq:lovasz` | `gapSum_eq_integral_lovasz`, `gapSum_compl_eq_integral` | `SignedTropical/Integral.lean` | proved, for every real `F` with `F(E) = 0` |
| proof of `prop:two-readings` (`G_t(D)` constant on `[s_k, s_{k+1})`) | `sublevel_eq_threshSet`, `intervalIntegral_gap` | `SignedTropical/Integral.lean` | proved |
| `lem:lipschitz` | `lipschitz`; general form `abs_gapSum_sub_le`, `abs_gapSum_sub_le_of_univ`, `gapSum_ite_univ` | `SignedTropical/Integral.lean` | proved, without `F(E) = 0` |
| `cor:integer-observable`, Lipschitz bound | `integer_observable_lipschitz` | `SignedTropical/Integral.lean` | proved, without `f(E) = 0` |

## 3. Differences from the paper

1. **`C_F` is the gap sum.** Phase 1 defines `C_F(D)` as the gap sum (`BLUEPRINT.md`, D4),
   which is defined for every `F : 2^E → ℝ`. This is also how `greedy_intersection.tex`
   defines `C_F` in Definition `def:ti`, so Theorem E2.3 is `def:ti` as written. In
   `signed_assignment.tex`, `C_F(D)` is the integral `∫_0^∞ F(G_t(D)) dt` of Definition
   `def:filtration`, for Boolean `F` with `F(E) = 0`; Theorems E2.4 and E2.5 show that the two
   definitions agree wherever the companion's is defined, so the Lean statements about the gap
   sum are statements about the companion's `C_F`. No change to either paper is needed.
2. **Proposition `prop:two-readings` for real-valued `F`.** The companion states it under
   Definition `def:filtration`, that is for Boolean `F`, but the proof of Corollary
   `cor:integer-observable` applies it to the integer observable `f`. Its proof never uses that
   `F` is Boolean, and the Lean statements (Theorems E2.4 and E2.5) take any `F : 2^E → ℝ` with
   `F(E) = 0`. Proposed wording for the opening of Proposition `prop:two-readings`:
   "Let $F\colon2^{E}\to\mathbb R$ satisfy $F(E)=0$, and write
   $\mathcal C_F(D)=\int_0^{\infty}F(G_t(D))\,dt$ as in \eqref{eq:threshold-integral}. For every
   $D\in\mathbb R_{\ge0}^{E}$, ..."
3. **Lemma `lem:lipschitz` and Corollary `cor:integer-observable` without `F(E) = 0`.** For the
   gap sum the bound holds for every Boolean `F` and every `f : 2^E → ℕ`, because a gap with
   `G_k = E` has width `0` (Lemma E2.6). In the companion, `F(E) = 0` is what makes
   `∫_0^∞ F(G_t(D)) dt` finite, so its statements are correct as they stand. A sentence the
   companion could add after Lemma `lem:lipschitz`: "Read through \eqref{eq:gap-sum},
   $\mathcal C_F$ is defined for every $F$, and \eqref{eq:lipschitz} holds without the
   hypothesis $F(E)=0$, since a gap with $G_k=E$ has $\Delta_k=0$."
4. **The proof of the Lipschitz bound in Corollary `cor:integer-observable`.** The companion
   writes "The Lipschitz bound is $\max_Sf(S)$ times \eqref{eq:lipschitz}", but Lemma
   `lem:lipschitz` is stated for Boolean observables and does not apply to `f` itself. The
   Lean proof reruns the argument of `lem:lipschitz` with integrands that differ by at most
   `max_S f(S)` (Theorem E2.7). Proposed wording: "The Lipschitz bound follows from
   \eqref{eq:lipschitz} applied to the Boolean observables $\mathbf 1[f\ge j]$,
   $1\le j\le\max_Sf(S)$, which vanish at $E$ and sum to $f$."
5. **`s_m = max_e D_e` when `m = 0`.** For `E = ∅` the expression `max_e D_e` is undefined; the
   prepended zero gives `s_0 = 0`, and Lean's `⨆ e, D e` over an empty index is `0`
   (Lemma E2.1(4)). No change is needed.
6. **Integrability is part of each statement.** Mathlib assigns the value `0` to the integral
   of a non-integrable function, so each of Theorems E2.3, E2.4 and E2.5 states the
   integrability of its integrand together with the identity.
7. **`eq:lovasz` with `g` as a second function.** "Writing $g(S)=F(E\setminus S)$" becomes the
   hypothesis `∀ S, g S = F (univ \ S)`, so that the integrand reads `g {e | t ≤ D e}` as in
   the paper.

## 4. Module line counts

| Module | Lines |
|--|--|
| `SignedTropical/Integral.lean` | 231 |

## 5. Not done

* The phrase "which is the Lovász extension of the set function $g$ evaluated at $D$" in
  Proposition `prop:two-readings`: Mathlib has no Lovász extension, and for `D ≥ 0` the
  integral `∫_0^∞ g({e : D_e ≥ t}) dt` is its definition, so Theorem E2.5 is the whole content.
* The sentence "Lemma `lem:lipschitz` settles continuity without any case analysis at ties" is a
  remark. Continuity of `D ↦ C_F(D)` on `ℝ^E_{≥0}` follows at once from Theorem E2.7 and is not
  stated separately.
* `PHASE1.md` (Section 6) and `BLUEPRINT.md` (D4 and the row "1 (open)") still list the integral
  form and `lem:lipschitz` as not formalized. These files belong to the coordinator and were not
  edited.

Every item of the assignment is proved.

## 6. Verification

`lake build SignedTropical.Integral` reports no errors and no warnings. `#print axioms` for
every theorem of the module lists only `propext`, `Classical.choice` and `Quot.sound`.
