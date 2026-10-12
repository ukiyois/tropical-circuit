# P3: the update and its validity (Definition `def:update`, `eq:update-integral`, Theorem `thm:validity`)

Natural-language companion of `SignedTropical/Rainbow/Update.lean` and
`SignedTropical/Rainbow/Validity.lean`, namespace `SignedTropical.Rainbow.Validity`.  Source:
`daishu/paper/greedy_intersection.tex`, Section 4.4 (Definition `def:update`, the paragraph after
it, equation `eq:update-integral`, Theorem `thm:validity` and its proof).

Build status: `lake build SignedTropical.Rainbow.Validity` (which builds `Update` first) succeeds
with no error and no warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
`extern`, `unsafe` or `opaque`.  All 47 theorems of the two modules depend only on `propext`,
`Classical.choice` and `Quot.sound` (checked with `#print axioms`).  Imports:
`Rainbow/MinBases`, `Integral` (E2), `Rainbow/Exchange` (P2), `Rainbow/PossiblyOptimal`
(coordinator); all used unchanged.

Notation.  `E = Fin m`, blocks `blk : E → [k]`, `M` a matroid with ground set `E`
(`hE : M.E = Set.univ`), `v = w - p_blk` (`shift blk w p`), `M^v = minBases M v`,
`ν₀ = ν(M^v)`, `S₀ = Av(M^v)`, `Ψ(p) = Σ_b p_b + β_M(v)` (`Psi`).  `N : ℝ → Matroid (Fin m)` is a
family of matroids; "admissible" is `IsAdmissible M blk v N` of `Rainbow/Defs.lean`, Definition
`def:admissible` with (F1) to (F5).  The stage `r` is a parameter of every definition.  A base
`B` "meets exactly `r` blocks" when `|blk(B)| = r` (`#(blocksMet blk B) = r`).  `[0, ∞]` is
`ℝ≥0∞`, in which `t - ∞ = 0` and the infimum of the empty set is `∞`.  Integrals are against
Lebesgue measure: `∫_0^∞` is `∫ t in Set.Ioi 0`, `∫_0^T` is the interval integral
`∫ t in (0)..T`, and the integrand of `eq:update-integral` is written
`g_b(t) = 1[ν(N(t)) ≤ r] 1[b ∈ Av(N(t))]`, in Lean
`(if nu (N t) blk ≤ r then 1 else 0) * (if b ∈ Av (N t) blk then 1 else 0)`.


## 1. Results

### 1.1 Definition `def:update`

* `BaseMisses N blk r b`: some base of the matroid `N` meeting exactly `r` blocks misses `b`.
* `tau N blk r = τ = inf {t ≥ 0 : ν(N(t)) ≥ r + 1}`, an infimum of reals.
* `lam N blk r b = λ_b = inf {t ≥ 0 : BaseMisses (N t) blk r b}`, an infimum in `[0, ∞]`; it is
  `∞` exactly when the set is empty.
* `update N blk r b = a_b = (τ - λ_b)₊`, computed in `[0, ∞]` and read as a real number; so
  `a_b = 0` when `λ_b = ∞`.  The update is `p ↦ p + a`.

None of the definitions assumes admissibility.  Section 1.3 shows that the infima are minima for
an admissible family, and Section 1.5 that `a = 0` when `ν₀ > r`, as the paper sets.

### 1.2 The levels of (F5)

**Lemma 1.**  `isLeast_sInf`.  Let `N` satisfy (F5) and let `P` be a property of matroids.  If
`P(N(t))` holds for some `t ≥ 0`, then the set `{t ≥ 0 : P(N(t))}` has a least element, its
infimum.

*Proof.*  Step 1, write `S` for the set and `l = inf S ≥ 0`.  Step 2, some `t ∈ S` has no level
in `(l, t]`: if some level exceeds `l`, let `x₀` be the least one; since `l < x₀` some `t ∈ S`
has `t < x₀`; otherwise take any `t ∈ S`.  Step 3, `l ≤ t`, so (F5) gives `N(l) = N(t)`, and
`P(N(l))` holds: `l ∈ S`.

**Lemma 2.**  Let `N` be admissible.
1. `nu_mono_of_le`, `nu_zero_le`: `ν(N(t)) ≤ ν(N(t'))` for `0 ≤ t ≤ t'`, and `ν₀ ≤ ν(N(t))`
   for `t ≥ 0` (by (F2), P0a's `nu_mono`, and (F1)).
2. `rank_eq_of_isAdmissible`: if `M` has rank `k`, then `N(t)` has rank `k` for `t ≥ 0`: a base
   of `N(0) = M^v`, which has `k` elements, is a base of `N(t)` by (F2).
3. `exists_succ_le_nu`: if `M` has rank `k` and `r < k`, then `ν(N(T)) ≥ r + 1` for some
   `T ≥ 0`: by (F4) some `N(T)` has a rainbow base, which has `rank N(T) = k ≥ r + 1` elements.

### 1.3 The minima exist

**Proposition 3 (the minima of Definition `def:update`).**  Let `N` be admissible.
1. `isLeast_tau`: if `M` has rank `k` and `r < k`, then `τ` is the least element of
   `{t ≥ 0 : ν(N(t)) ≥ r + 1}`.  `tau_nonneg`: `τ ≥ 0`.
2. `exists_isLeast_lam`: if `BaseMisses (N t) blk r b` for some `t ≥ 0`, the set of such `t`
   has a least element `l` and `λ_b = l`.  `lam_eq_top_iff`: `λ_b = ∞` if and only if there is
   no such `t`.
3. `BaseMisses.mono`, `lam_le_iff`: for `t ≥ 0`, `λ_b ≤ t` if and only if some base of `N(t)`
   meeting exactly `r` blocks misses `b`; that is, the set of these `t` is `[λ_b, ∞)`.

*Proof.*  Step 1, item 1 is Lemma 1 for `P(N') = (ν(N') ≥ r + 1)`, the set being nonempty by
Lemma 2(3).  Step 2, item 2 is Lemma 1 for `P = BaseMisses · blk r b`; then `λ_b ≤ l` as `l`
belongs to the set, and `l ≤ t` for every `t` of the set gives `λ_b ≥ l`.  The infimum in
`[0, ∞]` is `∞` exactly when every term of the infimum is `∞`, and no `ofReal t` is `∞`.
Step 3, item 3: `λ_b ≤ t` when `t` belongs to the set, by definition.  Conversely, if `λ_b ≤ t`
then `λ_b < ∞`, the set is nonempty, `λ_b = l` is its least element by item 2, `l ≤ t`, and by
(F2) the base of `N(l)` meeting `r` blocks and missing `b` is a base of `N(t)`.

### 1.4 The paragraph after the definition

**Proposition 4.**  Let `N` be admissible and `r ≤ ν₀`.
1. `nu_eq_of_lt_tau`: `ν(N(t)) = r` for `0 ≤ t < τ`.
2. `succ_le_nu_of_tau_le`: if `M` has rank `k` and `r < k`, then `ν(N(t)) ≥ r + 1` for
   `t ≥ τ`.
3. For every matroid `N'` on `E`: `exists_isRainbowIndep_subset`: a base `B` of `N'` contains a
   rainbow independent set `I` with `blk(I) = blk(B)`, so `|I| = |blk(B)|`;
   `exists_isBase_of_isRainbowIndep`: a rainbow independent set `I` with `|I| = ν(N')` lies in a
   base `B` of `N'` with `blk(B) = blk(I)`; `exists_isBase_card_blocksMet`: some base of `N'`
   meets exactly `ν(N')` blocks.
4. `mem_Av_iff_baseMisses`: if `ν(N') = r`, then `b ∈ Av(N')` if and only if some base of `N'`
   meeting exactly `r` blocks misses `b`.
5. `mem_Av_iff_lam_le`: for `0 ≤ t < τ`, `b ∈ Av(N(t))` if and only if `λ_b ≤ t`.  So the set
   of `t ∈ [0, τ)` at which `b` is avoidable is `[λ_b, τ)`.
6. `lam_eq_zero_iff`: if `ν₀ = r`, then `λ_b = 0` if and only if `b ∈ S₀`.

*Proof.*  Step 1, item 1: if `ν(N(t)) ≥ r + 1`, then `t` belongs to the set defining `τ`, so
`τ ≤ t`; hence `ν(N(t)) ≤ r`, while `ν(N(t)) ≥ ν₀ ≥ r` by Lemma 2(1).  Step 2, item 2:
`ν(N(τ)) ≥ r + 1` by Proposition 3(1), and `ν` grows by Lemma 2(1).  Step 3, item 3, first
part: choosing one element of `B` in each block that `B` meets gives `I ⊆ B`, independent and
rainbow, with `blk(I) = blk(B)` (Mathlib's `exists_subset_injOn_image_eq_of_surjOn`).  Second
part: extend `I` to a base `B`; then `blk(I) ⊆ blk(B)`, and
`|blk(B)| ≤ ν(N') = |I| = |blk(I)|`, since an independent set meets at most `ν(N')` blocks
(P0a's `card_blocksMet_le_nu`); so `blk(B) = blk(I)`.  Third part: apply the second part to a
rainbow independent set of size `ν(N')`.  Step 4, item 4: if a rainbow independent `I` with
`|I| = r` misses `b`, the base of item 3 meets the blocks `blk(I)`, `r` of them, and misses `b`;
if a base `B` meeting `r` blocks misses `b`, the set `I` of item 3 has `|I| = r = ν(N')` and
misses `b`.  Step 5, item 5: by item 1, `ν(N(t)) = r`, so item 4 and Proposition 3(3) apply.
Step 6, item 6: by (F1) `N(0) = M^v` with `ν(N(0)) = r`; item 4 and Proposition 3(3) at `t = 0`
give `b ∈ S₀` if and only if `λ_b ≤ 0`.

### 1.5 Values of the update

**Proposition 5.**  For every family `N`:
1. `update_nonneg`, `update_le_tau`: `0 ≤ a_b ≤ τ`.  `ofReal_update`: `a_b = τ - λ_b` in
   `[0, ∞]`.
2. `update_eq_max`: if `λ_b = l` is finite, `a_b = max(τ - l, 0)`.
   `update_eq_zero_of_lam_eq_top`: if `λ_b = ∞`, `a_b = 0`.

Let `N` be admissible.

3. `tau_eq_zero`, `update_eq_zero` (Definition `def:update`, the case `ν₀ > r`): if `ν₀ > r`,
   then `τ = 0` and `a = 0`.  Only (F1) is assumed.
4. `update_eq_tau`: if `ν₀ = r` and `b ∈ S₀`, then `a_b = τ`.
5. `update_le_of_forall_notMem`: if `r ≤ ν₀`, `δ ≤ τ`, and `b ∉ Av(N(t))` for every
   `t ∈ [0, δ)`, then `a_b ≤ τ - δ`.

*Proof.*  Step 1, items 1 and 2: `τ - λ_b ≤ τ` in `[0, ∞]`, `τ - ofReal l = ofReal (τ - l)` for
`l ≥ 0`, whose real value is `max(τ - l, 0)`, and `τ - ∞ = 0`.  Step 2, item 3: by (F1)
`ν(N(0)) = ν₀ ≥ r + 1`, so `0` belongs to the set defining `τ` and `τ = 0`; then
`a_b = (0 - λ_b)₊ = 0`.  Step 3, item 4: `λ_b = 0` by Proposition 4(6).  Step 4, item 5: if
`λ_b = ∞`, `a_b = 0 ≤ τ - δ`.  Otherwise `λ_b = l` is real; if `l < δ`, then `l < τ` and
Proposition 4(5) at `t = l` makes `b` avoidable at `l ∈ [0, δ)`, against the hypothesis.  So
`l ≥ δ` and `a_b = max(τ - l, 0) ≤ τ - δ`.

### 1.6 Equation `eq:update-integral`

**Theorem 6 (equation `eq:update-integral`).**  Let `M` have rank `k`, `r < k`, `r ≤ ν₀` and
`N` admissible.  For every block `b`:
1. `setOf_nu_le_mem_Av_eq`: `{t ≥ 0 : ν(N(t)) ≤ r, b ∈ Av(N(t))} = {t ∈ [0, τ) : λ_b ≤ t}`;
   `measurableSet_setOf_nu_le_mem_Av`: this set is Lebesgue measurable.
2. `volume_eq` (measure form): the Lebesgue measure of
   `{t ≥ 0 : ν(N(t)) ≤ r, b ∈ Av(N(t))}` is `a_b`.
3. `update_eq_integral`: `g_b` is integrable on `(0, ∞)` and `a_b = ∫_0^∞ g_b(t) dt`.
4. `update_eq_intervalIntegral`: for every `T ≥ τ`, `g_b` is integrable on `[0, T]` and
   `a_b = ∫_0^T g_b(t) dt`.

The hypothesis `r ≤ ν₀` covers both cases of Definition `def:update`: `ν₀ = r`, and `ν₀ > r`,
where `a = 0` and the set of item 1 is empty.

*Proof.*  Step 1, item 1: fix `t ≥ 0`.  If `t < τ`, then `ν(N(t)) = r ≤ r` and
`b ∈ Av(N(t))` if and only if `λ_b ≤ t` (Proposition 4(1), (5)).  If `t ≥ τ`, then
`ν(N(t)) ≥ r + 1` (Proposition 4(2)), and `t` lies in neither set.  The right-hand set is
`[0, ∞) ∩ (-∞, τ) ∩ {t : λ_b ≤ ofReal t}`, measurable since `ofReal` is measurable.  Step 2,
item 2: if `λ_b = ∞` the set is empty and `a_b = 0`.  Otherwise `λ_b = l ≥ 0` and the set is
`[l, τ)`, of measure `(τ - l)₊ = τ - λ_b = a_b` in `[0, ∞]` (Proposition 5(1)).  Step 3, item 3:
on `(0, ∞)`, `g_b` is the indicator of the set `A` of item 2 (`ite_zero_mul_ite_zero`).  `A`
has finite measure, so its indicator is integrable.  The integral over `(0, ∞)` equals the
integral over `[0, ∞)`, a point being null, which is the measure of `A ∩ [0, ∞) = A`, that is
`a_b` (item 2).  Step 4, item 4: integrability on `(0, T] ⊆ (0, ∞)` follows from item 3.  For
`t > T ≥ τ`, `ν(N(t)) ≥ r + 1` and `g_b(t) = 0`, so the integral over `(0, ∞)` equals the
integral over `(0, T]`, which is `∫_0^T` (Mathlib's
`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`, `intervalIntegral.integral_of_le`).

### 1.7 The path and the sandwich (Steps 1 to 4 of the proof of `thm:validity`)

Here `v` is any weight, `ν₀ = r`, `N` is admissible, and `B*` (Lean `B₀`) is a base of `M^v`
meeting exactly `r` blocks.

**Definition 7.**  `path N blk r s b = a(s)_b = (s - λ_b)₊`, computed in `[0, ∞]`;
`v(s) = v - a(s)_blk` (`shift blk v (path N blk r s)`).  `path_tau`: `a(τ) = a`, by definition.
`shift_shift`: `(w - p_blk) - q_blk = w - (p + q)_blk`.

**Lemma 8.**
1. `path_zero`: `a(0) = 0`.  `path_mem`: `a(s) ∈ [0, s]^k` for `s ≥ 0`.
2. `continuous_path`: `s ↦ a(s)_b` is continuous; it is `0` if `λ_b = ∞` and `max(s - l, 0)`
   if `λ_b = l`.
3. `eventually_path_eq` (Step 2, the right derivative): for `x ≥ 0` and all `y > x` close to
   `x`, `a(y)_b = a(x)_b + (y - x)` if `λ_b ≤ x`, and `a(y)_b = a(x)_b` otherwise.

*Proof.*  Step 1, item 1: `0 - λ_b = 0`, and `s - λ_b ≤ s` in `[0, ∞]`.  Step 2, item 2: as in
Proposition 5(2).  Step 3, item 3: if `λ_b ≤ x < y`, then `a(y)_b = y - λ_b` and
`a(x)_b = x - λ_b` as real numbers (Mathlib's `ENNReal.toReal_sub_of_le`).  If `λ_b > x`, then
`λ_b > y` for all `y` near `x`, by continuity of `ofReal`, and both values are `0`.

**Proposition 9 (Steps 3 and 4, the sandwich).**  `sandwich`.  Let `0 ≤ s < τ`,
`A = Av(N(s))` and `X = E_A`.  Then every base `B` of `N(s)` has `|B ∩ X| ≤ |B* ∩ X|`, and
`B*` meets every block of `A` at most once (`blk` is injective on `B* ∩ X`).

*Proof.*  Step 1, `ν(N(s)) = r` (Proposition 4(1)), so Lemma `lem:avoidable`(2) (P2's
`card_av_add_nu`) gives `|A| + r = k + r_{N(s)}(X)`; also `r ≤ k`.  Step 2, every base `B` of
`N(s)` has `|B ∩ X| ≤ r_{N(s)}(X)`, as `B ∩ X` is independent; in particular `B*`, a base of
`N(0) = M^v` (F1), hence of `N(s)` (F2).  Step 3, `B*` meets at least `|A| - (k - r)` blocks of
`A`: the blocks of `A` that `B*` meets are `A ∩ blk(B*)`, and `A \ blk(B*)` lies among the
`k - r` blocks that `B*` misses.  These blocks are all met by `B* ∩ X`, so
`|A| + r ≤ |blk(B* ∩ X)| + k ≤ |B* ∩ X| + k`.  Step 4, Steps 1 to 3 give, for every base `B` of
`N(s)`, `|B ∩ X| + k ≤ r_{N(s)}(X) + k = |A| + r ≤ |blk(B* ∩ X)| + k ≤ |B* ∩ X| + k`, and for
`B = B*` the chain is a chain of equalities.  So `|B ∩ X| ≤ |B* ∩ X|`, and
`|blk(B* ∩ X)| = |B* ∩ X|`, that is, `blk` is injective on `B* ∩ X`.

### 1.8 The old base stays minimum (Steps 1, 2 and 5)

**Theorem 10.**  `isMinBase_path`.  `B*` is a minimum base of `v(s)` for every `s ∈ [0, τ]`.

*Proof.*  Write `f_B(s) = v(s)(B)` for a set `B`; each `f_B` is continuous (Lemma 8(2)).  Let
`T` be the set of `s` at which `B*` is a minimum base of `v(s)`, that is, at which `B*` is a
base of `M` (it is, by Lemma `lem:minbases`(3)) and `f_{B*}(s) ≤ f_B(s)` for every base `B`.
The real induction of Mathlib (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`) gives
`[0, τ] ⊆ T` from Steps 1 to 3.
Step 1, `T` is closed: it is the intersection over the bases `B` of the closed sets
`{s : f_{B*}(s) ≤ f_B(s)}`.
Step 2, `0 ∈ T`: `v(0) = v` (Lemma 8(1)), and `B*` is a minimum base of `v` (Lemma
`lem:minbases`(3), `isBase_minBases_iff`).
Step 3, `T` extends to the right of each `x ∈ T` with `0 ≤ x < τ`.  Let
`X = E_{Av(N(x))}`.  By Lemma 8(3) and Proposition 4(5), for all `y > x` close to `x`,
`v(y) = v(x) - (y - x) 1_X`, so `f_B(y) = f_B(x) - (y - x)|B ∩ X|` for every `B`.  Fix a base
`B`.  If `f_{B*}(x) < f_B(x)`, then `f_{B*}(y) < f_B(y)` for `y` near `x` by continuity.
Otherwise `f_{B*}(x) = f_B(x)`, since `B*` is minimum at `x`, so `B` is a minimum base of
`v(x) = v - a(x)_blk`.  Lemma `lem:path` (`Pos.mem_pos_of_isMinBase_shift`, with
`a(x) ∈ [0, x]^k`) puts `B` in `P_x`, and (F3) makes `B` a base of `N(x)`; Proposition 9 gives
`|B ∩ X| ≤ |B* ∩ X|`, hence `f_{B*}(y) ≤ f_B(y)` for `y > x`.  There are finitely many bases,
so for all `y > x` close to `x` the inequality holds for every base, and `y ∈ T`.

### 1.9 Theorem `thm:validity`

**Theorem 11 (Theorem `thm:validity`).**  Let `M` have ground set `E`, `v = w - p_blk`,
`ν₀ = r`, `N` admissible and `a` its update.
1. `psi_update`: `Ψ(p + a) = Ψ(p) + (k - r) τ`.
2. `isMinBase_update`: every base of `M^v` meeting exactly `r` blocks is a minimum base of
   `v - a_blk`.
3. `nu_le_nu_update`: `ν₀` does not decrease: `ν(M^v) ≤ ν(M^{v - a_blk})`.  This item is stated
   for every `r ≤ ν₀`.

`validity` states items 1 to 3 together, with `v - a_blk = w - (p + a)_blk` in item 3.
`update_eq_zero_of_mem_of_mem`: a block that contains two elements of `B*` has `a_b = 0`.

*Proof.*  Step 1, item 2 is Theorem 10 at `s = τ`, as `a(τ) = a`.
Step 2, item 3: if `ν₀ > r`, then `a = 0` (Proposition 5(3)).  If `ν₀ = r`, take a rainbow
independent set `I` of `M^v` with `|I| = r` and a base `B*` of `M^v` containing it and meeting
the blocks of `I` (Proposition 4(3)).  By item 2, `B*` is a minimum base of `v - a_blk`, so a
base of `M^{v - a_blk}`, and `I ⊆ B*` is rainbow independent there: `ν(M^{v - a_blk}) ≥ r`.
Step 3, `update_eq_zero_of_mem_of_mem`: let `e₁ ≠ e₂` in `B*` lie in block `b`, and suppose
`a_b ≠ 0`.  Then `λ_b < τ`, so `λ_b = l` is real with `0 ≤ l < τ`, and `b ∈ Av(N(l))`
(Proposition 4(5)).  Both `e₁` and `e₂` lie in `B* ∩ E_{Av(N(l))}`, on which `blk` is injective
(Proposition 9): `e₁ = e₂`, a contradiction.
Step 4, item 1: take `B*` a base of `M^v` meeting `r` blocks (Proposition 4(3)); `r ≤ k`.
`β_M(v) = v(B*)`, and by item 2, `β_M(v - a_blk) = v(B*) - Σ_{e ∈ B*} a_{blk(e)}`, so
`Ψ(p + a) - Ψ(p) = Σ_b a_b - Σ_{e ∈ B*} a_{blk(e)}`.  Group the second sum by blocks
(`Finset.sum_comp`): a block `b` met by `B*` contributes `n_b a_b`, where `n_b ≥ 1` is the
number of elements of `B*` in `b`, and `n_b a_b = a_b`, since `a_b = 0` when `n_b ≥ 2`
(Step 3).  So `Σ_{e ∈ B*} a_{blk(e)} = Σ_{b ∈ blk(B*)} a_b`, and the difference is the sum of
`a_b` over the `k - r` blocks missed by `B*`.  Each of them is avoidable in `M^v`
(Proposition 4(4) with the witness `B*`), so `a_b = τ` (Proposition 5(4)), and the difference
is `(k - r) τ`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `def:update`: `ν(t)`, `τ`, `λ_b` (`∞` if none), `a_b = (τ - λ_b)₊` | `nu (N t) blk`, `tau`, `lam`, `update`, `BaseMisses` | `Rainbow/Update.lean` | definitions |
| `def:update`: "if `ν₀ > r` we set `a = 0`" | `tau_eq_zero`, `update_eq_zero` | same | proved |
| "the minima exist by (F2), (F4) and (F5)" | `isLeast_sInf`, `isLeast_tau`, `exists_isLeast_lam`, `lam_eq_top_iff`, `lam_le_iff` | same | proved |
| "for `t < τ` we have `ν(t) = r`" | `nu_eq_of_lt_tau` (also `succ_le_nu_of_tau_le`) | same | proved |
| "a base of `N(t)` meeting `r` blocks contains a rainbow independent set of size `r` and conversely" | `exists_isRainbowIndep_subset`, `exists_isBase_of_isRainbowIndep`, `mem_Av_iff_baseMisses` | same | proved |
| "the set of `t` at which `b` is avoidable is `[λ_b, ∞)`" | `mem_Av_iff_lam_le` (`[λ_b, τ)` within `[0, τ)`), `lam_le_iff` | same | proved in corrected form (Section 3, item 1) |
| `eq:update-integral` | `update_eq_integral`; measure form `volume_eq`; on `[0, T]`, `T ≥ τ`: `update_eq_intervalIntegral` | same | proved, for `r ≤ ν₀` |
| Figure `fig:axis` (values of `a_b`) | `update_eq_tau`, `update_eq_max`, `update_eq_zero_of_lam_eq_top`, `update_le_tau` | same | proved |
| `thm:validity`(1) | `psi_update` | `Rainbow/Validity.lean` | proved |
| `thm:validity`(2) | `isMinBase_update`; "`ν₀` does not decrease": `nu_le_nu_update` | same | proved |
| `thm:validity`, both items | `validity` | same | proved |
| proof, Steps 1 and 2 (the path, the right derivative) | `path`, `path_tau`, `continuous_path`, `eventually_path_eq` | same | proved |
| proof, Steps 3 and 4 (the sandwich, the old base) | `sandwich`, with `Pos.mem_pos_of_isMinBase_shift` (Lemma `lem:path`) and P2's `card_av_add_nu` (Lemma `lem:avoidable`(2)) | same | proved |
| proof, Step 5 | `isMinBase_path`, `update_eq_zero_of_mem_of_mem` | same | proved |


## 3. Differences from the paper

1. **The avoidable set after `τ`.**  The paragraph after Definition `def:update` says that "the
   set of `t` at which `b` is avoidable is `[λ_b, ∞)` by (F2)".  This is false for `t ≥ τ`:
   once `ν(N(t)) = k` (for instance at stage `r = k - 1`), every rainbow independent set of size
   `k` meets every block and `Av(N(t)) = ∅`.  Example: `M = U_{2,3}` on `{x, y, z}`, blocks
   `{x}` and `{y, z}`, `v = (1, 0, 0)`; `M^v` has the single base `{y, z}`, `ν₀ = 1 = r` and
   `S₀ = {1}`; for every admissible family `ν(N(t)) = 2` for `t ≥ τ` (by (F4)), and then block
   `1` is not avoidable.  What holds, and what the integral uses, is the statement for `t < τ`
   (`mem_Av_iff_lam_le`), together with the statement for bases (`lam_le_iff`).  Proposed
   wording: "and the set of $t<\tau$ at which $b$ is avoidable is $[\lambda_b,\tau)$ by (F2)".
2. **Which properties give the minima.**  The text says "The minima exist by (F2), (F4) and
   (F5)".  For `τ` the proof also uses (F1) and the rank of `M`: a rainbow base of `N(t)` has
   `ν(N(t)) ≥ r + 1` elements only because `N(t)` has rank `k`, which follows from `N(0) = M^v`
   (F1) and (F2).  `λ_b` needs only (F5).  Proposed wording: "The minima exist by (F1), (F2),
   (F4) and (F5)."
3. **`λ_b = ∞` and the case `ν₀ > r`.**  `λ_b` lives in `[0, ∞]` (`ℝ≥0∞`), where the infimum
   of the empty set is `∞` and `τ - ∞ = 0`; so `a_b = (τ - λ_b)₊` needs no case split.  The case
   `ν₀ > r` of the definition is a theorem (`update_eq_zero`, from (F1) alone): then `τ = 0`.
   No change to the paper; the proof of Theorem `thm:C` already says "since then `τ = 0`".
4. **Equation `eq:update-integral` for `r ≤ ν₀`.**  The Lean statements (`volume_eq`,
   `update_eq_integral`, `update_eq_intervalIntegral`) hold for every `r ≤ ν₀`, covering both
   cases of the definition; integrability of the integrand is part of each statement, since
   Mathlib assigns the value `0` to the integral of a non-integrable function.  No change to the
   paper.
5. **Hypotheses of Theorem `thm:validity`.**  The Lean theorem `validity` assumes `M.E = E`,
   `ν₀ = r` and admissibility.  It does not assume `rank M = k` or `r < k`: the proof never
   uses that `τ` is attained, which is where they enter (Proposition 3(1)).  The paper's
   statement is the special case.  `nu_le_nu_update` holds for every `r ≤ ν₀`, the form that the
   schedule of Theorem `thm:C` applies at every state of stage `r`.  No change to the paper.
6. **The integration of the right derivative.**  The paper integrates
   `φ'(s+) ≥ k - r` (Step 3) and the matching upper bound (Step 4).  The Lean proof uses the
   same two facts in a different order: the right-derivative argument becomes a real induction
   on the closed set of `s` at which `B*` is a minimum base of `v(s)` (Theorem 10), and item 1
   is then evaluated at `s = τ` by grouping `Σ_{e ∈ B*} a_{blk(e)}` by blocks (Theorem 11,
   Steps 3 and 4).  The inequality `|B* ∩ E_{S_s}| ≥ |S_s| - (k - r)` of Step 4 holds for every
   set of blocks; that the missed blocks lie in `S₀` is used only for `a_b = τ` on them.  No
   change to the paper is needed.
7. **`S_s = Av(N(s))`.**  Step 3 of the proof attributes `S_s = Av(N(s))` to (F2); it uses the
   paragraph after Definition `def:update` (Proposition 4(5)), which rests on (F2), (F5) and
   `ν(N(s)) = r`.  Optional wording: "and $S_s=\Av(N(s))$ by the paragraph after
   Definition~\ref{def:update}".


## 4. Line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Update.lean` | 380 |
| `SignedTropical/Rainbow/Validity.lean` | 286 |


## 5. Not done

Every item of the assignment is proved: Definition `def:update` with the existence of the
minima and the facts of the following paragraph, equation `eq:update-integral` in measure,
Lebesgue and interval form, and Theorem `thm:validity` with both items and the last clause.  The
conversion of `eq:update-integral` into the gap sum `C_{F_b}(D⁺)` of Lemma `lem:oneupdate`
belongs to the circuit agent; `update_eq_integral` has the shape of E2's
`gapSum_eq_integral_Ioi`, and `update_eq_intervalIntegral` that of E2's
`gapSum_eq_intervalIntegral` with `T = max D⁺ ≥ τ`.
