# P5: the potential and the stage bound (Theorem `thm:potential`)

Natural-language companion of `SignedTropical/Rainbow/Potential.lean`, namespace
`SignedTropical.Rainbow.Potential`.  Source: `daishu/paper/greedy_intersection.tex`, Section 4.6
(Termination): the definition of `Π`, Theorem `thm:potential` and Steps 1 to 8 of its proof; the
referee-checked version is Theorem 8 of `daishu/docs/phase2a-rainbow-2026-10-11.md`, Section 4.3.

Build status: `lake build SignedTropical.Rainbow.Potential` succeeds with no error and no warning.
No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
All 21 theorems of the module depend only on `propext`, `Classical.choice` and `Quot.sound`
(checked with `#print axioms`).  Imports: `Rainbow/Validity` (P3, with `Rainbow/Update`) and
`Rainbow/POSL` (P4), used unchanged; through them `Rainbow/Exchange` (P2), `Rainbow/MinBases`
(P0a) and `Rainbow/Connectivity` (P0b).


## Notation

`E = Fin m`, `M` a matroid with ground set `E` (`hE : M.E = Set.univ`), rank `k`
(`hk : rank M = k`) and a rainbow base (`hM : ∃ B, IsRainbowBase M blk B`); the blocks are the
fibres of `blk : E → Fin k`, and `E_Q = blockSet blk Q`.  A state is a weight `v` (in the
algorithm `v = w - p_blk = shift blk w p`).  `M^v = minBases M v`, `ν₀ = ν(M^v)`,
`S₀ = Av(M^v)`.  Stage `r`: `ν₀ = r < k`.  `N(t) = POSL.N M v t` is the PO-SL family of
Definition `def:posl`, admissible by P4's `POSL.isAdmissible hE hM v`; `u_t = POSL.u M v t`,
`PO_t = POSL.PO M v t`, and the clusters at scale `t` are the classes of
`POSL.SameCluster M PO_t (POSL.near v t)`.  `τ = tau N blk r`, `λ_b = lam N blk r b`, and
`a = update N blk r` is the update `a_b = (τ - λ_b)₊` of Definition `def:update` (P3);
`v' = v - a_blk = shift blk v a`.

**Definition.**  `piPairs blk S v = Π = {(y, g) : y ∈ E_S, g ∉ E_S, v_y ≤ v_g}` (a `Finset` of
ordered pairs of elements), ties included.

**Definition (the stage map).**  `stageMap M blk w r p = p + update (POSL.N M (shift blk w p)) blk r`:
the stage-`r` update `p ↦ p + a(p)`, with `a(p)` the PO-SL update at `v = w - p_blk`.
`ν₀(p)` below means `nu (minBases M (shift blk w p)) blk`, and `p_n = stageMap^[n] p`.

**Definition (the potential of Step 8).**
`Phi M blk w r p = (|S₀| - (k - r)) (⌊m² / 4⌋ + 1) + |Π(v)|`, with `v = w - p_blk`,
`S₀ = Av(M^v)`, `Π` formed with `S₀`, and natural-number subtraction (`⌊m² / 4⌋` is
`m ^ 2 / 4` in `ℕ`).


## 1. Results

### 1.1 The size of `Π`

**Lemma 1.**  `card_piPairs_le`.  For every set of blocks `S` and every `v`,
`|Π| ≤ ⌊m² / 4⌋`.

*Proof.*  Step 1, `Π ⊆ E_S × (E \ E_S)`, of size `a (m - a)` with `a = |E_S| ≤ m`.  Step 2,
writing `m = a + b`, `4ab ≤ (a + b)²` since `(a - b)² ≥ 0` (in `ℤ`), so `a b ≤ ⌊m² / 4⌋`.

### 1.2 Items 1 and 2 (Steps 1 and 2), for every admissible family

In this section `N` is any admissible family for `v` (`IsAdmissible M blk v N`) and
`a = update N blk r`.

**Proposition 2 (Theorem `thm:potential`(1)).**  `av_subset_av_update`.  Let `ν₀ = r`.  If
`ν(M^{v'}) = r`, then `Av(M^{v'}) ⊇ S₀`.

*Proof.*  Step 1, a block `b ∈ S₀` is missed by a base `B` of `M^v` meeting exactly `r` blocks
(P3's `mem_Av_iff_baseMisses`, as `ν₀ = r`).  Step 2, `B` is a minimum base of `v'` by Theorem
`thm:validity`(2) (`isMinBase_update`), so a base of `M^{v'}` (Lemma `lem:minbases`(3)).
Step 3, as `ν(M^{v'}) = r`, the same lemma of P3 gives `b ∈ Av(M^{v'})`.

**Proposition 3 (Theorem `thm:potential`(2)).**  `piPairs_subset`.  Let `ν₀ = r`.  Then
`Π(v') ⊇ Π(v)`, both formed with `S₀`.

*Proof.*  Let `(y, g) ∈ Π(v)`.  Step 1, `blk(y) ∈ S₀`, so `a_{blk(y)} = τ` (P3's
`update_eq_tau`: blocks of `S₀` have `λ_b = 0`).  Step 2, `a_{blk(g)} ≤ τ` (`update_le_tau`).
Step 3, `v'_y = v_y - τ ≤ v_g - τ ≤ v_g - a_{blk(g)} = v'_g`.

### 1.3 Steps 3 and 4: the first event and a rank jump

Here `N` is again any admissible family.

**Proposition 4 (Step 3, the first event).**  `exists_first_event`.  Let `ν₀ = r < k`.  There
is `δ` with `0 < δ ≤ τ`, `Av(N(t)) = S₀` for `0 ≤ t < δ`, and `Av(N(δ)) ≠ S₀` or
`ν(N(δ)) > r`.  That is, `δ` is the least `t ≥ 0` at which `Av(N(t)) ≠ S₀` or `ν(N(t)) > r`
(for `t < δ ≤ τ` also `ν(N(t)) = r`).

*Proof.*  Step 1, the set `{t ≥ 0 : Av(N(t)) ≠ S₀ or ν(N(t)) > r}` contains `τ`, since
`ν(N(τ)) ≥ r + 1` (P3's `isLeast_tau`, which uses `rank M = k` and `r < k`).  Step 2, by (F5)
it has a least element `δ` (P3's `isLeast_sInf`); `δ ≤ τ`.  Step 3, `δ ≠ 0`: at `t = 0`,
`N(0) = M^v` (F1), where `Av = S₀` and `ν = r`.  Step 4, for `0 ≤ t < δ`, `t` is not in the
set, so `Av(N(t)) = S₀`.

The paper adds that every block `b ∉ S₀` has `λ_b ≥ δ`; in Lean this enters Step 7 through P3's
`update_le_of_forall_notMem`, whose proof is that argument: `b` is avoidable at no `t < δ`, and
for `t < τ` avoidability at `t` is `λ_b ≤ t` (P3's `mem_Av_iff_lam_le`).

**Proposition 5 (Step 4, a rank jump).**  `rk_lt_rk`.  Let `ν₀ = r`, `δ ≥ 0`, and
`Av(N(δ)) ≠ S₀` or `ν(N(δ)) > r`.  Then `r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`.

*Proof.*  Step 1, Lemma `lem:avoidable`(2) for `M^v` (P2's `card_av_add_nu`):
`|S₀| + r = k + r_{M^v}(E_{S₀})`; Lemma `lem:avoidable`(1) for `N(δ)` (P2's `card_add_nu_le`):
`|S₀| + ν(N(δ)) ≤ k + r_{N(δ)}(E_{S₀})`.  Step 2, if `ν(N(δ)) > r`, these two give
`r_{N(δ)}(E_{S₀}) ≥ r_{M^v}(E_{S₀}) + 1`.  Step 3, otherwise `ν(N(δ)) = r`, since
`ν(N(δ)) ≥ ν₀` (P3's `nu_zero_le`), and `Av(N(δ)) ≠ S₀`.  Step 4, `S₀ ⊆ Av(N(δ))`: a block `b ∈ S₀` is missed by a base of
`M^v = N(0)` meeting `r` blocks, which is a base of `N(δ)` by (F2) (`BaseMisses.mono`), and
`ν(N(δ)) = r`.  Step 5, if `S₀` attained equality in Lemma `lem:avoidable`(1) for `N(δ)`, item 3
of that lemma (P2's `av_subset`) would give `Av(N(δ)) ⊆ S₀`, so `Av(N(δ)) = S₀` by Step 4,
against Step 3.  So the inequality of Step 1 for `N(δ)` is strict, and with the equality for
`M^v` it gives `r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`.

### 1.4 Steps 5 to 7 for PO-SL

**Lemma 6.**  `exists_isBase_card_inter_eq`.  A matroid `M'` on `E` has a base `B` with
`|B ∩ X| = r_{M'}(X)`, for every `X ⊆ E`.

*Proof.*  Extend a basis `I` of `X` to a base `B`; then `I ⊆ B ∩ X`, which is independent and
inside `X`, so `r(X) = |I| ≤ |B ∩ X| ≤ r(X)`.

**Proposition 7 (Step 5, a tie across `S₀`).**  `exists_tie`.  Let `N` be PO-SL, `δ ≥ 0`, and
`r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`.  Then there are `g` with `blk(g) ∉ S₀` and `y` with
`blk(y) ∈ S₀` in one cluster at scale `δ`, with `v_g < v_y`.

*Proof.*  Write `X = E_{S₀}`.  Step 1, take a base `B` of `M^v` with `|B ∩ X| = r_{M^v}(X)`
(Lemma 6); it is a minimum base of `v`, and a base of `N(δ)` by (F1) and (F2).  Step 2,
`B ∩ X` does not span `X` in `N(δ)`: otherwise it would be a basis of `X` in `N(δ)`, of size
`r_{N(δ)}(X) > r_{M^v}(X) = |B ∩ X|`.  So some `y ∈ X` lies outside the closure of `B ∩ X` in
`N(δ)`; in particular `y ∉ B`.  Step 3, the fundamental circuit `C` of `y` in `B + y` in
`N(δ)` is not inside `(B ∩ X) + y`, since `y` lies in the closure of `C - y`; so some
`g ∈ C - y` lies in `B \ X`.  Step 4, `N(δ) = M^{u_δ}` and `B` is a minimum base of `u_δ`
(P4's `isBase_N_iff`); by Lemma `lem:minbases`(3) (P0a's `IsMinBase.fundCircuit_minBases`),
`C = {y} ∪ {f ∈ C_M(B, y) : u_δ(f) = u_δ(y)}`, so `g ∈ C_M(B, y)` and `u_δ(g) = u_δ(y)`.
Step 5, `g` and `y` lie on the circuit `C_M(B, y)` of `M`, so in one component; `g ∈ B ⊆ PO_δ`
(P4's `subset_PO_of_isBase_N`), so `u_δ(y) = u_δ(g) ≤ m` and `y ∈ PO_δ` (`u_le_iff_mem`);
P4's `u_eq_u_iff` puts `g` and `y` in one cluster at scale `δ`.  Step 6, `v_g ≤ v_y`, since `B`
is a minimum base of `v` and `g ∈ C_M(B, y)` (P0b's `le_of_mem_fundCircuit`).  If `v_g = v_y`,
then `B - g + y` is a minimum base of `v` (P0a's `isMinBase_exchange_iff`), so a base of `M^v`,
and it contains `(B ∩ X) + y`, as `g ∉ X`: it has `r_{M^v}(X) + 1` independent elements in
`X`, which is impossible.  So `v_g < v_y`.

**Proposition 8 (Step 6, a crossing pair).**  `exists_crossing`.  Let `S` be a set of blocks,
and let `g` with `blk(g) ∉ S` and `y` with `blk(y) ∈ S` lie in one cluster at scale `δ`, with
`v_g < v_y`.  Then the cluster contains `z₁` with `blk(z₁) ∉ S` and `z₂` with `blk(z₂) ∈ S` such
that `0 < v_{z₂} - v_{z₁} ≤ δ`.

*Proof.*  Let `K` be the cluster of `g`.  Step 1, among the elements `z ∈ K` with
`blk(z) ∉ S` and `v_z < v_y` (`g` is one) take `z₁` of largest value `α = v_{z₁}`.  Step 2,
among the elements `z ∈ K` with `blk(z) ∈ S` and `v_z > α` (`y` is one) take `z₂` of least
value `β = v_{z₂}`; so `0 < β - α`.  Step 3, no `x ∈ K` has `α < v_x < β`: if `blk(x) ∈ S`,
then `β ≤ v_x` by Step 2; if `blk(x) ∉ S` and `v_x < v_y`, then `v_x ≤ α` by Step 1; otherwise
`v_x ≥ v_y ≥ β`.  Step 4, `z₁` and `z₂` lie in one cluster with consecutive values, so
`β - α ≤ δ` (P4's `SameCluster.sub_le`).

**Theorem 9 (Theorem `thm:potential`(3), Step 7).**  `piPairs_ne`.  Let `ν₀ = r < k` and `a` the
PO-SL update.  Then `Π(v') ≠ Π(v)`, both formed with `S₀`.

*Proof.*  Step 1, Proposition 4 gives the first event `δ`, Proposition 5 the rank jump at `δ`,
Proposition 7 a tie `g`, `y`, and Proposition 8 the crossing pair `z₁`, `z₂` with `S = S₀`,
`α = v_{z₁} < β = v_{z₂}` and `β - α ≤ δ`.  Step 2, `a_{blk(z₂)} = τ` (Step 2 of the paper,
P3's `update_eq_tau`), and `a_{blk(z₁)} ≤ τ - δ`, since `blk(z₁) ∉ S₀ = Av(N(t))` for
`0 ≤ t < δ` (Proposition 4 and P3's `update_le_of_forall_notMem`, which needs `δ ≤ τ`).
Step 3, `v'_{z₂} - v'_{z₁} ≤ (β - α) - τ + (τ - δ) ≤ 0`, so `(z₂, z₁) ∈ Π(v')`, while
`(z₂, z₁) ∉ Π(v)` as `v_{z₂} > v_{z₁}`.

**Theorem 10 (Theorem `thm:potential`, items 1 to 3).**  `potential`.  Let `M` have ground set
`E`, rank `k` and a rainbow base, let `ν₀ = ν(M^v) = r < k`, let `a` be the PO-SL update,
`v' = v - a_blk` and `S₀ = Av(M^v)`.  Then
1. if `ν(M^{v'}) = r`, then `Av(M^{v'}) ⊇ S₀`;
2. `Π(v') ⊇ Π(v)`, both formed with `S₀`;
3. `Π(v') ≠ Π(v)`.

*Proof.*  Proposition 2 and Proposition 3 for the admissible family PO-SL
(`POSL.isAdmissible`), and Theorem 9.

### 1.5 Step 8: the stage bound

**Lemma 11.**  `card_av_bounds`.  If `ν₀ = r < k`, then `k - r ≤ |S₀| ≤ k - 1`.

*Proof.*  Step 1, `|S₀| + r = k + r_{M^v}(E_{S₀}) ≥ k` (Lemma `lem:avoidable`(2)).  Step 2,
if `|S₀| = k`, then `S₀` is every block, `E_{S₀} = E`, and `r_{M^v}(E) = rank M = k` (P0a's
`rank_minBases`), so `k + r = 2k` and `r = k`, against `r < k`.

**Lemma 12 (the stage map).**
1. `shift_stageMap`: `w - (p + a(p))_blk = v - a(p)_blk` with `v = w - p_blk`.
2. `stageMap_eq_self`: if `ν₀(p) > r`, then `stageMap p = p` (an update at a state with
   `ν₀ > r` is the identity, since then `τ = 0`; P3's `update_eq_zero` with P4's `N_zero`).
   `iterate_stageMap_eq_self`: then every iterate is `p`.
3. `nu_le_nu_stageMap`: if `ν₀(p) ≥ r`, then `ν₀(stageMap p) ≥ ν₀(p)` (Theorem
   `thm:validity`(2), P3's `nu_le_nu_update`).  `le_nu_iterate`: if `ν₀(p) ≥ r`, then
   `ν₀(p_n) ≥ r` for every `n`.

**Lemma 13.**  `Phi_lt`.  If `ν₀(p) = r < k`, then `Phi(p) < r (⌊m² / 4⌋ + 1)`.

*Proof.*  By Lemma 11, `|S₀| - (k - r) + 1 ≤ r`, and `|Π| ≤ ⌊m² / 4⌋` by Lemma 1.  So
`Phi(p) ≤ (|S₀| - (k - r)) (Q + 1) + Q < (|S₀| - (k - r) + 1)(Q + 1) ≤ r (Q + 1)`, with
`Q = ⌊m² / 4⌋`.

**Proposition 14 (Step 8, the potential grows).**  `Phi_lt_Phi_stageMap`.  If `r < k`,
`ν₀(p) = r` and `ν₀(stageMap p) = r`, then `Phi(p) < Phi(stageMap p)`.

*Proof.*  Let `S₀`, `S₀'` be the avoidable sets before and after, `Q = ⌊m² / 4⌋`.  Step 1,
`S₀ ⊆ S₀'` by Theorem 10(1).  Step 2, if `S₀' = S₀`, then `Π(v) ⊊ Π(v')`, both formed with
`S₀`, by Theorem 10(2), (3), so the second term of `Phi` grows and the first is unchanged.
Step 3, if `S₀ ⊊ S₀'`, then `|S₀'| ≥ |S₀| + 1`, and, as `|S₀| ≥ k - r` (Lemma 11),
`Phi(stageMap p) ≥ (|S₀'| - (k - r))(Q + 1) ≥ (|S₀| - (k - r))(Q + 1) + Q + 1 > Phi(p)`, since
`|Π(v)| ≤ Q` (Lemma 1).

This is the counting of the paper in one number: by Lemma 11 and item 1 the set `S₀` takes at
most `r` values in a stage, ordered by inclusion (the first term of `Phi`), and while it is
fixed `Π` grows at every update and has at most `Q + 1` sizes (the second term).

**Theorem 15 (Theorem `thm:potential`, the consequence).**  Let `M` have ground set `E`, rank `k`
and a rainbow base, let `r < k`, and let `p` satisfy `ν₀(p) ≥ r`.
1. `le_Phi_iterate`: if `ν₀(p_n) = r`, then `n ≤ Phi(p_n)`.
2. `lt_of_nu_iterate_eq` (counting form): if `ν₀(p_n) = r`, then `n < r (⌊m² / 4⌋ + 1)`.  So
   at most `r (⌊m² / 4⌋ + 1)` iterates have `ν₀ = r`, and at most that many updates are applied
   at states of stage `r`.
3. `stage_bound`: `ν₀(p_n) ≥ r + 1` for `n = r (⌊m² / 4⌋ + 1)`: stage `r` ends after at most
   `r (⌊m² / 4⌋ + 1)` updates.
4. `stage_bound_of_le`: `ν₀(p_n) ≥ r + 1` for every `n ≥ r (⌊m² / 4⌋ + 1)`.

*Proof.*  Step 1, item 1 by induction on `n`.  For `n = 0` it is clear.  If `ν₀(p_{n+1}) = r`,
then `r ≤ ν₀(p_n) ≤ ν₀(p_{n+1}) = r` (Lemma 12(3)), so `ν₀(p_n) = r`, and the induction
hypothesis and Proposition 14 give `n ≤ Phi(p_n) < Phi(p_{n+1})`.  Step 2, item 2 is item 1 with
Lemma 13.  Step 3, item 3: `ν₀(p_n) ≥ r` (Lemma 12(3)), and `ν₀(p_n) = r` is excluded by
item 2 at `n = r (⌊m² / 4⌋ + 1)`.  Step 4, item 4: write `n = j + r (⌊m² / 4⌋ + 1)`; the state
after `r (⌊m² / 4⌋ + 1)` updates has `ν₀ > r` by item 3, so the remaining `j` updates are the
identity (Lemma 12(2)).


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| Section 4.6, `Π(v)` (ties included) | `piPairs`, `mem_piPairs` | `Rainbow/Potential.lean` | defined |
| Step 8, `|Π| ≤ ⌊m²/4⌋` | `card_piPairs_le` | same | proved |
| `thm:potential`(1), Step 1 | `av_subset_av_update` (every admissible family) | same | proved |
| `thm:potential`(2), Step 2 | `piPairs_subset` (every admissible family) | same | proved |
| Step 3, the first event `δ` | `exists_first_event` | same | proved |
| Step 4, a rank jump | `rk_lt_rk` | same | proved |
| Step 5, a tie across `S₀` | `exists_tie`, `exists_isBase_card_inter_eq` | same | proved |
| Step 6, a crossing pair | `exists_crossing` | same | proved |
| `thm:potential`(3), Step 7 | `piPairs_ne` | same | proved |
| `thm:potential`, items 1 to 3 | `potential` | same | proved |
| Step 8, `k - r ≤ |S₀| ≤ k - 1` | `card_av_bounds` | same | proved |
| Step 8, counting | `Phi`, `Phi_lt`, `Phi_lt_Phi_stageMap`, `le_Phi_iterate` | same | proved |
| the stage-`r` update map `p ↦ p + a` | `stageMap`, `shift_stageMap` | same | defined |
| "an update at a state with `ν₀ > r` is the identity" (proof of `thm:C`, Step 1) | `stageMap_eq_self`, `iterate_stageMap_eq_self` | same | proved |
| "`ν₀` never decreases" along a stage | `nu_le_nu_stageMap`, `le_nu_iterate` | same | proved |
| "stage `r` ends after at most `r(⌊m²/4⌋+1)` updates" | `stage_bound`, `stage_bound_of_le`, `lt_of_nu_iterate_eq` | same | proved |
| remark: with strict inequality item 3 fails on `M(K₄)` | none | none | not formalized (Section 5) |


## 3. Differences from the paper

1. **The hypothesis `r < k`.**  The theorem says "Fix a stage `r`, a state with `ν₀ = r`".  The
   Lean statements assume `r < k`, the standing hypothesis of Definition `def:admissible`
   ("Let `ν₀ = r < k`"), which the update needs (for `r = k` there is no `t` with
   `ν(t) ≥ r + 1`).  Item 3 is false without it: for `ν₀ = k`, `S₀ = ∅` and `Π = ∅`.  Proposed
   wording for the first sentence of Section 4.6: "Fix a stage $r<k$, a state with $\nu_0=r$, its
   update $a$ under PO-SL and $v'=v-a_{\blk}$."
2. **Step 4.**  "Otherwise $\Av(N(\delta))\supsetneq S_0$ by (F2)" compresses two facts: the
   inclusion uses (F1), (F2) and `ν(N(δ)) = r`, and the strictness is the choice of `δ`.
   Proposed wording: "Otherwise $\nu(N(\delta))=r$; a base of $M^{v}$ meeting $r$ blocks and
   missing a block of $S_0$ is a base of $N(\delta)$ by (F1) and (F2), so
   $\Av(N(\delta))\supseteq S_0$, with $\Av(N(\delta))\ne S_0$ by the choice of $\delta$; so
   $S_0$ does not attain the maximum $k-r$ by Lemma~\ref{lem:avoidable}(3)."
3. **Step 5, "one cluster".**  Sharing a cluster needs `g, y ∈ PO_δ`; `u_δ(g) = u_δ(y)` alone
   does not give it for elements outside `PO_δ`.  `g ∈ B ⊆ PO_δ` because a minimum base of
   `u_δ` lies in `PO_δ` (P4, Section 3, item 2), and then `u_δ(y) = u_δ(g) ≤ m` puts `y` in
   `PO_δ`.  Proposed wording: "By Lemma~\ref{lem:minbases}(3) for $u_\delta$, $g\in C(B,y)$ and
   $u_\delta(g)=u_\delta(y)$; as $g\in B\subseteq\PO_\delta$, also $y\in\PO_\delta$, so $g$ and
   $y$ lie in one component and one cluster."
4. **Step 8, the count per value of `S₀`.**  The step says that `Π` grows at every update while
   `S₀` is fixed, and that `|Π| ≤ ⌊m²/4⌋`; the `+ 1` of the bound comes from the `⌊m²/4⌋ + 1`
   possible sizes of `Π`.  The Lean proof combines both counts in the potential `Phi`
   (Proposition 14).  Proposed wording for the last sentence: "While it is fixed, item 3
   enlarges $\Pi\subseteq E_{S_0}\times(E\setminus E_{S_0})$, of size at most
   $\lfloor m^{2}/4\rfloor$, at every update, so at most $\lfloor m^{2}/4\rfloor+1$ updates start
   from a state with a given $S_0$."
5. **Generality.**  Items 1 and 2 hold for every admissible family (`av_subset_av_update`,
   `piPairs_subset`); only item 3 uses PO-SL (Steps 5 and 6).  Steps 3 and 4 hold for every
   admissible family.  No change to the paper needed.
6. **Form of the consequence.**  "Stage `r` ends after at most `r(⌊m²/4⌋+1)` updates" is stated
   for the iterated stage map from any `p` with `ν₀(p) ≥ r` (`stage_bound`): after
   `r(⌊m²/4⌋+1)` iterations, `ν₀ ≥ r + 1`.  The counting form `lt_of_nu_iterate_eq` bounds the
   number of iterates with `ν₀ = r`.  No change needed.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Potential.lean` | 428 |


## 5. Not done

* **The remark after the definition of `Π`** ("With strict inequality item 3 below fails on the
  cycle matroid of `K₄`") is not formalized: it would need the PO-SL family, `τ` and the `λ_b`
  of a concrete graphic matroid computed in Lean through noncomputable definitions (closures,
  clusters, minimum bases), for a remark that no result uses.  An independent exact-arithmetic
  script (not kept in the package) confirms it on the instance of the research note: `M(K₄)`
  with edges `01, 02, 03, 12, 13, 23`, blocks `[0, 0, 0, 0, 1, 2]`, `v = (0, 0, 3, 1, 2, 2)`,
  `r = 2`: `ν₀ = 2`, `S₀ = {1, 2}`, `τ = 1`, `a = (0, 1, 1)`, `v' = (0, 0, 3, 1, 1, 1)`; the
  strict pairs are `{(13, 03), (23, 03)}` before and after, while `Π` gains `(13, 12)` and
  `(23, 12)`.
* The schedule of Theorem `thm:C` (stages `r = 1, …, k - 1`) is left to the Theorem C agent; this
  module supplies the stage map and its bound.


## 6. API for later agents (Theorem C)

Namespace `SignedTropical.Rainbow.Potential`; `ν₀(p)` is
`nu (minBases M (shift blk w p)) blk`.

* `stageMap M blk w r p : Fin k → ℝ`, defined as `p + update (POSL.N M (shift blk w p)) blk r`
  (unfold by `rfl` or `rw [stageMap]`); with P3's `psi_update` this gives
  `Ψ(stageMap p) = Ψ(p) + (k - r) τ` when `ν₀(p) = r`.
* `shift_stageMap : shift blk w (stageMap M blk w r p) = shift blk (shift blk w p) (update (POSL.N M (shift blk w p)) blk r)`.
* `stageMap_eq_self (hE) (h : r < ν₀(p)) : stageMap M blk w r p = p`.
* `iterate_stageMap_eq_self (hE) (h : r < ν₀(p)) (n) : (stageMap M blk w r)^[n] p = p`.
* `nu_le_nu_stageMap (hE) (hM) (h : r ≤ ν₀(p)) : ν₀(p) ≤ ν₀(stageMap M blk w r p)`.
* `le_nu_iterate (hE) (hM) (h : r ≤ ν₀(p)) (n) : r ≤ ν₀((stageMap M blk w r)^[n] p)`.
* `stage_bound (hE) (hk : rank M = k) (hM) (hrk : r < k) (hp : r ≤ ν₀(p)) :
  r + 1 ≤ ν₀((stageMap M blk w r)^[r * (m ^ 2 / 4 + 1)] p)`.
* `stage_bound_of_le (hE) (hk) (hM) (hrk) (hp) (hn : r * (m ^ 2 / 4 + 1) ≤ n) :
  r + 1 ≤ ν₀((stageMap M blk w r)^[n] p)`.
* `lt_of_nu_iterate_eq (hE) (hk) (hM) (hrk) (hp) (hn : ν₀((stageMap M blk w r)^[n] p) = r) :
  n < r * (m ^ 2 / 4 + 1)`.
* `potential (hE) (hk) (hM) (hr : nu (minBases M v) blk = r) (hrk : r < k)`: items 1 to 3 of
  Theorem `thm:potential` at a weight `v`.

Here `hE : M.E = Set.univ`, `hM : ∃ B, IsRainbowBase M blk B`.
