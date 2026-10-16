# P1x: the partition matroid of the columns, `U_{2,4}`, doubling

Natural-language companion of three modules:

* `SignedTropical/Rainbow/Partition.lean`, namespace `SignedTropical.Rainbow.Partition`: the
  partition matroid of the columns, the matroid `N_S` of Corollary `cor:transversal`;
* `SignedTropical/Rainbow/NotMatroid.lean`, namespace `SignedTropical.Rainbow.NotMatroid`:
  Proposition `prop:notmatroid` (Section 4.3);
* `SignedTropical/Rainbow/Doubling.lean`, namespace `SignedTropical.Rainbow.Doubling`:
  Lemma `lem:doubling` and Steps 1 and 2 of the proof of Theorem `thm:D` (Section 5).

Source: `daishu/paper/greedy_intersection.tex`.

Build status: `lake build SignedTropical.Rainbow.Partition`, `lake build
SignedTropical.Rainbow.NotMatroid` and `lake build SignedTropical.Rainbow.Doubling` succeed with
no error and no warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
`extern`, `unsafe` or `opaque`.  All declarations of the three namespaces, auxiliary ones
included, depend only on `propext`, `Classical.choice` and `Quot.sound` (checked with
`Lean.collectAxioms`, and with `#print axioms` on the main results).  The finite checks on
`Fin 4` are kernel `decide` on statements about natural numbers and finite sets.

Notation.  `E = {0, ..., m-1}` (Lean `Fin m`); "`M.E = E`" is the hypothesis
`M.E = Set.univ`, stated only where it is used.  From `Rainbow/Defs.lean`: `theta M v B` is
`θ(B) = max({0} ∪ {v_f - v_e : e ∉ B, f ∈ C(B, e)})` with `C(B, e)` Mathlib's
`M.fundCircuit e B`; `Pos M v t` is `P_t = {B ∈ Bases(M) : θ(B) ≤ t}`; `connRel M e f` says
`e = f` or some circuit contains `e` and `f`; `IsRainbow blk S` says that `S` meets every block
at most once; `blocksMet blk S` is the set of blocks met by `S`; `IsRainbowBase M blk B` says
that `B` is a base and rainbow; `Opt M blk w = inf{w(B) : B a rainbow base}`.  From Phase 1:
`rk M S` (the rank `r(S)`, a natural number) and `rank M = r(E)`.  `M ↾ T` is the restriction,
`M✶` the dual.  For `u ∈ ℝ^E` and `X ⊆ E`, `u(X) = Σ_{e ∈ X} u_e`.


## 1. Results

### 1.1 The partition matroid of the columns (`Partition.lean`)

`col : Fin m → Fin n` sends an element to its column, and the column of `e` is
`{f : col f = col e}`.  The matroid is the matroid `N_S` of the transversal matroids in
Corollary `cor:transversal` (`Classes/Transversal.lean`, notes/E5-transversal.md).

**Definition 1.**  `colMatroid col`: the matroid on `E` (ground set `univ`) in which a set `I`
is independent if and only if `col` is injective on `I`, that is, `I` meets every column at
most once (`indep_iff`, `colMatroid_ground`).  It is built with Mathlib's
`IndepMatroid.ofFinite`; the augmentation axiom is `injOn_augment`.

*Proof of `injOn_augment`.*  Step 1, let `col` be injective on `I` and `J` with `|I| < |J|`.
Then `|col(I)| = |I| < |J| = |col(J)|`, so some `e ∈ J` has `col e ∉ col(I)`.  Step 2, then
`e ∉ I` and `col` is injective on `I + e` (`Set.injOn_insert`).

**Proposition 2 (bases and rank).**

* `isBasis_iff`: `I` is a basis of `X` if and only if `col` is injective on `I`, `I ⊆ X`, and
  every column that meets `X` meets `I`.
* `rk_eq`: `r(S) = |col(S)|`, the number of columns that `S` meets.

*Proof.*  `isBasis_iff`.  Step 1, a basis is independent and contained in `X`.  If some `e ∈ X`
had no element of `I` in its column, then `e ∉ I` and `I + e` would be independent, against
`IsBasis.insert_dep`.  Step 2, conversely, for `e ∈ X \ I` the column of `e` contains some
`f ∈ I`, `f ≠ e`, so `I + e` is dependent, and `Indep.isBasis_of_forall_insert` applies.

`rk_eq`.  Step 1, take a basis `I` of `S`, so `|I| = r(S)` (Phase 1 `card_eq_rk`).  Step 2,
`col` is injective on `I`, so `|I| = |col(I)|`.  Step 3, `col(I) = col(S)`: `⊆` from `I ⊆ S`,
`⊇` from `isBasis_iff`.


### 1.2 `U_{2,4}` (`NotMatroid.lean`)

**Definition 3.**  `unif r m`: the uniform matroid `U_{r,m}` on `E = Fin m` (ground set
`univ`), in which a set is independent if and only if it has at most `r` elements
(`unif_indep_iff`); the augmentation axiom is `ncard_augment`.  `U24 = unif 2 4` on
`{a, b, c, d} = {0, 1, 2, 3}`, and `v24 i = i`, so `v = (0, 1, 2, 3)` (`v24_values`).

**Lemma 4.**  `isBase_iff`: for `r ≤ m`, `B` is a base of `U_{r,m}` if and only if `|B| = r`.
`fundCircuit_eq`: for a base `B` and `e ∉ B`, `C(B, e) = B + e`.

*Proof.*  `isBase_iff`.  Step 1, a base has at most `r` elements.  If it had fewer, some
`e ∉ B` exists (`|B| < r ≤ m`) and `B + e` has at most `r` elements, so it is independent,
against `IsBase.insert_dep`.  Step 2, conversely, a set of `r` elements is independent and
`B + e` has `r + 1` elements for `e ∉ B` (`Indep.isBase_of_forall_insert`).
`fundCircuit_eq`.  Step 1, `B + e` is dependent (`IsBase.insert_dep`) and every proper subset
of it has at most `r` elements, so it is a circuit.  Step 2, it lies in `B + e`, so it is the
fundamental circuit (`IsCircuit.eq_fundCircuit_of_subset`).

**Proposition 5 (Step 1 of the proof of `prop:notmatroid`).**  In `U_{r,m}`, for a base `B`:

* `theta_le_iff`: `θ(B) ≤ t` if and only if `0 ≤ t` and `v_f - v_e ≤ t` for all `f ∈ B` and
  `e ∉ B`;
* `theta_eq`: if `B` and `E \ B` are nonempty,
  `θ(B) = max(0, max_{f ∈ B} v_f - min_{e ∉ B} v_e)`.

*Proof.*  Step 1, by the definition of `θ` and `C(B, e) = B + e`, the pairs `(e, e)` contribute
the gain `0` and the pairs `(e, f)` with `f ∈ B` contribute `v_f - v_e`; this is
`theta_le_iff`.  Step 2, for `theta_eq`: every `v_f - v_e` with `f ∈ B`, `e ∉ B` is at most
`max_B v - min_{E \ B} v`, which gives `≤`; the maximum and the minimum are attained
(`exists_mem_eq_sup'`, `exists_mem_eq_inf'`) at some `f₀ ∈ B`, `e₀ ∉ B`, and
`v_{f₀} - v_{e₀} ≤ θ(B)` together with `0 ≤ θ(B)` gives `≥`.

**Proposition 6 (Proposition `prop:notmatroid`).**  For `U_{2,4}` on `{a, b, c, d}` with
`v = (0, 1, 2, 3)`:

* `theta_values`: `θ` takes the values `0, 1, 2, 2, 3, 3` on `ab, ac, ad, bc, bd, cd`;
* `pos_two`: `P_2 = {ab, ac, ad, bc}`;
* `pos_two_not_exchange`: there are `B₁, B₂ ∈ P_2` and `e ∈ B₁ \ B₂` such that no
  `f ∈ B₂ \ B₁` has `B₁ - e + f ∈ P_2` (namely `B₁ = ad`, `B₂ = bc`, `e = a`: neither `bd` nor
  `cd` lies in `P_2`);
* `not_exists_matroid`, `pos_two_not_matroid`: a family that violates basis exchange in this
  way is not the set of bases of any matroid; in particular `P_2` is not the set of bases of a
  matroid on `{a, b, c, d}`.

*Proof.*  `theta_values`.  Step 1, since `v` takes natural values, `v_f - v_e ≤ c` if and only
if `f ≤ e + c` in `ℕ` (`v24_sub_le_iff`), so for a base `B` (`|B| = 2`, `isBase_U24_iff`),
`θ(B) ≤ c` if and only if `f ≤ e + c` for all `e ∉ B`, `f ∈ B` (`theta_U24_le_iff`).  Step 2,
`θ(B) = c` once this bound holds and either `c = 0` or `f = e + c` for some `e ∉ B`, `f ∈ B`
(`theta_U24_eq`, by `theta_le_iff` at `t = θ(B)`).  Step 3, for each of the six bases these
conditions on `Fin 4` are checked by kernel `decide`.

`pos_two`.  Step 1, `B ∈ P_2` if and only if `|B| = 2` and `f ≤ e + 2` for all `e ∉ B`,
`f ∈ B` (`mem_pos_two_iff`).  Step 2, kernel `decide` compares this with membership in
`{ab, ac, ad, bc}` for all sixteen subsets `B` of `Fin 4`.

`pos_two_not_exchange`.  By `pos_two` the statement concerns the explicit family
`{ab, ac, ad, bc}`; with the witnesses `ad`, `bc`, `a`, kernel `decide` checks that
`B₂ \ B₁ = {b, c}` and that `bd` and `cd` are not in the family.

`not_exists_matroid`.  If the bases of a matroid `N` were the members of the family, the
exchange property of `N` (Mathlib's `IsBase.exchange`) applied to `B₁`, `B₂` and `e` would give
`f ∈ B₂ \ B₁` with `B₁ - e + f` a base of `N`, hence in the family, a contradiction.
`pos_two_not_matroid` is `not_exists_matroid` applied to `pos_two_not_exchange`.


### 1.3 Doubling (`Doubling.lean`)

`E × {1, 2}` is `Fin (m + m)`: `(e, 1)` is `Fin.castAdd m e = finSumFinEquiv (Sum.inl e)`, and
`(e, 2)` is `Fin.addNat e m = Fin.natAdd m e = finSumFinEquiv (Sum.inr e)`; the statements use
`Fin.addNat e m`, the simp normal form (`Fin.natAdd_eq_addNat`).

**Definition 7.**

* `double M₁ M₂`: `N = M₁ ⊕ M₂✶`, Mathlib's `Matroid.sum M₁ M₂✶` on `Fin m ⊕ Fin m` carried to
  `Fin (m + m)` by `Matroid.mapEquiv finSumFinEquiv`.  `double_ground`: its ground set is
  `E × {1, 2}` when `M₁.E = M₂.E = E`.
* `blk m`: the block of `(e, 1)` and of `(e, 2)` is `e` (`blk_castAdd`, `blk_addNat`);
  `weight w`: `w_e` on `(e, 1)` and `0` on `(e, 2)` (`weight_castAdd`, `weight_addNat`).
* `pair A B = A × {1} ∪ B × {2}`; `fst S = {e : (e, 1) ∈ S}`, `snd S = {e : (e, 2) ∈ S}`;
  `lift X = pair X (E \ X) = X × {1} ∪ (E \ X) × {2}`.  Membership and counting:
  `castAdd_mem_pair`, `addNat_mem_pair`, `mem_fst`, `mem_snd`, `castAdd_mem_lift`,
  `addNat_mem_lift`, `fst_pair`, `snd_pair`, `fst_lift`, `pair_fst_snd` (`S = pair (fst S)
  (snd S)` for every `S`), `card_pair` (`|pair A B| = |A| + |B|`), `card_lift` (`|lift X| = m`),
  `pair_univ_univ`, `coe_fst`, `coe_snd`, `preimage_castAdd_pair`, `preimage_addNat_pair`.

**Lemma 8 (sets meeting every block once).**  `isRainbow_lift`, `blocksMet_lift`,
`isTransversal_iff`: a set `S ⊆ E × {1, 2}` meets every block exactly once and chooses the copy
`(e, 1)` exactly for `e ∈ X` (that is, `fst S = X`) if and only if `S = lift X`.

*Proof.*  Step 1, for `S = lift X`: two elements of `lift X` in one block `e` are both `(e, 1)`
(when `e ∈ X`) or both `(e, 2)` (when `e ∉ X`), so `lift X` is rainbow, and it meets the block
`e` at `(e, 1)` or `(e, 2)`.  Step 2, conversely, `(e, 1) ∈ S` if and only if
`e ∈ fst S = X`, if and only if `(e, 1) ∈ lift X`.  Step 3, if `(e, 2) ∈ S` then `(e, 1) ∉ S`,
since `S` meets the block `e` at most once.  Step 4, if `(e, 1) ∉ S`, then `S` meets the block
`e` at some element other than `(e, 1)`, which is `(e, 2)`.

**Proposition 9 (bases of `N`).**  `isBasis_iff`, `isBase_iff`: `I` is a basis of `X` in `N`
if and only if its first copies form a basis of the first copies of `X` in `M₁` and its second
copies a basis of the second copies of `X` in `M₂✶`; likewise for bases.
`isBase_iff_fst_snd` (when `M₂.E = E`): `S` is a base of `N` if and only if `fst S` is a base of
`M₁` and `E \ snd S` is a base of `M₂`.

*Proof.*  Step 1, Mathlib's `mapEquiv_isBasis_iff` and `sum_isBasis_iff` (and the `IsBase`
versions) reduce to the preimages under `Sum.inl` and `Sum.inr` of the image of `S` under
`finSumFinEquiv⁻¹`, which are the preimages of `S` under `e ↦ (e, 1)` and `e ↦ (e, 2)`
(`preimage_inl_image_symm`, `preimage_inr_image_symm`).  Step 2, for `isBase_iff_fst_snd`, a
set `Y` is a base of `M₂✶` if and only if `E \ Y` is a base of `M₂` (`dual_isBase_iff'`).

**Lemma 10 (Lemma `lem:doubling`).**  `doubling` (from `isBase_lift_iff` and
`sum_weight_lift`).  Let `M₁`, `M₂` be matroids on `E` with `M₂.E = E`, and let `X ⊆ E`.  The
set `X × {1} ∪ (E \ X) × {2}` (which meets every block once and chooses `(e, 1)` exactly for
`e ∈ X`, Lemma 8) is a base of `N = M₁ ⊕ M₂✶` if and only if `X` is a base of `M₁` and of
`M₂`, and its weight under `weight w` is `w(X)`.

*Proof.*  Step 1, by `isBase_iff` the set is a base of `N` if and only if its first copies `X`
form a base of `M₁` and its second copies `E \ X` form a base of `M₂✶`.  Step 2, `E \ X` is a
base of `M₂✶` if and only if `E \ (E \ X) = X` is a base of `M₂` (`dual_isBase_iff'`).
Step 3, the weight is a sum over the disjoint union `X × {1} ∪ (E \ X) × {2}`; the first copies
contribute `w(X)` and the second copies `0`.

**Proposition 11 (Theorem `thm:D`, Step 2).**  Let `M₁.E = M₂.E = E`, and write `r₁`, `r₂`,
`r₂*`, `r_N` for the ranks in `M₁`, `M₂`, `M₂✶`, `N`.

* `rk_dual_add_rank`: `r₂*(B) + r₂(E) = r₂(E \ B) + |B|`.
* `rk_pair_eq_add`: `r_N(A × {1} ∪ B × {2}) = r₁(A) + r₂*(B)`.
* `rk_pair`: `r_N(A × {1} ∪ B × {2}) + r₂(E) = r₁(A) + |B| + r₂(E \ B)`.
* `rk_pair_eq_sub`: `r_N(A × {1} ∪ B × {2}) = r₁(A) + |B| + r₂(E \ B) - r₂(E)`, with the
  subtraction of natural numbers justified by `rk_pair`.
* `rk_add_rank`: for every `S ⊆ E × {1, 2}`,
  `r_N(S) + r₂(E) = r₁(fst S) + |snd S| + r₂(E \ snd S)`.

*Proof.*  `rk_dual_add_rank` is Mathlib's `eRk_dual_add_eRank`, read in `ℕ`.  `rk_pair_eq_add`:
Step 1, take a basis `I` of `A` in `M₁` and a basis `J` of `B` in `M₂✶`.  Step 2,
`I × {1} ∪ J × {2}` is a basis of `A × {1} ∪ B × {2}` in `N` (`isBasis_iff` and the preimage
lemmas).  Step 3, `r_N(A × {1} ∪ B × {2}) = |I| + |J| = r₁(A) + r₂*(B)` (`card_pair`, Phase 1
`card_eq_rk`).  `rk_pair` adds `rk_dual_add_rank`; `rk_pair_eq_sub` follows by arithmetic;
`rk_add_rank` is `rk_pair` at `A = fst S`, `B = snd S` (`pair_fst_snd`).

**Proposition 12 (Theorem `thm:D`, Step 1).**  Let `M₁.E = M₂.E = E`.

* `rank_double`: `r(N) + r₂(E) = r₁(E) + m`.
* `rank_eq_rank_of_isBase`: matroids with a common base have equal rank.
* `rank_double_eq`: if `r₁(E) = r₂(E)`, then `N` has rank `m`, the number of blocks.

*Proof.*  Step 1, `rk_pair` at `A = B = E`: `E × {1} ∪ E × {2}` is the ground set, `r₂(∅) = 0`
and `|E| = m`.  Step 2, a common base `X` has `r₁(E) = |X| = r₂(E)` (Phase 1 `card_base`).
Step 3, `rank_double_eq` follows from Step 1 by arithmetic.

**Proposition 13 (rainbow bases of `N`).**  Let `M₁.E = M₂.E = E` and `r₁(E) = r₂(E)`.

* `eq_lift_of_isRainbowBase`: every rainbow base `S` of `N` equals
  `fst S × {1} ∪ (E \ fst S) × {2}`, so it is of the form `X × {1} ∪ (E \ X) × {2}`.
* `isRainbowBase_iff`: `S` is a rainbow base of `N` if and only if
  `S = X × {1} ∪ (E \ X) × {2}` for a common base `X` of `M₁` and `M₂`.
* `exists_isRainbowBase_iff`: `N` has a rainbow base if and only if `M₁` and `M₂` have a
  common base.
* `opt_eq`: `Opt` of `N` with the blocks `blk m` at the weight `weight w` equals
  `inf{w(X) : X a common base of M₁ and M₂}`.

*Proof.*  `eq_lift_of_isRainbowBase`: Step 1, `|S| = r(N) = m` (Phase 1 `card_base`,
`rank_double_eq`).  Step 2, `blk` is injective on `S`, so `S` meets `|S| = m` blocks, that is,
all of them.  Step 3, Lemma 8 gives `S = lift (fst S)`.  `isRainbowBase_iff`: one direction is
`eq_lift_of_isRainbowBase` with `isBase_lift_iff`; the other is `isBase_lift_iff` with
`isRainbow_lift`.  `exists_isRainbowBase_iff` and `opt_eq` follow: by `isRainbowBase_iff` and
`sum_weight_lift` the rainbow bases of `N` and their weights are the sets `lift X` for the
common bases `X`, with weights `w(X)`.


## 2. Correspondence

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| partition matroid of the columns, the matroid `N_S` of `cor:transversal` | `colMatroid`, `colMatroid_ground`, `indep_iff`, `injOn_augment` | `Rainbow/Partition.lean` | defined |
| bases and rank of the column matroid | `isBasis_iff`, `rk_eq` | same | proved |
| `U_{2,4}`, `v = (0, 1, 2, 3)` | `unif`, `unif_ground`, `unif_indep_iff`, `ncard_augment`, `U24`, `v24`, `v24_values`, `isBase_iff`, `isBase_U24_iff` | `Rainbow/NotMatroid.lean` | defined, proved |
| `prop:notmatroid`, Step 1, "the fundamental circuit of `e ∉ B` is `B + e`" | `fundCircuit_eq` | same | proved |
| `prop:notmatroid`, Step 1, formula for `θ` | `theta_eq`, `theta_le_iff` | same | proved |
| `prop:notmatroid`, Step 1, values `0, 1, 2, 2, 3, 3` | `theta_values` (via `theta_U24_le_iff`, `theta_U24_eq`) | same | proved |
| `prop:notmatroid`, `P_2 = {ab, ac, ad, bc}` | `pos_two`, `mem_pos_two_iff` | same | proved |
| `prop:notmatroid`, Step 2, violation of basis exchange | `pos_two_not_exchange` | same | proved |
| "not a matroid" (title of `prop:notmatroid`) | `not_exists_matroid`, `pos_two_not_matroid` | same | proved |
| `N = M₁ ⊕ M₂*`, blocks, weights on `E × {1, 2}` | `double`, `double_ground`, `blk`, `weight`, `pair`, `fst`, `snd`, `lift` and their lemmas | `Rainbow/Doubling.lean` | defined, proved |
| "a rainbow set choosing `(e, 1)` exactly for `e ∈ X`" | `isTransversal_iff`, `isRainbow_lift`, `blocksMet_lift` | same | proved |
| bases of `N` | `isBase_iff`, `isBasis_iff`, `isBase_iff_fst_snd`, `isBase_lift_iff` | same | proved |
| `lem:doubling` | `doubling`, `isBase_lift_iff`, `sum_weight_lift` | same | proved |
| `thm:D`, Step 1, "`N` has rank `m`" | `rank_double`, `rank_double_eq`, `rank_eq_rank_of_isBase` | same | proved |
| `thm:D`, Step 2, rank formula of `N` | `rk_pair`, `rk_pair_eq_sub`, `rk_add_rank`, `rk_pair_eq_add`, `rk_dual_add_rank` | same | proved |
| rainbow bases of `N` are the `X × {1} ∪ (E \ X) × {2}` for common bases `X`; `Opt` | `eq_lift_of_isRainbowBase`, `isRainbowBase_iff`, `exists_isRainbowBase_iff`, `opt_eq` | same | proved |


## 3. Differences from the paper

1. `prop:notmatroid`.  Lean also proves the consequence named in the title: `P_2` is not the
   set of bases of any matroid on `{a, b, c, d}` (`pos_two_not_matroid`).  No change is needed.

2. `lem:doubling`, the hypothesis "of rank `ρ`".  The equivalence and the weight hold for all
   matroids `M₁`, `M₂` on `E` (`doubling`).  Equal ranks are needed for the converse reading
   used in the proof of Theorem `thm:D`: every rainbow base of `N` has the form
   `X × {1} ∪ (E \ X) × {2}` (`eq_lift_of_isRainbowBase`), because `N` then has rank `m`.  The
   paper is correct as written; the hypothesis can stay.

3. `lem:doubling`, "a rainbow set choosing the copy `(e, 1)` exactly for `e ∈ X`".  With
   "rainbow" as defined in Section 4.1 (meets every block at most once), such a set may omit
   both copies of some `e ∉ X`, and then the "if" direction fails.  Example: `M₁ = M₂ = U_{1,2}`
   on `E = {a, b}`, `X = {a}`, a common base; the set `{(a, 1)}` is rainbow and chooses `(e, 1)`
   exactly for `e ∈ X`, but its second copies form `∅`, which is not a base of
   `M₂* = U_{1,2}`, so it is not a base of `N`.  The intended set, as in
   Figure `fig:double`, is `X × {1} ∪ (E \ X) × {2}`, which meets every block once; Lean states
   the lemma for this set and proves that it is the only set meeting every block once with
   first copies `X` (`isTransversal_iff`).  Proposed wording for the statement of
   `lem:doubling`:

   > Let $M_1,M_2$ be matroids of rank $\rho$ on $E$.  On $E\times\{1,2\}$ let
   > $N=M_1\oplus M_2^{*}$, with blocks $\{(e,1),(e,2)\}$ and weight $w_e$ on $(e,1)$, $0$ on
   > $(e,2)$.  The set $X\times\{1\}\cup(E\setminus X)\times\{2\}$, which meets every block once
   > and chooses the copy $(e,1)$ exactly for $e\in X$, is a base of $N$ if and only if $X$ is a
   > common base of $M_1$ and $M_2$, and its weight is $w(X)$.

4. Theorem `thm:D`, Step 2.  The rank formula contains a subtraction of natural numbers; Lean
   states it additively (`rk_pair`) and with truncated subtraction (`rk_pair_eq_sub`), which
   agrees because `r₂(E) ≤ r₁(A) + |B| + r₂(E \ B)`.  No change is needed.

5. Representation.  `E × {1, 2}` is `Fin (m + m)` with `(e, 1) = Fin.castAdd m e` and
   `(e, 2) = Fin.addNat e m` (equal to `Fin.natAdd m e`), so that the doubled matroid is a
   `Matroid (Fin (m + m))` with ground set `univ`, the form in which Theorem `thm:C` is stated.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Partition.lean` | 75 |
| `SignedTropical/Rainbow/NotMatroid.lean` | 201 |
| `SignedTropical/Rainbow/Doubling.lean` | 384 |


## 5. Not done

Nothing in these modules.  Theorem `thm:D`, Steps 3 and 4, and the Boolean rank circuit of `N`
of Step 2 are in `Rainbow/TheoremDRank.lean` and `Rainbow/TheoremD.lean`
(notes/P8-theoremD.md).
