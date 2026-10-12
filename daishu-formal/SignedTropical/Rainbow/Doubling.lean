import SignedTropical.Rainbow.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Common bases as rainbow bases (Lemma `lem:doubling`)

`greedy_intersection.tex`, Section 5: Lemma `lem:doubling`, and Steps 1 and 2 of the proof of
Theorem `thm:D`.

The ground set `E × {1, 2}` of the doubled matroid is `Fin (m + m)`: the copy `(e, 1)` is
`Fin.castAdd m e = finSumFinEquiv (Sum.inl e)` and the copy `(e, 2)` is
`Fin.addNat e m = Fin.natAdd m e = finSumFinEquiv (Sum.inr e)`, written with `Fin.addNat`
because `Fin.natAdd_eq_addNat` is a simp lemma.

* `double M₁ M₂`: `N = M₁ ⊕ M₂✶`, Mathlib's `Matroid.sum` carried to `Fin (m + m)` by
  `finSumFinEquiv`; `blk m`: the block of `(e, 1)` and `(e, 2)` is `e`; `weight w`: `w_e` on
  `(e, 1)` and `0` on `(e, 2)`.
* `pair A B = A × {1} ∪ B × {2}`; `fst S`, `snd S`, with `pair (fst S) (snd S) = S`;
  `lift X = X × {1} ∪ (E \ X) × {2}`.  The sets that meet every block exactly once and choose
  the copy `(e, 1)` exactly for `e ∈ X` are the set `lift X` (`isTransversal_iff`).
* `isBasis_iff`, `isBase_iff`, `isBase_iff_fst_snd`: `S` is a base of `N` if and only if
  `fst S` is a base of `M₁` and `E \ snd S` is a base of `M₂`.
* `doubling` (Lemma `lem:doubling`): `lift X` is a base of `N` if and only if `X` is a common
  base of `M₁` and `M₂`, and its weight is `w(X)`.
* `rk_pair`, `rk_add_rank`, `rk_pair_eq_sub` (Theorem `thm:D`, Step 2):
  `r_N(A × {1} ∪ B × {2}) = r₁(A) + |B| + r₂(E \ B) - r₂(E)`.
* `rank_double`, `rank_double_eq` (Theorem `thm:D`, Step 1): `r_N + r₂(E) = r₁(E) + m`, so `N`
  has rank `m` when `M₁` and `M₂` have equal rank, in particular when they have a common base
  (`rank_eq_rank_of_isBase`).
* `eq_lift_of_isRainbowBase`, `isRainbowBase_iff`, `exists_isRainbowBase_iff`, `opt_eq`: when
  `M₁` and `M₂` have equal rank, every rainbow base of `N` is `lift X` for a common base `X`,
  and `Opt` of `N` at `weight w` is the least weight of a common base.
-/

open Finset

namespace SignedTropical.Rainbow.Doubling

variable {m : ℕ}

/-! ### The doubled ground set -/

/-- The block of `(e, 1)` and of `(e, 2)` is `e`. -/
def blk (m : ℕ) : Fin (m + m) → Fin m :=
  Fin.addCases (motive := fun _ => Fin m) id id

/-- The weight `w_e` on `(e, 1)` and `0` on `(e, 2)`. -/
def weight (w : Fin m → ℝ) : Fin (m + m) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) w fun _ => 0

@[simp] theorem blk_castAdd (e : Fin m) : blk m (Fin.castAdd m e) = e := by
  simp only [blk, Fin.addCases_left, id]

@[simp] theorem blk_addNat (e : Fin m) : blk m (Fin.addNat e m) = e := by
  rw [← Fin.natAdd_eq_addNat]
  simp only [blk, Fin.addCases_right, id]

@[simp] theorem weight_castAdd (w : Fin m → ℝ) (e : Fin m) :
    weight w (Fin.castAdd m e) = w e := by
  simp only [weight, Fin.addCases_left]

@[simp] theorem weight_addNat (w : Fin m → ℝ) (e : Fin m) : weight w (Fin.addNat e m) = 0 := by
  rw [← Fin.natAdd_eq_addNat]
  simp only [weight, Fin.addCases_right]

theorem castAdd_ne_addNat (e f : Fin m) : Fin.castAdd m e ≠ Fin.addNat f m := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_addNat]
  omega

@[simp] theorem castAdd_eq_addNat_iff (e f : Fin m) : Fin.castAdd m e = Fin.addNat f m ↔ False :=
  iff_false_intro (castAdd_ne_addNat e f)

@[simp] theorem addNat_eq_castAdd_iff (e f : Fin m) : Fin.addNat f m = Fin.castAdd m e ↔ False :=
  iff_false_intro (castAdd_ne_addNat e f).symm

/-- `A × {1} ∪ B × {2}`. -/
def pair (A B : Finset (Fin m)) : Finset (Fin (m + m)) :=
  A.map (Fin.castAddEmb m) ∪ B.map (Fin.addNatEmb m)

/-- `{e : (e, 1) ∈ S}`. -/
def fst (S : Finset (Fin (m + m))) : Finset (Fin m) :=
  univ.filter fun e => Fin.castAdd m e ∈ S

/-- `{e : (e, 2) ∈ S}`. -/
def snd (S : Finset (Fin (m + m))) : Finset (Fin m) :=
  univ.filter fun e => Fin.addNat e m ∈ S

/-- `X × {1} ∪ (E \ X) × {2}`: the set that chooses the copy `(e, 1)` exactly for `e ∈ X` and
the copy `(e, 2)` otherwise. -/
def lift (X : Finset (Fin m)) : Finset (Fin (m + m)) :=
  pair X (univ \ X)

variable {A B X : Finset (Fin m)} {S : Finset (Fin (m + m))} {e : Fin m}

@[simp] theorem castAdd_mem_pair : Fin.castAdd m e ∈ pair A B ↔ e ∈ A := by
  simp [pair]

@[simp] theorem addNat_mem_pair : Fin.addNat e m ∈ pair A B ↔ e ∈ B := by
  simp [pair]

@[simp] theorem mem_fst : e ∈ fst S ↔ Fin.castAdd m e ∈ S := by
  simp [fst]

@[simp] theorem mem_snd : e ∈ snd S ↔ Fin.addNat e m ∈ S := by
  simp [snd]

@[simp] theorem castAdd_mem_lift : Fin.castAdd m e ∈ lift X ↔ e ∈ X := by
  simp [lift]

@[simp] theorem addNat_mem_lift : Fin.addNat e m ∈ lift X ↔ e ∉ X := by
  simp [lift]

@[simp] theorem fst_pair (A B : Finset (Fin m)) : fst (pair A B) = A := by
  ext e
  simp

@[simp] theorem snd_pair (A B : Finset (Fin m)) : snd (pair A B) = B := by
  ext e
  simp

@[simp] theorem fst_lift (X : Finset (Fin m)) : fst (lift X) = X :=
  fst_pair _ _

theorem pair_fst_snd (S : Finset (Fin (m + m))) : pair (fst S) (snd S) = S := by
  ext x
  induction x using Fin.addCases <;> simp

theorem disjoint_pair (A B : Finset (Fin m)) :
    Disjoint (A.map (Fin.castAddEmb m)) (B.map (Fin.addNatEmb m)) := by
  refine disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨a, -, rfl⟩ := mem_map.1 hx
  obtain ⟨b, -, h⟩ := mem_map.1 hx'
  exact castAdd_ne_addNat a b (by simpa using h.symm)

theorem card_pair (A B : Finset (Fin m)) : #(pair A B) = #A + #B := by
  rw [pair, card_union_of_disjoint (disjoint_pair A B), card_map, card_map]

theorem card_lift (X : Finset (Fin m)) : #(lift X) = m := by
  rw [lift, card_pair, ← compl_eq_univ_sdiff, card_add_card_compl, Fintype.card_fin]

theorem pair_univ_univ : pair (univ : Finset (Fin m)) univ = univ :=
  eq_univ_of_card _ (by rw [card_pair, card_univ, Fintype.card_fin, Fintype.card_fin])

@[simp] theorem preimage_castAdd_pair (A B : Finset (Fin m)) :
    Fin.castAdd m ⁻¹' (pair A B : Set (Fin (m + m))) = A := by
  ext e
  simp

@[simp] theorem preimage_addNat_pair (A B : Finset (Fin m)) :
    (Fin.addNat · m) ⁻¹' (pair A B : Set (Fin (m + m))) = B := by
  ext e
  simp

theorem coe_fst (S : Finset (Fin (m + m))) :
    (fst S : Set (Fin m)) = Fin.castAdd m ⁻¹' (S : Set (Fin (m + m))) := by
  ext e
  simp

theorem coe_snd (S : Finset (Fin (m + m))) :
    (snd S : Set (Fin m)) = (Fin.addNat · m) ⁻¹' (S : Set (Fin (m + m))) := by
  ext e
  simp

/-- `lift X` meets every block at most once. -/
theorem isRainbow_lift (X : Finset (Fin m)) : IsRainbow (blk m) (lift X) := by
  intro x hx y hy hxy
  induction x using Fin.addCases <;> induction y using Fin.addCases <;> simp_all

/-- `lift X` meets every block. -/
theorem blocksMet_lift (X : Finset (Fin m)) : blocksMet (blk m) (lift X) = univ := by
  refine eq_univ_of_forall fun e => mem_image.2 ?_
  by_cases he : e ∈ X
  · exact ⟨Fin.castAdd m e, castAdd_mem_lift.2 he, blk_castAdd e⟩
  · exact ⟨Fin.addNat e m, addNat_mem_lift.2 he, blk_addNat e⟩

/-- The sets that meet every block exactly once and choose the copy `(e, 1)` exactly for
`e ∈ X` are the set `lift X = X × {1} ∪ (E \ X) × {2}`. -/
theorem isTransversal_iff :
    (IsRainbow (blk m) S ∧ blocksMet (blk m) S = univ ∧ fst S = X) ↔ S = lift X := by
  refine ⟨fun ⟨hS, hmet, hX⟩ => ?_, fun h => h ▸ ⟨isRainbow_lift X, blocksMet_lift X, fst_lift X⟩⟩
  subst hX
  ext x
  induction x using Fin.addCases with
  | left e => simp
  | right e =>
    rw [Fin.natAdd_eq_addNat, addNat_mem_lift, mem_fst]
    refine ⟨fun h h' => castAdd_ne_addNat e e (hS h' h (by simp)), fun h => ?_⟩
    obtain ⟨y, hy, hye⟩ := mem_image.1 (hmet ▸ mem_univ e : e ∈ blocksMet (blk m) S)
    induction y using Fin.addCases with
    | left f =>
      rw [blk_castAdd] at hye
      exact absurd (hye ▸ hy) h
    | right f =>
      rw [Fin.natAdd_eq_addNat, blk_addNat] at hye
      rw [Fin.natAdd_eq_addNat, hye] at hy
      exact hy

/-! ### The doubled matroid -/

section Matroid

variable {M₁ M₂ : Matroid (Fin m)}

/-- `N = M₁ ⊕ M₂✶` on `E × {1, 2} = Fin (m + m)`. -/
def double (M₁ M₂ : Matroid (Fin m)) : Matroid (Fin (m + m)) :=
  (M₁.sum M₂✶).mapEquiv finSumFinEquiv

/-- The ground set of `N` is `E × {1, 2}`. -/
theorem double_ground (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) :
    (double M₁ M₂).E = Set.univ := by
  simp [double, hE₁, hE₂, Set.image_univ, Set.range_inl_union_range_inr]

theorem preimage_inl_image_symm (S : Set (Fin (m + m))) :
    Sum.inl ⁻¹' (finSumFinEquiv.symm '' S) = Fin.castAdd m ⁻¹' S := by
  ext e
  simp [Equiv.image_symm_eq_preimage]

theorem preimage_inr_image_symm (S : Set (Fin (m + m))) :
    Sum.inr ⁻¹' (finSumFinEquiv.symm '' S) = (Fin.addNat · m) ⁻¹' S := by
  ext e
  simp [Equiv.image_symm_eq_preimage]

/-- `I` is a basis of `X` in `N` if and only if its first copies form a basis of the first
copies of `X` in `M₁` and its second copies a basis of the second copies of `X` in `M₂✶`. -/
theorem isBasis_iff {I X : Set (Fin (m + m))} : (double M₁ M₂).IsBasis I X ↔
    M₁.IsBasis (Fin.castAdd m ⁻¹' I) (Fin.castAdd m ⁻¹' X) ∧
      M₂✶.IsBasis ((Fin.addNat · m) ⁻¹' I) ((Fin.addNat · m) ⁻¹' X) := by
  rw [double, Matroid.mapEquiv_isBasis_iff, Matroid.sum_isBasis_iff, preimage_inl_image_symm,
    preimage_inl_image_symm, preimage_inr_image_symm, preimage_inr_image_symm]

/-- `B` is a base of `N` if and only if its first copies form a base of `M₁` and its second
copies a base of `M₂✶`. -/
theorem isBase_iff {B : Set (Fin (m + m))} : (double M₁ M₂).IsBase B ↔
    M₁.IsBase (Fin.castAdd m ⁻¹' B) ∧ M₂✶.IsBase ((Fin.addNat · m) ⁻¹' B) := by
  rw [double, Matroid.mapEquiv_isBase_iff, Matroid.sum_isBase_iff, preimage_inl_image_symm,
    preimage_inr_image_symm]

/-- `S` is a base of `N` if and only if its first copies form a base of `M₁` and the elements
whose second copy is not in `S` form a base of `M₂`. -/
theorem isBase_iff_fst_snd (hE₂ : M₂.E = Set.univ) (S : Finset (Fin (m + m))) :
    (double M₁ M₂).IsBase (S : Set (Fin (m + m))) ↔
      M₁.IsBase (fst S : Set (Fin m)) ∧
        M₂.IsBase ((univ \ snd S : Finset (Fin m)) : Set (Fin m)) := by
  rw [isBase_iff, ← coe_fst, ← coe_snd, Matroid.dual_isBase_iff', hE₂, coe_sdiff, coe_univ]
  simp

/-- `lift X` is a base of `N` if and only if `X` is a common base of `M₁` and `M₂`. -/
theorem isBase_lift_iff (hE₂ : M₂.E = Set.univ) (X : Finset (Fin m)) :
    (double M₁ M₂).IsBase (lift X : Set (Fin (m + m))) ↔
      M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)) := by
  rw [isBase_iff, lift, preimage_castAdd_pair, preimage_addNat_pair, Matroid.dual_isBase_iff', hE₂]
  simp

/-- The weight of `lift X` is `w(X)`. -/
theorem sum_weight_lift (w : Fin m → ℝ) (X : Finset (Fin m)) :
    ∑ x ∈ lift X, weight w x = ∑ e ∈ X, w e := by
  rw [lift, pair, sum_union (disjoint_pair X _), sum_map, sum_map]
  simp

/-- Lemma `lem:doubling`: on `E × {1, 2}` let `N = M₁ ⊕ M₂✶`, with blocks `{(e, 1), (e, 2)}` and
weight `w_e` on `(e, 1)` and `0` on `(e, 2)`.  The set `X × {1} ∪ (E \ X) × {2}`, which meets
every block once and chooses the copy `(e, 1)` exactly for `e ∈ X` (`isTransversal_iff`), is a
base of `N` if and only if `X` is a common base of `M₁` and `M₂`, and its weight is `w(X)`. -/
theorem doubling (hE₂ : M₂.E = Set.univ) (w : Fin m → ℝ) (X : Finset (Fin m)) :
    ((double M₁ M₂).IsBase (lift X : Set (Fin (m + m))) ↔
      M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m))) ∧
      ∑ x ∈ lift X, weight w x = ∑ e ∈ X, w e :=
  ⟨isBase_lift_iff hE₂ X, sum_weight_lift w X⟩

/-! ### Rank -/

/-- `r₂*(B) + r₂(E) = r₂(E \ B) + |B|`. -/
theorem rk_dual_add_rank (hE₂ : M₂.E = Set.univ) (B : Finset (Fin m)) :
    rk M₂✶ B + rank M₂ = rk M₂ (univ \ B) + #B := by
  have h := M₂.eRk_dual_add_eRank (B : Set (Fin m)) (by rw [hE₂]; exact Set.subset_univ _)
  rw [hE₂, ← coe_univ, ← coe_sdiff, ← coe_rk, ← coe_rk, ← ENat.coe_toNat (eRank_ne_top M₂),
    Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- `r_N(A × {1} ∪ B × {2}) = r₁(A) + r₂*(B)`. -/
theorem rk_pair_eq_add (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) (A B : Finset (Fin m)) :
    rk (double M₁ M₂) (pair A B) = rk M₁ A + rk M₂✶ B := by
  obtain ⟨I₀, hI⟩ := M₁.exists_isBasis (A : Set (Fin m)) (by rw [hE₁]; exact Set.subset_univ _)
  obtain ⟨J₀, hJ⟩ := M₂✶.exists_isBasis (B : Set (Fin m))
    (by rw [Matroid.dual_ground, hE₂]; exact Set.subset_univ _)
  obtain ⟨I, rfl⟩ := exists_finset I₀
  obtain ⟨J, rfl⟩ := exists_finset J₀
  have hIJ : (double M₁ M₂).IsBasis (pair I J : Set (Fin (m + m))) (pair A B) := by
    rw [isBasis_iff, preimage_castAdd_pair, preimage_castAdd_pair, preimage_addNat_pair,
      preimage_addNat_pair]
    exact ⟨hI, hJ⟩
  rw [← card_eq_rk _ hIJ, ← card_eq_rk _ hI, ← card_eq_rk _ hJ, card_pair]

/-- Theorem `thm:D`, Step 2: `r_N(A × {1} ∪ B × {2}) + r₂(E) = r₁(A) + |B| + r₂(E \ B)`. -/
theorem rk_pair (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) (A B : Finset (Fin m)) :
    rk (double M₁ M₂) (pair A B) + rank M₂ = rk M₁ A + #B + rk M₂ (univ \ B) := by
  have h := rk_dual_add_rank hE₂ B
  rw [rk_pair_eq_add hE₁ hE₂]
  omega

/-- Theorem `thm:D`, Step 2, with the subtraction:
`r_N(A × {1} ∪ B × {2}) = r₁(A) + |B| + r₂(E \ B) - r₂(E)`, where `r₂(E) ≤ r₁(A) + |B| + r₂(E \ B)`
by `rk_pair`. -/
theorem rk_pair_eq_sub (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) (A B : Finset (Fin m)) :
    rk (double M₁ M₂) (pair A B) = rk M₁ A + #B + rk M₂ (univ \ B) - rank M₂ := by
  have h := rk_pair hE₁ hE₂ A B
  omega

/-- Theorem `thm:D`, Step 2, for an arbitrary set `S = fst S × {1} ∪ snd S × {2}`. -/
theorem rk_add_rank (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) (S : Finset (Fin (m + m))) :
    rk (double M₁ M₂) S + rank M₂ = rk M₁ (fst S) + #(snd S) + rk M₂ (univ \ snd S) := by
  conv_lhs => rw [← pair_fst_snd S]
  exact rk_pair hE₁ hE₂ _ _

/-- Theorem `thm:D`, Step 1: `r_N(E × {1, 2}) + r₂(E) = r₁(E) + m`. -/
theorem rank_double (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) :
    rank (double M₁ M₂) + rank M₂ = rank M₁ + m := by
  have h := rk_pair hE₁ hE₂ univ univ
  rwa [pair_univ_univ, rk_univ _ (double_ground hE₁ hE₂), rk_univ _ hE₁, card_univ,
    Fintype.card_fin, Finset.sdiff_self, show rk M₂ ∅ = 0 by simp [rk], add_zero] at h

/-- Matroids with a common base have equal rank. -/
theorem rank_eq_rank_of_isBase {X : Finset (Fin m)} (h₁ : M₁.IsBase (X : Set (Fin m)))
    (h₂ : M₂.IsBase (X : Set (Fin m))) : rank M₁ = rank M₂ :=
  (card_base M₁ h₁).symm.trans (card_base M₂ h₂)

/-- Theorem `thm:D`, Step 1: if `M₁` and `M₂` have equal rank, for instance a common base
(`rank_eq_rank_of_isBase`), then `N` has rank `m`. -/
theorem rank_double_eq (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hrank : rank M₁ = rank M₂) : rank (double M₁ M₂) = m := by
  have h := rank_double hE₁ hE₂
  omega

/-! ### Rainbow bases of `N` -/

/-- If `M₁` and `M₂` have equal rank, every rainbow base of `N` is `lift X` for `X` the set of
its first copies. -/
theorem eq_lift_of_isRainbowBase (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hrank : rank M₁ = rank M₂) {S : Finset (Fin (m + m))}
    (hS : IsRainbowBase (double M₁ M₂) (blk m) S) : S = lift (fst S) := by
  refine isTransversal_iff.1 ⟨hS.2, eq_univ_of_card _ ?_, rfl⟩
  rw [blocksMet, card_image_of_injOn hS.2, card_base _ hS.1, rank_double_eq hE₁ hE₂ hrank,
    Fintype.card_fin]

/-- If `M₁` and `M₂` have equal rank, the rainbow bases of `N` are the sets `lift X` for the
common bases `X` of `M₁` and `M₂`. -/
theorem isRainbowBase_iff (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hrank : rank M₁ = rank M₂) {S : Finset (Fin (m + m))} :
    IsRainbowBase (double M₁ M₂) (blk m) S ↔
      ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)) ∧
        S = lift X := by
  refine ⟨fun hS => ⟨fst S, ?_⟩, fun ⟨X, h₁, h₂, hS⟩ => hS ▸ ⟨(isBase_lift_iff hE₂ X).2 ⟨h₁, h₂⟩,
    isRainbow_lift X⟩⟩
  have h := eq_lift_of_isRainbowBase hE₁ hE₂ hrank hS
  exact ⟨((isBase_lift_iff hE₂ _).1 (h ▸ hS.1)).1, ((isBase_lift_iff hE₂ _).1 (h ▸ hS.1)).2, h⟩

/-- If `M₁` and `M₂` have equal rank, `N` has a rainbow base if and only if `M₁` and `M₂` have a
common base. -/
theorem exists_isRainbowBase_iff (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hrank : rank M₁ = rank M₂) :
    (∃ S, IsRainbowBase (double M₁ M₂) (blk m) S) ↔
      ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)) := by
  simp only [isRainbowBase_iff hE₁ hE₂ hrank]
  exact ⟨fun ⟨_, X, h₁, h₂, _⟩ => ⟨X, h₁, h₂⟩, fun ⟨X, h₁, h₂⟩ => ⟨lift X, X, h₁, h₂, rfl⟩⟩

/-- If `M₁` and `M₂` have equal rank, `Opt` of `N` at the weight `weight w` is the least weight
`w(X)` of a common base `X` of `M₁` and `M₂`. -/
theorem opt_eq (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) (hrank : rank M₁ = rank M₂)
    (w : Fin m → ℝ) : Opt (double M₁ M₂) (blk m) (weight w) =
      sInf {x | ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧
        M₂.IsBase (X : Set (Fin m)) ∧ x = ∑ e ∈ X, w e} := by
  rw [Opt]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, isRainbowBase_iff hE₁ hE₂ hrank]
  constructor
  · rintro ⟨S, ⟨X, h₁, h₂, rfl⟩, rfl⟩
    exact ⟨X, h₁, h₂, sum_weight_lift w X⟩
  · rintro ⟨X, h₁, h₂, rfl⟩
    exact ⟨lift X, ⟨X, h₁, h₂, rfl⟩, (sum_weight_lift w X).symm⟩

end Matroid

end SignedTropical.Rainbow.Doubling
