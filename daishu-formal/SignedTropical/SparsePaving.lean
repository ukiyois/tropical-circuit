import SignedTropical.Counting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sparse paving matroids and the number of matroids

`greedy_intersection.tex`, Corollary `cor:count`, Step 1: a lower bound on the number of
matroids on `m` labeled elements.  The paper cites Knuth (1974); the weaker bound proved here
suffices for the corollary (`Asymptotic.lean`).

* **Sparse paving matroids** (`exists_matroid`, `matroid`).  Let `0 < r < m` and let `H` be a
  family of subsets of `Fin m`, two distinct members of which share at most `r - 2` elements
  (`IsSparse r H`).  The `r`-subsets of `Fin m` not in `H` are the bases of a matroid with
  ground set `univ`.  Base exchange: if `B₁ - e + f₁` and `B₁ - e + f₂` were both in `H`, they
  would share the `r - 1` elements of `B₁ - e`.
* **The family of Graham and Sloane** (`gsFamily`, `isSparse_gsFamily`, `exists_le_card_gsFamily`):
  the `r`-subsets `X` of `Fin m` with `∑_{x ∈ X} x ≡ c (mod m)` pairwise share at most `r - 2`
  elements, and for some `c < m` there are at least `C(m, r)/m` of them.
* **The number of matroids** (`two_pow_card_le_ncard_matroids`,
  `two_pow_ceil_le_ncard_matroids`, `rpow_le_ncard_matroids`).  Distinct subfamilies of a sparse
  family of `r`-subsets give distinct matroids, so there are at least
  `2^{⌈C(m,⌊m/2⌋)/m⌉} ≥ 2^{2^m/(m(m+1))}` matroids on `Fin m` with ground set `univ`; here
  `C(m, ⌊m/2⌋) ≥ 2^m/(m+1)` (`two_pow_le_succ_mul_choose_half`).  The construction needs
  `m ≥ 2`; at `m = 0` and `m = 1` the first bound is `1` and `2`, met by the free and the loopy
  matroid.  The first bound is a natural number, so it can be passed as `N` to `corollaryD`.
-/

open Finset

namespace SignedTropical.SparsePaving

variable {m r : ℕ} {H : Finset (Finset (Fin m))}

/-! ### Sparse paving matroids -/

/-- Two distinct members of `H` share at most `r - 2` elements: `|X ∩ Y| + 2 ≤ r`. -/
def IsSparse (r : ℕ) (H : Finset (Finset (Fin m))) : Prop :=
  ∀ X ∈ H, ∀ Y ∈ H, X ≠ Y → #(X ∩ Y) + 2 ≤ r

theorem IsSparse.mono {H' : Finset (Finset (Fin m))} (h : IsSparse r H) (hH' : H' ⊆ H) :
    IsSparse r H' :=
  fun X hX Y hY => h X (hH' hX) Y (hH' hY)

/-- Two members of a sparse family that contain a common set of `r - 1` elements are equal. -/
theorem IsSparse.eq_of_subset_inter (h : IsSparse r H) {X Y W : Finset (Fin m)} (hX : X ∈ H)
    (hY : Y ∈ H) (hW : W ⊆ X ∩ Y) (hWr : #W + 1 = r) : X = Y := by
  by_contra hne
  have h₁ := h X hX Y hY hne
  have h₂ := card_le_card hW
  omega

/-- Base exchange for the `r`-subsets not in a sparse family. -/
theorem exchangeProperty (hH : IsSparse r H) :
    Matroid.ExchangeProperty fun B : Set (Fin m) =>
      ∃ X : Finset (Fin m), #X = r ∧ X ∉ H ∧ (X : Set (Fin m)) = B := by
  rintro _ _ ⟨X, hXr, hXH, rfl⟩ ⟨Y, hYr, hYH, rfl⟩ a ⟨haX, haY⟩
  rw [mem_coe] at haX haY
  have hW : #(X.erase a) + 1 = r := by
    rw [card_erase_of_mem haX]
    have := card_pos.2 ⟨a, haX⟩
    omega
  have hZ : ∀ b ∉ X, #(insert b (X.erase a)) = r := fun b hb => by
    rw [card_insert_of_notMem fun h => hb (mem_of_mem_erase h), hW]
  suffices ∃ b ∈ Y, b ∉ X ∧ insert b (X.erase a) ∉ H by
    obtain ⟨b, hbY, hbX, hbH⟩ := this
    exact ⟨b, ⟨hbY, hbX⟩, _, hZ b hbX, hbH, by rw [coe_insert, coe_erase]⟩
  -- some `b ∈ Y \ X`; if `X - a + b ∈ H`, a second `b' ∈ Y \ X` exists and `X - a + b' ∉ H`
  obtain ⟨b, hbY, hbX⟩ := not_subset.1 fun hYX : Y ⊆ X =>
    haY (by rw [eq_of_subset_of_card_le hYX (by omega)]; exact haX)
  by_cases hb : insert b (X.erase a) ∈ H
  swap
  · exact ⟨b, hbY, hbX, hb⟩
  obtain ⟨b', hb'Y, hb'Z⟩ := not_subset.1 fun hYZ : Y ⊆ insert b (X.erase a) =>
    hYH (by rw [eq_of_subset_of_card_le hYZ (by rw [hZ b hbX, hYr])]; exact hb)
  have hb'X : b' ∉ X := fun h =>
    hb'Z (mem_insert_of_mem (mem_erase.2 ⟨fun h' => haY (h' ▸ hb'Y), h⟩))
  refine ⟨b', hb'Y, hb'X, fun hb' => ?_⟩
  have heq := hH.eq_of_subset_inter hb hb'
    (subset_inter (subset_insert _ _) (subset_insert _ _)) hW
  rcases mem_insert.1 (heq ▸ mem_insert_self b (X.erase a)) with h | h
  · exact hb'Z (h ▸ mem_insert_self b _)
  · exact hbX (mem_of_mem_erase h)

/-- The sparse paving matroid on `Fin m` whose bases are the `r`-subsets not in `H`; it needs
`H` sparse and some `r`-subset outside `H`. -/
def matroid (r : ℕ) (H : Finset (Finset (Fin m))) (hH : IsSparse r H)
    (hne : ∃ X : Finset (Fin m), #X = r ∧ X ∉ H) : Matroid (Fin m) :=
  Matroid.ofIsBaseOfFinite Set.finite_univ
    (fun B => ∃ X : Finset (Fin m), #X = r ∧ X ∉ H ∧ (X : Set (Fin m)) = B)
    (hne.elim fun X hX => ⟨X, X, hX.1, hX.2, rfl⟩) (exchangeProperty hH)
    fun _ _ => Set.subset_univ _

@[simp] theorem matroid_E (hH : IsSparse r H) (hne : ∃ X : Finset (Fin m), #X = r ∧ X ∉ H) :
    (matroid r H hH hne).E = Set.univ := rfl

/-- The bases of `matroid r H` are the `r`-subsets not in `H`. -/
theorem isBase_matroid_iff (hH : IsSparse r H) (hne : ∃ X : Finset (Fin m), #X = r ∧ X ∉ H)
    (B : Finset (Fin m)) : (matroid r H hH hne).IsBase (B : Set (Fin m)) ↔ #B = r ∧ B ∉ H := by
  simp only [matroid, Matroid.ofIsBaseOfFinite_isBase, coe_inj]
  exact ⟨fun ⟨X, hXr, hXH, hXB⟩ => hXB ▸ ⟨hXr, hXH⟩, fun h => ⟨B, h.1, h.2, rfl⟩⟩

/-- For `0 < r < m`, some `r`-subset is not in a sparse family `H`. -/
theorem exists_card_eq_notMem (hr : 0 < r) (hrm : r < m) (hH : IsSparse r H) :
    ∃ X : Finset (Fin m), #X = r ∧ X ∉ H := by
  obtain ⟨X, -, hX⟩ := exists_subset_card_eq (s := (univ : Finset (Fin m))) (n := r)
    (by simp; omega)
  by_cases hXH : X ∈ H
  swap
  · exact ⟨X, hX, hXH⟩
  obtain ⟨a, haX⟩ := card_pos.1 (hX ▸ hr)
  obtain ⟨b, -, hbX⟩ := exists_mem_notMem_of_card_lt_card (s := X) (t := univ) (by simp; omega)
  have hW : #(X.erase a) + 1 = r := by rw [card_erase_of_mem haX]; omega
  refine ⟨insert b (X.erase a), by rw [card_insert_of_notMem fun h => hbX (mem_of_mem_erase h),
    hW], fun hZ => hbX ?_⟩
  rw [hH.eq_of_subset_inter hXH hZ (subset_inter (erase_subset a X) (subset_insert _ _)) hW]
  exact mem_insert_self b _

/-- **Sparse paving matroids** (`cor:count`, Step 1).  Let `0 < r < m` and let `H` be a family
of subsets of `Fin m`, two distinct members of which share at most `r - 2` elements.  The
`r`-subsets of `Fin m` not in `H` are the bases of a matroid on `Fin m` with ground set
`univ`. -/
theorem exists_matroid (hr : 0 < r) (hrm : r < m) (hH : IsSparse r H) :
    ∃ M : Matroid (Fin m), M.E = Set.univ ∧
      ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ↔ #B = r ∧ B ∉ H :=
  ⟨_, matroid_E hH (exists_card_eq_notMem hr hrm hH), isBase_matroid_iff hH _⟩

/-- **Distinct subfamilies give distinct matroids** (`cor:count`, Step 1).  For `0 < r < m` and
a sparse family `A` of `r`-subsets of `Fin m`, there are at least `2^{|A|}` matroids on `Fin m`
with ground set `univ`. -/
theorem two_pow_card_le_ncard_matroids (hr : 0 < r) (hrm : r < m)
    {A : Finset (Finset (Fin m))} (hA : IsSparse r A) (hAr : ∀ X ∈ A, #X = r) :
    2 ^ #A ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  have hA' : ∀ H : Finset (Finset (Fin m)), IsSparse r (H ∩ A) :=
    fun H => hA.mono inter_subset_right
  let f : Finset (Finset (Fin m)) → Matroid (Fin m) := fun H =>
    matroid r (H ∩ A) (hA' H) (exists_card_eq_notMem hr hrm (hA' H))
  have hinj : Set.InjOn f (A.powerset : Set (Finset (Finset (Fin m)))) := by
    intro H hH H' hH' h
    rw [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hH hH'
    have hiff : ∀ X ∈ A, X ∈ H ↔ X ∈ H' := fun X hX => by
      have := congrArg (fun M : Matroid (Fin m) => M.IsBase (X : Set (Fin m))) h
      simpa [f, isBase_matroid_iff, hAr X hX, hX, not_iff_not] using this
    ext X
    exact ⟨fun hX => (hiff X (hH hX)).1 hX, fun hX => (hiff X (hH' hX)).2 hX⟩
  calc 2 ^ #A = (A.powerset : Set (Finset (Finset (Fin m)))).ncard := by
        rw [Set.ncard_coe_finset, card_powerset]
    _ ≤ _ := Set.ncard_le_ncard_of_injOn f (fun H _ => matroid_E _ _) hinj finite_matroids

/-! ### The family of Graham and Sloane -/

/-- The family of Graham and Sloane: the `r`-subsets of `Fin m` whose elements sum to `c`
modulo `m`. -/
def gsFamily (m r c : ℕ) : Finset (Finset (Fin m)) :=
  {X ∈ univ.powersetCard r | (∑ x ∈ X, (x : ℕ)) % m = c}

theorem card_of_mem_gsFamily {c : ℕ} {X : Finset (Fin m)} (hX : X ∈ gsFamily m r c) :
    #X = r :=
  (mem_powersetCard.1 (mem_filter.1 hX).1).2

/-- **Graham and Sloane, sparseness** (`cor:count`, Step 1).  Two distinct sets of the family share
at most `r - 2` elements. -/
theorem isSparse_gsFamily (m r c : ℕ) : IsSparse r (gsFamily m r c) := by
  intro X hX Y hY hne
  have hXr := card_of_mem_gsFamily hX
  have hYr := card_of_mem_gsFamily hY
  by_contra! hlt
  -- `X \ Y = {a}` and `Y \ X = {b}`
  have hXY := card_sdiff_add_card_inter X Y
  have hYX := card_sdiff_add_card_inter Y X
  rw [inter_comm] at hYX
  have hpos := card_pos.2 (sdiff_nonempty.2 fun h => hne (eq_of_subset_of_card_le h (by omega)))
  obtain ⟨a, ha⟩ := card_eq_one.1 (show #(X \ Y) = 1 by omega)
  obtain ⟨b, hb⟩ := card_eq_one.1 (show #(Y \ X) = 1 by omega)
  -- the sums of `X` and `Y` differ by `a - b`, so `a ≡ b (mod m)` and `a = b`
  have hsX := sum_inter_add_sum_sdiff X Y fun x : Fin m => (x : ℕ)
  have hsY := sum_inter_add_sum_sdiff Y X fun x : Fin m => (x : ℕ)
  rw [ha, sum_singleton] at hsX
  rw [hb, sum_singleton, inter_comm] at hsY
  have hab := (Nat.ModEq.add_left_cancel' _ (by
    rw [Nat.ModEq, hsX, hsY, (mem_filter.1 hX).2, (mem_filter.1 hY).2])).eq_of_lt_of_lt
    a.isLt b.isLt
  have ha' : a ∈ X \ Y := ha ▸ mem_singleton_self a
  have hb' : b ∈ Y \ X := hb ▸ mem_singleton_self b
  exact (mem_sdiff.1 ha').2 (Fin.ext hab ▸ (mem_sdiff.1 hb').1)

/-- **Graham and Sloane, size** (`cor:count`, Step 1).  For `m > 0`, some residue `c < m` has at
least `C(m, r)/m` sets in its family. -/
theorem exists_le_card_gsFamily (hm : 0 < m) (r : ℕ) :
    ∃ c < m, (m.choose r : ℝ) / m ≤ #(gsFamily m r c) := by
  obtain ⟨c, hc, h⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := (univ : Finset (Fin m)).powersetCard r) (t := range m)
    (f := fun X => (∑ x ∈ X, (x : ℕ)) % m) (b := (m.choose r : ℝ) / m)
    (fun X _ => mem_range.2 (Nat.mod_lt _ hm)) (nonempty_range_iff.2 hm.ne') (by
      rw [card_range, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (by exact_mod_cast hm.ne')])
  exact ⟨c, mem_range.1 hc, h⟩

/-! ### The number of matroids -/

/-- `C(m, ⌊m/2⌋) ≥ 2^m/(m+1)`. -/
theorem two_pow_le_succ_mul_choose_half (m : ℕ) : 2 ^ m ≤ (m + 1) * m.choose (m / 2) :=
  calc 2 ^ m = ∑ k ∈ range (m + 1), m.choose k := (Nat.sum_range_choose m).symm
    _ ≤ ∑ _k ∈ range (m + 1), m.choose (m / 2) := sum_le_sum fun k _ => Nat.choose_le_middle k m
    _ = (m + 1) * m.choose (m / 2) := by rw [sum_const, card_range, smul_eq_mul]

/-- There is a matroid on `Fin m` with ground set `univ`. -/
theorem ncard_matroids_pos : 0 < Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} :=
  (Set.ncard_pos finite_matroids).2 ⟨Matroid.freeOn Set.univ, Matroid.freeOn_ground⟩

/-- For `0 < r < m` there are at least `2^{⌈C(m,r)/m⌉}` matroids on `Fin m` with ground set
`univ`. -/
theorem two_pow_ceil_choose_le_ncard_matroids (hr : 0 < r) (hrm : r < m) :
    2 ^ ⌈(m.choose r : ℝ) / m⌉₊ ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  obtain ⟨c, -, hc⟩ := exists_le_card_gsFamily (by omega : 0 < m) r
  exact (Nat.pow_le_pow_right two_pos (Nat.ceil_le.2 hc)).trans
    (two_pow_card_le_ncard_matroids hr hrm (isSparse_gsFamily m r c)
      fun _ => card_of_mem_gsFamily)

/-- **The number of matroids** (`cor:count`, Step 1).  There are at least `2^{⌈C(m,⌊m/2⌋)/m⌉}`
matroids on `Fin m` with ground set `univ`.  As a natural number, this bound can be passed as
`N` to `corollaryD`. -/
theorem two_pow_ceil_le_ncard_matroids (m : ℕ) :
    2 ^ ⌈(m.choose (m / 2) : ℝ) / m⌉₊ ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | hm
  · simpa using Nat.succ_le_of_lt (ncard_matroids_pos (m := 0))
  · -- the free and the loopy matroid on `Fin 1` are distinct
    have hne : Matroid.freeOn (Set.univ : Set (Fin 1)) ≠ Matroid.loopyOn Set.univ := fun h => by
      simpa using congrArg (fun M : Matroid (Fin 1) => M.Indep {0}) h
    have h := Set.ncard_le_ncard (s := {Matroid.freeOn Set.univ, Matroid.loopyOn Set.univ})
      (t := {M : Matroid (Fin 1) | M.E = Set.univ}) (by simp [Set.insert_subset_iff])
      finite_matroids
    simpa [Set.ncard_pair hne] using h
  · exact two_pow_ceil_choose_le_ncard_matroids (by omega) (by omega)

/-- **The number of matroids, closed form** (`cor:count`, Step 1).  There are at least
`2^{2^m/(m(m+1))}` matroids on `Fin m` with ground set `univ`. -/
theorem rpow_le_ncard_matroids (m : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ m / (m * (m + 1))) ≤
      Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  have hC : (2 : ℝ) ^ m / (m * (m + 1)) ≤ (m.choose (m / 2) : ℝ) / m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hm)]
    have : ((2 ^ m : ℕ) : ℝ) ≤ ((m + 1) * m.choose (m / 2) : ℕ) := by
      exact_mod_cast two_pow_le_succ_mul_choose_half m
    push_cast at this
    nlinarith
  calc (2 : ℝ) ^ ((2 : ℝ) ^ m / (m * (m + 1)))
      ≤ (2 : ℝ) ^ (⌈(m.choose (m / 2) : ℝ) / m⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (hC.trans (Nat.le_ceil _))
    _ ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
        rw [Real.rpow_natCast]
        exact_mod_cast two_pow_ceil_le_ncard_matroids m

end SignedTropical.SparsePaving
