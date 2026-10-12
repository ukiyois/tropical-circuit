import SignedTropical.GapSum
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Weighted basis maximization: greedy optimality as a gap sum

`docs/research-direction-2026-10-11.md`, Section 3.2, the first step of the proof of
Theorem A: `h_M` is the Lovász extension of the rank function.

Matroids are Mathlib's `Matroid (Fin m)` with ground set `univ`.  For a set
`S : Finset (Fin m)` the rank is `M.eRk S : ℕ∞`, and `rk M S : ℕ` is its value as a natural
number (`coe_rk`).  The weight of a basis maximization problem is

`h_M(w) = max_B w(B)` (`maxBasisWeight`), the greatest element of the finite nonempty set
of basis weights (`isGreatest_maxBasisWeight`).

Results:

* `maxBasisWeight_eq_gapSum`: for `D ≥ 0`,
  `h_M(D) = ∑_{k<m} (s_{k+1} - s_k) r({e : D_e > s_k}) = C_F(D)` with `F(S) = r(E \ S)`.
  The upper bound reads each basis weight as the gap sum of `|B \ G_k|`
  (`sum_eq_gapSum_card`) and bounds `|B ∩ U| ≤ r(U)`; the lower bound is a basis that
  restricts to a basis of every strict upper level set `{e : D_e > s_k}`, which exists
  because these sets form a chain (`exists_isBase_chain`).
* `maxBasisWeight_add_const`: `h_M(w + c·1) = h_M(w) + c k` with `k = r(E)`, since every
  basis has `k` elements.
* `maxBasisWeight_indicator`: `h_M(1_T) = r(T)`.
-/

open Finset

namespace SignedTropical

variable {m : ℕ}

section Rank

variable (M : Matroid (Fin m))

/-- The rank of a set of elements, as a natural number. -/
noncomputable def rk (S : Finset (Fin m)) : ℕ := (M.eRk (S : Set (Fin m))).toNat

theorem eRk_ne_top (X : Set (Fin m)) : M.eRk X ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.toFinite X).encard_lt_top.ne (M.eRk_le_encard X)

theorem coe_rk (S : Finset (Fin m)) : (rk M S : ℕ∞) = M.eRk (S : Set (Fin m)) :=
  ENat.coe_toNat (eRk_ne_top M _)

/-- The rank `k = r(E)`, as a natural number. -/
noncomputable def rank : ℕ := M.eRank.toNat

theorem eRank_ne_top : M.eRank ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.toFinite M.E).encard_lt_top.ne M.eRank_le_encard_ground

theorem rk_le_rank (S : Finset (Fin m)) : rk M S ≤ rank M := by
  have h := M.eRk_le_eRank (S : Set (Fin m))
  rw [← coe_rk, ← ENat.coe_toNat (eRank_ne_top M)] at h
  exact_mod_cast h

/-- The rank of `univ` is `k`, when the ground set is `univ`. -/
theorem rk_univ (hE : M.E = Set.univ) : rk M univ = rank M := by
  simp only [rk, rank, coe_univ, ← hE, Matroid.eRk_ground]

/-- An independent subset of `S` has at most `r(S)` elements. -/
theorem card_le_rk {I S : Finset (Fin m)} (hI : M.Indep (I : Set (Fin m))) (hIS : I ⊆ S) :
    I.card ≤ rk M S := by
  have h := hI.encard_le_eRk_of_subset (Finset.coe_subset.2 hIS)
  rw [Set.encard_coe_eq_coe_finsetCard, ← coe_rk] at h
  exact_mod_cast h

/-- A basis of `S` has exactly `r(S)` elements. -/
theorem card_eq_rk {I S : Finset (Fin m)} (h : M.IsBasis (I : Set (Fin m)) (S : Set (Fin m))) :
    I.card = rk M S := by
  have h' := h.encard_eq_eRk
  rw [Set.encard_coe_eq_coe_finsetCard, ← coe_rk] at h'
  exact_mod_cast h'

/-- Every basis has `k` elements. -/
theorem card_base {B : Finset (Fin m)} (hB : M.IsBase (B : Set (Fin m))) :
    B.card = rank M := by
  have h := hB.encard_eq_eRank
  rw [Set.encard_coe_eq_coe_finsetCard, ← ENat.coe_toNat (eRank_ne_top M)] at h
  exact_mod_cast h

/-- Every set of `Fin m` is a finite set, read as a `Finset`. -/
theorem exists_finset (X : Set (Fin m)) : ∃ F : Finset (Fin m), (F : Set (Fin m)) = X :=
  ⟨(Set.toFinite X).toFinset, Set.Finite.coe_toFinset _⟩

/-- A matroid on `Fin m` has rank at most `m`. -/
theorem rank_le_card : rank M ≤ m := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨B, rfl⟩ := exists_finset B
  rw [← card_base M hB]
  simpa using Finset.card_le_univ B

/-- The rank of a set is at most its size. -/
theorem rk_le_card (S : Finset (Fin m)) : rk M S ≤ S.card := by
  have h : (rk M S : ℕ∞) ≤ S.card := by
    rw [coe_rk, ← Set.encard_coe_eq_coe_finsetCard]
    exact M.eRk_le_encard _
  exact_mod_cast h

end Rank

section BasisWeight

variable (M : Matroid (Fin m))

/-- The weights of the bases at `w`. -/
def basisWeights (w : Fin m → ℝ) : Set ℝ :=
  {x | ∃ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ∧ x = ∑ e ∈ B, w e}

/-- `h_M(w) = max_B w(B)`. -/
noncomputable def maxBasisWeight (w : Fin m → ℝ) : ℝ := sSup (basisWeights M w)

theorem basisWeights_finite (w : Fin m → ℝ) : (basisWeights M w).Finite := by
  refine ((Set.finite_univ (α := Finset (Fin m))).image fun B => ∑ e ∈ B, w e).subset ?_
  rintro x ⟨B, -, rfl⟩
  exact ⟨B, trivial, rfl⟩

theorem basisWeights_nonempty (w : Fin m → ℝ) : (basisWeights M w).Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨F, rfl⟩ := exists_finset B
  exact ⟨_, F, hB, rfl⟩

/-- `h_M(w)` is the greatest basis weight. -/
theorem isGreatest_maxBasisWeight (w : Fin m → ℝ) :
    IsGreatest (basisWeights M w) (maxBasisWeight M w) :=
  ⟨(basisWeights_nonempty M w).csSup_mem (basisWeights_finite M w),
    fun _ hx => le_csSup (basisWeights_finite M w).bddAbove hx⟩

theorem maxBasisWeight_eq_of_isGreatest {w : Fin m → ℝ} {v : ℝ}
    (h : IsGreatest (basisWeights M w) v) : maxBasisWeight M w = v :=
  (isGreatest_maxBasisWeight M w).unique h

/-- **Translation.**  `h_M(w + c·1) = h_M(w) + c k`. -/
theorem maxBasisWeight_add_const (w : Fin m → ℝ) (c : ℝ) :
    maxBasisWeight M (fun e => w e + c) = maxBasisWeight M w + c * rank M := by
  have hshift : ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) →
      ∑ e ∈ B, (w e + c) = ∑ e ∈ B, w e + c * rank M := fun B hB => by
    rw [sum_add_distrib, sum_const, card_base M hB, nsmul_eq_mul, mul_comm]
  obtain ⟨⟨B, hB, hBv⟩, hmax⟩ := isGreatest_maxBasisWeight M w
  refine maxBasisWeight_eq_of_isGreatest M ⟨⟨B, hB, by rw [hshift B hB, hBv]⟩, ?_⟩
  rintro x ⟨B', hB', rfl⟩
  rw [hshift B' hB']
  exact add_le_add_left (hmax ⟨B', hB', rfl⟩) _

end BasisWeight

section Chain

variable {M : Matroid (Fin m)}

theorem chain_mono {X : ℕ → Set (Fin m)} {p : ℕ} (hX : ∀ i < p, X i ⊆ X (i + 1)) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ p → X i ⊆ X j := by
  intro i j hij hjp
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h | rfl
    · exact (ih (by omega) (by omega)).trans (hX j (by omega))
    · exact subset_rfl

/-- **Bases along a chain.**  For sets `X 0 ⊆ X 1 ⊆ ⋯ ⊆ X p = E` there is a basis `B`
whose intersection with every `X i` is a basis of `X i`. -/
theorem exists_isBase_chain (X : ℕ → Set (Fin m)) (p : ℕ) (hX : ∀ i < p, X i ⊆ X (i + 1))
    (hXp : X p = M.E) : ∃ B, M.IsBase B ∧ ∀ i ≤ p, M.IsBasis (B ∩ X i) (X i) := by
  have hground : ∀ i ≤ p, X i ⊆ M.E := fun i hi => hXp ▸ chain_mono hX hi le_rfl
  have key : ∀ i ≤ p, ∃ J, M.IsBasis J (X i) ∧ ∀ j ≤ i, M.IsBasis (J ∩ X j) (X j) := by
    intro i hi
    induction i with
    | zero =>
      obtain ⟨J, hJ⟩ := M.exists_isBasis (X 0) (hground 0 (Nat.zero_le p))
      refine ⟨J, hJ, fun j hj => ?_⟩
      rw [Nat.le_zero.1 hj, Set.inter_eq_left.2 hJ.subset]
      exact hJ
    | succ i ih =>
      obtain ⟨J, hJ, hJj⟩ := ih (by omega)
      obtain ⟨J', hJ', hJ'i⟩ := hJ.exists_isBasis_inter_eq_of_superset (hX i (by omega))
        (hground (i + 1) hi)
      refine ⟨J', hJ', fun j hj => ?_⟩
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · have hji : X j ⊆ X i := chain_mono hX (by omega) (by omega)
        rw [show J' ∩ X j = J ∩ X j by
          rw [← hJ'i, Set.inter_assoc, Set.inter_eq_right.2 hji]]
        exact hJj j (by omega)
      · rw [Set.inter_eq_left.2 hJ'.subset]
        exact hJ'
  obtain ⟨B, hB, hBi⟩ := key p le_rfl
  rw [hXp, Matroid.isBasis_ground_iff] at hB
  exact ⟨B, hB, hBi⟩

end Chain

section Greedy

variable {M : Matroid (Fin m)}

/-- **Greedy optimality, as a gap sum.**  For `D ≥ 0`,
`h_M(D) = ∑_{k<m} (s_{k+1} - s_k) r({e : D_e > s_k})`, i.e. `h_M(D) = C_F(D)` for
`F(S) = r(E \ S)`. -/
theorem maxBasisWeight_eq_gapSum (hE : M.E = Set.univ) {D : Fin m → ℝ} (hD : ∀ e, 0 ≤ D e) :
    maxBasisWeight M D = gapSum (fun S => (rk M (univ \ S) : ℝ)) D := by
  apply maxBasisWeight_eq_of_isGreatest
  -- the strict upper level sets, as an increasing chain ending at the ground set
  set X : ℕ → Set (Fin m) := fun i =>
    if i ≤ m then ((univ \ threshSet D (m - i) : Finset (Fin m)) : Set (Fin m)) else Set.univ
  have hX : ∀ i < m + 1, X i ⊆ X (i + 1) := by
    intro i hi
    simp only [X]
    by_cases him : i + 1 ≤ m
    · rw [if_pos (by omega), if_pos him, coe_subset]
      intro e
      simp only [compl_threshSet, mem_filter, mem_univ, true_and]
      exact (sortedVal_mono hD (by omega) (by omega)).trans_lt
    · rw [if_neg him]; exact Set.subset_univ _
  obtain ⟨B₀, hB₀, hB₀X⟩ := exists_isBase_chain (M := M) X (m + 1) hX (by simp [X, hE])
  obtain ⟨B, rfl⟩ := exists_finset B₀
  refine ⟨⟨B, hB₀, ?_⟩, ?_⟩
  · rw [sum_eq_gapSum_card hD]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    have hbasis := hB₀X (m - k) (by omega)
    simp only [X, if_pos (show m - k ≤ m by omega), show m - (m - k) = k by omega,
      ← Finset.coe_inter] at hbasis
    have hBk : B ∩ (univ \ threshSet D k) = B \ threshSet D k := by ext e; simp
    rw [hBk] at hbasis
    simp only [card_eq_rk M hbasis]
  · rintro x ⟨B', hB', rfl⟩
    rw [sum_eq_gapSum_card hD]
    exact gapSum_mono hD fun S => by
      exact_mod_cast card_le_rk M (hB'.indep.subset (by simp)) (sdiff_subset_sdiff
        (subset_univ B') subset_rfl)

/-- `h_M(1_T) = r(T)`. -/
theorem maxBasisWeight_indicator (hE : M.E = Set.univ) (T : Finset (Fin m)) :
    maxBasisWeight M (fun e => if e ∈ T then 1 else 0) = rk M T := by
  apply maxBasisWeight_eq_of_isGreatest
  have hsum : ∀ B : Finset (Fin m), ∑ e ∈ B, (if e ∈ T then (1 : ℝ) else 0)
      = ((B ∩ T).card : ℝ) := by
    intro B; rw [sum_boole]; congr 2
  obtain ⟨I, hI⟩ := M.exists_isBasis (T : Set (Fin m)) (by rw [hE]; exact Set.subset_univ _)
  obtain ⟨B₀, hB₀, hIB⟩ := hI.exists_isBase
  obtain ⟨B, rfl⟩ := exists_finset B₀
  refine ⟨⟨B, hB₀, ?_⟩, ?_⟩
  · rw [hsum]
    have h : M.IsBasis ((B ∩ T : Finset (Fin m)) : Set (Fin m)) (T : Set (Fin m)) := by
      rw [Finset.coe_inter, ← hIB]; exact hI
    rw [card_eq_rk M h]
  · rintro x ⟨B', hB', rfl⟩
    rw [hsum]
    exact_mod_cast card_le_rk M (hB'.indep.subset (by simp)) inter_subset_right

end Greedy

end SignedTropical
