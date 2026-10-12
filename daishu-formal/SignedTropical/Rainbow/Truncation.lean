import SignedTropical.Rainbow.MinBases

/-!
# Truncations

`greedy_intersection.tex`, proof of Theorem `thm:D`, Step 4.  The truncation of `M` at `j` keeps
the independent sets of `M` with at most `j` elements (Mathlib has no truncation).

* `truncate M j`, `indep_truncate_iff`.
* `rk_truncate`: its rank function is `min(r, j)`.
* `isBase_truncate_iff`: for `j ≤ r(M)`, its bases are the independent sets of `M` with `j`
  elements.
* `isBase_truncate_both_iff`: for `j ≤ r(M₁), r(M₂)`, the common bases of the truncations at `j`
  are the common independent sets of size `j`.
-/

open Finset

namespace SignedTropical.Rainbow.Trunc

variable {m : ℕ}

/-- The truncation of `M` at `j`, as an independence system. -/
noncomputable def truncIndepMatroid (M : Matroid (Fin m)) (j : ℕ) : IndepMatroid (Fin m) :=
  IndepMatroid.ofFinset Set.univ (fun I => M.Indep (I : Set (Fin m)) ∧ #I ≤ j)
    ⟨by simp, by simp⟩
    (fun _ _ hJ hIJ => ⟨hJ.1.subset (coe_subset.2 hIJ), (card_le_card hIJ).trans hJ.2⟩)
    (fun I J hI hJ hcard => by
      obtain ⟨e, heJ, heI, he⟩ := hI.1.augment_finset hJ.1 hcard
      refine ⟨e, heJ, heI, by simpa using he, ?_⟩
      rw [card_insert_of_notMem heI]
      exact (Nat.succ_le_of_lt hcard).trans hJ.2)
    (fun _ _ => Set.subset_univ _)

/-- **The truncation** of `M` at `j`: the independent sets of `M` with at most `j` elements. -/
noncomputable def truncate (M : Matroid (Fin m)) (j : ℕ) : Matroid (Fin m) :=
  (truncIndepMatroid M j).matroid

variable {M : Matroid (Fin m)} {j : ℕ}

@[simp] theorem truncate_E : (truncate M j).E = Set.univ := rfl

theorem indep_truncate_iff (I : Finset (Fin m)) :
    (truncate M j).Indep (I : Set (Fin m)) ↔ M.Indep (I : Set (Fin m)) ∧ #I ≤ j := by
  simp [truncate, truncIndepMatroid]

/-- **The rank of the truncation** at `j` is `min(r, j)`. -/
theorem rk_truncate (hE : M.E = Set.univ) (S : Finset (Fin m)) :
    rk (truncate M j) S = min (rk M S) j := by
  refine le_antisymm ?_ ?_
  · obtain ⟨J, hJ⟩ := (truncate M j).exists_isBasis (S : Set (Fin m)) (by simp)
    obtain ⟨J, rfl⟩ := exists_finset J
    have hJi := (indep_truncate_iff J).1 hJ.indep
    rw [← card_eq_rk _ hJ]
    exact le_min (card_le_rk M hJi.1 (coe_subset.1 hJ.subset)) hJi.2
  · obtain ⟨I, hI⟩ := M.exists_isBasis (S : Set (Fin m)) (by rw [hE]; exact Set.subset_univ _)
    obtain ⟨I, rfl⟩ := exists_finset I
    obtain ⟨I', hI'I, hcard⟩ := exists_subset_card_eq (show min (rk M S) j ≤ #I by
      rw [card_eq_rk M hI]; exact min_le_left _ _)
    rw [← hcard]
    exact card_le_rk _ ((indep_truncate_iff I').2 ⟨hI.indep.subset (coe_subset.2 hI'I),
      hcard ▸ min_le_right _ _⟩) (hI'I.trans (coe_subset.1 hI.subset))

/-- The truncation at `j ≤ r(M)` has rank `j`. -/
theorem rank_truncate (hE : M.E = Set.univ) (hj : j ≤ rank M) : rank (truncate M j) = j := by
  rw [← rk_univ _ truncate_E, rk_truncate hE, rk_univ M hE, min_eq_right hj]

/-- **The bases of the truncation** at `j ≤ r(M)` are the independent sets of `M` with `j`
elements. -/
theorem isBase_truncate_iff (hE : M.E = Set.univ) (hj : j ≤ rank M) (B : Finset (Fin m)) :
    (truncate M j).IsBase (B : Set (Fin m)) ↔ M.Indep (B : Set (Fin m)) ∧ #B = j := by
  refine ⟨fun h => ⟨((indep_truncate_iff B).1 h.indep).1,
    (card_base _ h).trans (rank_truncate hE hj)⟩, fun ⟨hB, hcard⟩ => ?_⟩
  have hBi : (truncate M j).Indep (B : Set (Fin m)) := (indep_truncate_iff B).2 ⟨hB, hcard.le⟩
  have hr : (truncate M j).eRank = (j : ℕ∞) := by
    rw [← ENat.coe_toNat (eRank_ne_top (truncate M j))]
    exact_mod_cast rank_truncate hE hj
  refine hBi.isBase_of_eRk_ge (Set.toFinite _) ?_
  rw [hBi.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard]
  exact hr.le

/-- **Common bases of truncations.**  For `j ≤ r(M₁)` and `j ≤ r(M₂)`, a set is a common base of
the truncations at `j` iff it is a common independent set of `M₁` and `M₂` with `j` elements. -/
theorem isBase_truncate_both_iff {M₁ M₂ : Matroid (Fin m)} (hE₁ : M₁.E = Set.univ)
    (hE₂ : M₂.E = Set.univ) (hj₁ : j ≤ rank M₁) (hj₂ : j ≤ rank M₂) (X : Finset (Fin m)) :
    ((truncate M₁ j).IsBase (X : Set (Fin m)) ∧ (truncate M₂ j).IsBase (X : Set (Fin m))) ↔
      M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧ #X = j := by
  rw [isBase_truncate_iff hE₁ hj₁, isBase_truncate_iff hE₂ hj₂]
  tauto

end SignedTropical.Rainbow.Trunc
