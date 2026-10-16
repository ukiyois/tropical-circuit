import SignedTropical.Rainbow.Connectivity

/-!
# The partition matroid of the columns

`colMatroid col`, for `col : Fin m → Fin n`, is the partition matroid of the columns: a set is
independent if and only if it meets every column at most once (`indep_iff`).  Its rank function
counts the columns that a set meets (`rk_eq`).  It is the matroid `N_S` of the transversal
matroids in Corollary `cor:transversal` (`Classes/Transversal.lean`).

* `colMatroid col`: the partition matroid of the columns, with ground set `univ`.
* `isBasis_iff`: `I` is a basis of `X` if and only if `I ⊆ X` meets every column at most once and
  meets every column that `X` meets.
* `rk_eq`: the rank of `S` is the number of columns that `S` meets.
-/

open Finset
open scoped Matroid

namespace SignedTropical.Rainbow.Partition

variable {m n : ℕ} {col : Fin m → Fin n}

/-! ### The matroid -/

/-- Augmentation for sets that meet every column at most once. -/
theorem injOn_augment {I J : Set (Fin m)} (hI : Set.InjOn col I) (hJ : Set.InjOn col J)
    (hIJ : I.ncard < J.ncard) : ∃ e ∈ J, e ∉ I ∧ Set.InjOn col (insert e I) := by
  rw [← hI.ncard_image, ← hJ.ncard_image] at hIJ
  obtain ⟨_, ⟨e, heJ, rfl⟩, he⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hIJ
  have heI : e ∉ I := fun h => he (Set.mem_image_of_mem col h)
  exact ⟨e, heJ, heI, (Set.injOn_insert heI).2 ⟨hI, he⟩⟩

variable (col) in
/-- The partition matroid of the columns: a set is independent if and only if it meets every
column at most once. -/
def colMatroid : Matroid (Fin m) :=
  (IndepMatroid.ofFinite Set.finite_univ (fun I => Set.InjOn col I) (Set.injOn_empty col)
    (fun _ _ hJ hIJ => hJ.mono hIJ) (fun _ _ hI hJ hIJ => injOn_augment hI hJ hIJ)
    fun _ _ => Set.subset_univ _).matroid

@[simp] theorem colMatroid_ground : (colMatroid col).E = Set.univ := rfl

@[simp] theorem indep_iff {I : Set (Fin m)} : (colMatroid col).Indep I ↔ Set.InjOn col I :=
  Iff.rfl

/-- `I` is a basis of `X` if and only if `I ⊆ X` meets every column at most once and meets every
column that `X` meets. -/
theorem isBasis_iff {I X : Set (Fin m)} : (colMatroid col).IsBasis I X ↔
    Set.InjOn col I ∧ I ⊆ X ∧ ∀ e ∈ X, ∃ f ∈ I, col f = col e := by
  refine ⟨fun h => ⟨indep_iff.1 h.indep, h.subset, fun e he => ?_⟩, fun ⟨hI, hIX, hX⟩ => ?_⟩
  · by_contra! hcol
    have heI : e ∉ I := fun heI => hcol e heI rfl
    exact (h.insert_dep ⟨he, heI⟩).not_indep (indep_iff.2 ((Set.injOn_insert heI).2
      ⟨indep_iff.1 h.indep, fun ⟨f, hf, hfe⟩ => hcol f hf hfe⟩))
  · refine Matroid.Indep.isBasis_of_forall_insert (indep_iff.2 hI) hIX fun e ⟨he, heI⟩ => ?_
    obtain ⟨f, hf, hfe⟩ := hX e he
    refine Matroid.dep_iff.2 ⟨fun h => heI ?_, Set.subset_univ _⟩
    rw [indep_iff.1 h (Set.mem_insert e I) (Set.mem_insert_of_mem e hf) hfe.symm]
    exact hf

/-- The rank of `S` is the number of columns that `S` meets. -/
theorem rk_eq (S : Finset (Fin m)) : rk (colMatroid col) S = #(S.image col) := by
  obtain ⟨I₀, hI₀⟩ := (colMatroid col).exists_isBasis (S : Set (Fin m)) (Set.subset_univ _)
  obtain ⟨I, rfl⟩ := exists_finset I₀
  obtain ⟨hinj, hIS, hcov⟩ := isBasis_iff.1 hI₀
  rw [← card_eq_rk _ hI₀, ← card_image_of_injOn hinj]
  congr 1
  ext j
  simp only [mem_image]
  exact ⟨fun ⟨f, hf, hfj⟩ => ⟨f, hIS hf, hfj⟩, fun ⟨e, he, hej⟩ =>
    let ⟨f, hf, hfe⟩ := hcov e he
    ⟨f, hf, hfe.trans hej⟩⟩

end SignedTropical.Rainbow.Partition
