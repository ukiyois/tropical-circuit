import SignedTropical.Rainbow.Connectivity

/-!
# The partition matroid of the columns (Proposition `prop:assign-pos`)

`greedy_intersection.tex`, Section 4.2, Proposition `prop:assign-pos`.

The elements `Fin m` are the edges of a bipartite graph and `col : Fin m → Fin n` sends an edge
to its column.  The blocks of the assignment problem are the rows, `blk : Fin m → Fin k`; they do
not enter `θ`, and appear only in `isRainbowBase_iff`.

* `colMatroid col`: the partition matroid of the columns, with ground set `univ`; a set is
  independent if and only if it meets every column at most once (`indep_iff`).
* `isBasis_iff`, `isBase_iff`: a base picks one element in each column that has an element;
  `rk_eq`, `rank_eq`: the rank of `S` is the number of columns that `S` meets;
  `mem_closure_iff`: `e ∈ cl(X)` if and only if `X` meets the column of `e`.
* `isCircuit_iff`: the circuits are the pairs of distinct elements of one column;
  `fundCircuit_eq`: for a base `B` and `e ∉ B`, `C(B, e) = {e, f}` with `f` the element of `B`
  in the column of `e`.
* `connRel_iff`, `exists_isCircuit_iff`, `comp_eq`, `mem_components_iff`: two elements are
  connected if and only if they lie in one column, and the components are the nonempty columns.
* `slack col v f`: `D_f = v_f - min{v_e : col e = col f}`; `notMem_closure_iff_slack_le`:
  `f ∉ cl{g : v_g < v_f - t}` if and only if `D_f ≤ t`.
* `theta_le_iff`, `theta_eq_fold`, `theta_eq_sup'` (Proposition `prop:assign-pos`):
  `θ(B) = max_{f ∈ B} D_f`; `pos_eq`: `P_t` is the set of bases inside `{D ≤ t}`.
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

/-- A base picks one element in each column that has an element: `B` is a base if and only if it
meets every column at most once and meets the column of every element. -/
theorem isBase_iff {B : Set (Fin m)} : (colMatroid col).IsBase B ↔
    Set.InjOn col B ∧ ∀ e, ∃ f ∈ B, col f = col e := by
  rw [← Matroid.isBasis_ground_iff, colMatroid_ground, isBasis_iff]
  simp

/-- If `T` meets the column of every element, the bases of `M ↾ T` are the bases of `M` inside
`T`. -/
theorem isBase_restrict_iff {T B : Set (Fin m)} (hT : ∀ e, ∃ g ∈ T, col g = col e) :
    ((colMatroid col) ↾ T).IsBase B ↔ (colMatroid col).IsBase B ∧ B ⊆ T := by
  rw [Matroid.isBase_restrict_iff (Set.subset_univ T), isBasis_iff, isBase_iff]
  refine ⟨fun ⟨hinj, hBT, hcov⟩ => ⟨⟨hinj, fun e => ?_⟩, hBT⟩,
    fun ⟨⟨hinj, hcov⟩, hBT⟩ => ⟨hinj, hBT, fun e _ => hcov e⟩⟩
  obtain ⟨g, hg, hge⟩ := hT e
  obtain ⟨f, hf, hfg⟩ := hcov g hg
  exact ⟨f, hf, hfg.trans hge⟩

/-- A base is nonempty when `E` is. -/
theorem nonempty_of_isBase {B : Finset (Fin m)} (hB : (colMatroid col).IsBase (B : Set (Fin m)))
    (e : Fin m) : B.Nonempty :=
  let ⟨f, hf, _⟩ := (isBase_iff.1 hB).2 e
  ⟨f, hf⟩

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

/-- The rank of `colMatroid col` is the number of columns that have an element. -/
theorem rank_eq : rank (colMatroid col) = #(univ.image col) := by
  rw [← rk_univ _ colMatroid_ground, rk_eq]

/-- `e ∈ cl(X)` if and only if `X` meets the column of `e`. -/
theorem mem_closure_iff {X : Set (Fin m)} {e : Fin m} :
    e ∈ (colMatroid col).closure X ↔ ∃ f ∈ X, col f = col e := by
  obtain ⟨I, hI⟩ := (colMatroid col).exists_isBasis X (Set.subset_univ X)
  obtain ⟨hinj, hIX, hcov⟩ := isBasis_iff.1 hI
  rw [← hI.closure_eq_closure, hI.indep.mem_closure_iff]
  constructor
  · rintro (hdep | heI)
    · by_contra! h
      have heI : e ∉ I := fun heI => h e (hIX heI) rfl
      exact hdep.not_indep (indep_iff.2 ((Set.injOn_insert heI).2
        ⟨hinj, fun ⟨f, hf, hfe⟩ => h f (hIX hf) hfe⟩))
    · exact ⟨e, hIX heI, rfl⟩
  · rintro ⟨f, hf, hfe⟩
    obtain ⟨g, hg, hgf⟩ := hcov f hf
    by_cases heI : e ∈ I
    · exact .inr heI
    refine .inl (Matroid.dep_iff.2 ⟨fun h => heI ?_, Set.subset_univ _⟩)
    rw [indep_iff.1 h (Set.mem_insert e I) (Set.mem_insert_of_mem e hg) (hgf.trans hfe).symm]
    exact hg

/-- With the rows as blocks, a rainbow base is a set that meets every row and every column at
most once and meets the column of every element. -/
theorem isRainbowBase_iff {k : ℕ} {blk : Fin m → Fin k} {B : Finset (Fin m)} :
    IsRainbowBase (colMatroid col) blk B ↔
      Set.InjOn col B ∧ Set.InjOn blk B ∧ ∀ e, ∃ f ∈ B, col f = col e := by
  rw [IsRainbowBase, isBase_iff, IsRainbow]
  tauto

/-! ### Circuits and components -/

/-- Two distinct elements of one column form a circuit. -/
theorem isCircuit_pair {e f : Fin m} (hef : e ≠ f) (hcol : col e = col f) :
    (colMatroid col).IsCircuit {e, f} := by
  refine Matroid.isCircuit_iff_forall_ssubset.2 ⟨Matroid.dep_iff.2 ⟨fun h => hef (indep_iff.1 h
    (Set.mem_insert e {f}) (Set.mem_insert_of_mem e (Set.mem_singleton f)) hcol),
    Set.subset_univ _⟩, fun I hI => indep_iff.2 ?_⟩
  have h := Set.ncard_lt_ncard hI
  rw [Set.ncard_pair hef] at h
  exact (Set.ncard_le_one_iff_subsingleton.1 (by omega)).injOn col

/-- The circuits are the pairs of distinct elements of one column. -/
theorem isCircuit_iff {C : Set (Fin m)} : (colMatroid col).IsCircuit C ↔
    ∃ e f, e ≠ f ∧ col e = col f ∧ C = {e, f} := by
  refine ⟨fun hC => ?_, fun ⟨e, f, hef, hcol, hC⟩ => hC ▸ isCircuit_pair hef hcol⟩
  have h : ¬Set.InjOn col C := fun h => hC.dep.not_indep (indep_iff.2 h)
  simp only [Set.InjOn, not_forall] at h
  obtain ⟨e, he, f, hf, hcol, hef⟩ := h
  exact ⟨e, f, hef, hcol, ((isCircuit_pair hef hcol).eq_of_subset_isCircuit hC
    (Set.insert_subset he (Set.singleton_subset_iff.2 hf))).symm⟩

/-- The elements of a circuit lie in one column. -/
theorem col_eq_of_mem_isCircuit {C : Set (Fin m)} (hC : (colMatroid col).IsCircuit C)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) : col e = col f := by
  obtain ⟨x, y, -, hxy, rfl⟩ := isCircuit_iff.1 hC
  have key : ∀ z ∈ ({x, y} : Set (Fin m)), col z = col x := by
    rintro z (rfl | rfl)
    exacts [rfl, hxy.symm]
  exact (key e he).trans (key f hf).symm

/-- For a base `B`, `e ∉ B` and the element `f` of `B` in the column of `e`,
`C(B, e) = {e, f}`. -/
theorem fundCircuit_eq {B : Set (Fin m)} (hB : (colMatroid col).IsBase B) {e f : Fin m}
    (he : e ∉ B) (hf : f ∈ B) (hcol : col f = col e) :
    (colMatroid col).fundCircuit e B = {e, f} :=
  ((isCircuit_pair (fun h => he (by rw [h]; exact hf)) hcol.symm).eq_fundCircuit_of_subset hB.indep
    (Set.insert_subset_insert (Set.singleton_subset_iff.2 hf))).symm

/-- For a base `B` and `e ∉ B`, `C(B, e) = {e, f}` for some `f ∈ B` in the column of `e`. -/
theorem exists_fundCircuit_eq {B : Set (Fin m)} (hB : (colMatroid col).IsBase B) {e : Fin m}
    (he : e ∉ B) : ∃ f ∈ B, col f = col e ∧ (colMatroid col).fundCircuit e B = {e, f} :=
  let ⟨f, hf, hcol⟩ := (isBase_iff.1 hB).2 e
  ⟨f, hf, hcol, fundCircuit_eq hB he hf hcol⟩

/-- Two elements are connected (`e = f` or a circuit contains both) if and only if they lie in
one column. -/
theorem connRel_iff {e f : Fin m} : connRel (colMatroid col) e f ↔ col e = col f := by
  refine ⟨?_, fun h => ?_⟩
  · rintro (rfl | ⟨C, hC, he, hf⟩)
    exacts [rfl, col_eq_of_mem_isCircuit hC he hf]
  by_cases hef : e = f
  · exact .inl hef
  exact .inr ⟨{e, f}, isCircuit_pair hef h, Set.mem_insert e {f},
    Set.mem_insert_of_mem e (Set.mem_singleton f)⟩

/-- Two distinct elements lie on a common circuit if and only if they lie in one column. -/
theorem exists_isCircuit_iff {e f : Fin m} (hef : e ≠ f) :
    (∃ C, (colMatroid col).IsCircuit C ∧ e ∈ C ∧ f ∈ C) ↔ col e = col f := by
  rw [← connRel_iff, connRel, or_iff_right hef]

/-- The component of `e` is the column of `e`. -/
theorem comp_eq (e : Fin m) :
    Conn.comp (colMatroid col) e = univ.filter fun f => col f = col e := by
  ext f
  rw [Conn.mem_comp, connRel_iff, mem_filter, eq_comm]
  simp

/-- The components are the nonempty columns. -/
theorem mem_components_iff {K : Finset (Fin m)} :
    K ∈ Conn.components (colMatroid col) ↔ ∃ e, K = univ.filter fun f => col f = col e := by
  rw [Conn.mem_components]
  exact exists_congr fun e => by rw [comp_eq, eq_comm]

/-! ### The slacks `D` and Proposition `prop:assign-pos` -/

section Slack

variable (col) (v : Fin m → ℝ)

/-- `D_f = v_f - min{v_e : col e = col f}`, the excess of `v_f` over the least value of `v` in the
column of `f`. -/
noncomputable def slack (f : Fin m) : ℝ :=
  v f - (univ.filter fun e => col e = col f).inf' ⟨f, mem_filter.2 ⟨mem_univ f, rfl⟩⟩ v

/-- `v_f - v_e ≤ D_f` for `e` in the column of `f`. -/
theorem sub_le_slack {e f : Fin m} (h : col e = col f) : v f - v e ≤ slack col v f :=
  sub_le_sub_left (inf'_le _ (mem_filter.2 ⟨mem_univ e, h⟩)) _

/-- `D_f ≥ 0`. -/
theorem slack_nonneg (f : Fin m) : 0 ≤ slack col v f := by
  simpa using sub_le_slack col v (rfl : col f = col f)

/-- The minimum of a column is attained. -/
theorem exists_slack_eq (f : Fin m) : ∃ e, col e = col f ∧ slack col v f = v f - v e := by
  obtain ⟨e, he, heq⟩ := exists_mem_eq_inf' (s := univ.filter fun e => col e = col f)
    ⟨f, mem_filter.2 ⟨mem_univ f, rfl⟩⟩ v
  exact ⟨e, (mem_filter.1 he).2, by rw [slack, heq]⟩

/-- `D_f ≤ t` if and only if `v_f - t ≤ v_g` for every `g` in the column of `f`. -/
theorem slack_le_iff {f : Fin m} {t : ℝ} :
    slack col v f ≤ t ↔ ∀ g, col g = col f → v f - t ≤ v g := by
  rw [slack, sub_le_comm, le_inf'_iff]
  simp

/-- Every column has an element of slack `0`, one of least value. -/
theorem exists_slack_eq_zero (f : Fin m) : ∃ g, col g = col f ∧ slack col v g = 0 := by
  obtain ⟨g, hg, heq⟩ := exists_slack_eq col v f
  refine ⟨g, hg, le_antisymm ((slack_le_iff col v).2 fun h hh => ?_) (slack_nonneg col v g)⟩
  have := sub_le_slack col v (hh.trans hg)
  rw [heq] at this
  linarith

/-- `f ∉ cl{g : v_g < v_f - t}` if and only if `D_f ≤ t`: the possibly optimal elements of
Definition `def:posl` are those of the threshold graph `{D ≤ t}`. -/
theorem notMem_closure_iff_slack_le (f : Fin m) (t : ℝ) :
    f ∉ (colMatroid col).closure {g | v g < v f - t} ↔ slack col v f ≤ t := by
  rw [mem_closure_iff, slack_le_iff]
  simp only [Set.mem_setOf_eq, not_exists, not_and]
  exact forall_congr' fun g => ⟨fun h hg => not_lt.1 fun hlt => h hlt hg,
    fun h hlt hg => (h hg).not_gt hlt⟩

variable {col v}

/-- For a base `B`, `θ(B) ≤ t` if and only if `0 ≤ t` and `D_f ≤ t` for every `f ∈ B`. -/
theorem theta_le_iff {B : Finset (Fin m)} (hB : (colMatroid col).IsBase (B : Set (Fin m)))
    {t : ℝ} : theta (colMatroid col) v B ≤ t ↔ 0 ≤ t ∧ ∀ f ∈ B, slack col v f ≤ t := by
  have hinj := (isBase_iff.1 hB).1
  rw [theta, fold_max_le]
  simp only [mem_filter, mem_product, mem_univ, true_and, and_imp, Prod.forall]
  refine and_congr_right fun ht => ⟨fun h f hf => ?_, fun h e g heB hg => ?_⟩
  · obtain ⟨e, hcol, heq⟩ := exists_slack_eq col v f
    rw [heq]
    by_cases hef : e = f
    · rw [hef, sub_self]
      exact ht
    have heB : e ∉ B := fun heB => hef (hinj heB hf hcol)
    refine h e f heB ?_
    rw [fundCircuit_eq hB heB hf hcol.symm]
    exact Set.mem_insert_of_mem e (Set.mem_singleton f)
  · obtain ⟨f, hfB, hcol⟩ := (isBase_iff.1 hB).2 e
    rw [fundCircuit_eq hB heB hfB hcol] at hg
    rcases hg with rfl | hg
    · rw [sub_self]
      exact ht
    · rw [Set.mem_singleton_iff.1 hg]
      exact (sub_le_slack col v hcol.symm).trans (h f hfB)

/-- Proposition `prop:assign-pos`, with the `0` of Definition `def:theta`: for every base `B`,
`θ(B) = max({0} ∪ {D_f : f ∈ B})`. -/
theorem theta_eq_fold {B : Finset (Fin m)} (hB : (colMatroid col).IsBase (B : Set (Fin m))) :
    theta (colMatroid col) v B = B.fold max 0 (slack col v) :=
  le_antisymm ((theta_le_iff hB).2 ((fold_max_le _).1 le_rfl))
    ((fold_max_le _).2 ((theta_le_iff hB).1 le_rfl))

/-- Proposition `prop:assign-pos`: if `M` is the partition matroid of the columns, then for every
nonempty base `B`, `θ(B) = max_{f ∈ B} D_f` with `D_f = v_f - min{v_e : col e = col f}`.  (The
bases are nonempty as soon as `E` is, `nonempty_of_isBase`.) -/
theorem theta_eq_sup' {B : Finset (Fin m)} (hB : (colMatroid col).IsBase (B : Set (Fin m)))
    (hne : B.Nonempty) : theta (colMatroid col) v B = B.sup' hne (slack col v) := by
  refine le_antisymm ((theta_le_iff hB).2 ⟨?_, fun f hf => le_sup' _ hf⟩)
    (sup'_le _ _ ((theta_le_iff hB).1 le_rfl).2)
  obtain ⟨f, hf⟩ := hne
  exact (slack_nonneg col v f).trans (le_sup' _ hf)

/-- Proposition `prop:assign-pos`: for `t ≥ 0`, `P_t` is the set of bases inside the threshold
graph `{D ≤ t}`. -/
theorem pos_eq {t : ℝ} (ht : 0 ≤ t) : Pos (colMatroid col) v t =
    {B : Finset (Fin m) | (colMatroid col).IsBase (B : Set (Fin m)) ∧
      (B : Set (Fin m)) ⊆ {f | slack col v f ≤ t}} := by
  ext B
  simp only [Pos, Set.mem_setOf_eq]
  exact and_congr_right fun hB => (theta_le_iff hB).trans (and_iff_right ht)

/-- Proposition `prop:assign-pos`, in the form used by Proposition `prop:posl`: for `t ≥ 0`,
`P_t` is the set of bases of the column matroid restricted to the threshold graph `{D ≤ t}`. -/
theorem pos_eq_restrict {t : ℝ} (ht : 0 ≤ t) : Pos (colMatroid col) v t =
    {B : Finset (Fin m) |
      ((colMatroid col) ↾ {f | slack col v f ≤ t}).IsBase (B : Set (Fin m))} := by
  rw [pos_eq ht]
  ext B
  refine (isBase_restrict_iff fun e => ?_).symm
  obtain ⟨g, hg, h0⟩ := exists_slack_eq_zero col v e
  exact ⟨g, (h0.le.trans ht : slack col v g ≤ t), hg⟩

end Slack

end SignedTropical.Rainbow.Partition
