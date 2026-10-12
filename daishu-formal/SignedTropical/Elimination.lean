import SignedTropical.Matroid
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Linear matroids and elimination without branching

The linear algebra shared by the binary matroids of `Binary.lean` and the matroids over a finite
field of `Classes/Field.lean`, for a matrix `A ∈ K^{r × m}` over a field `K`.

1. **The column matroid** (`colMatroid`): a set of columns is independent iff the columns are
   linearly independent over `K`.  Its rank function is the dimension of the span of the columns
   (`eRk_colMatroid`), Mathlib's `Matrix.rank` of the column submatrix (`eRk_colMatroid_eq_rank`).
2. **The leading position** of a Boolean vector (`leadV`, `leadV_eq`), read by the circuits.
3. **Elimination without branching** (`elimK`): the columns are processed in order; each is
   reduced against an echelon basis kept in `r` slots, and a nonzero remainder, scaled to a
   leading `1`, is stored in the slot of its leading position (`colStepK`).  One column keeps the
   invariant "echelon, and the stored vectors span the processed columns" (`colStepK_inv`), so
   the number of occupied slots is the rank (`card_occ_elimK`).  `Binary.lean` reads its Boolean
   elimination over `GF(2)` through this one (`zst_elimV`), and `Classes/Field.lean` runs it on
   one-hot codes.
-/

open Finset Module Submodule

namespace SignedTropical

variable {K : Type} [Field K] {r m : ℕ}

/-! ### The column matroid of a matrix -/

section ColumnMatroid

variable (A : Matrix (Fin r) (Fin m) K)

/-- Column `e` of `A`. -/
def colK (e : Fin m) : Fin r → K := fun i => A i e

/-- A linearly independent family on a finite set spans a space of dimension equal to the
number of elements. -/
theorem finrank_span_image {ι V : Type} [AddCommGroup V] [Module K V] {v : ι → V}
    {s : Finset ι} (h : LinearIndepOn K v (s : Set ι)) :
    finrank K (span K (v '' s)) = s.card := by
  have := finrank_span_eq_card h
  rw [← Set.image_eq_range] at this
  simpa using this

theorem colK_indep_aug {I J : Finset (Fin m)}
    (hI : LinearIndepOn K (colK A) (I : Set (Fin m)))
    (hJ : LinearIndepOn K (colK A) (J : Set (Fin m))) (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K (colK A) (insert e I : Finset (Fin m)) := by
  by_contra hcon
  push Not at hcon
  have hsub : colK A '' (J : Set (Fin m)) ⊆ span K (colK A '' (I : Set (Fin m))) := by
    rintro _ ⟨e, he, rfl⟩
    by_cases heI : e ∈ I
    · exact subset_span ⟨e, heI, rfl⟩
    · have h := hcon e he heI
      rw [Finset.coe_insert] at h
      by_contra h'
      exact h ((linearIndepOn_insert (Finset.mem_coe.not.2 heI)).2 ⟨hI, h'⟩)
  have hle := Submodule.finrank_mono (span_le.2 hsub)
  rw [finrank_span_image hJ, finrank_span_image hI] at hle
  omega

/-- The column matroid of `A`, as an independence system. -/
noncomputable def colIndepMatroid : IndepMatroid (Fin m) :=
  IndepMatroid.ofFinset Set.univ (fun I => LinearIndepOn K (colK A) (I : Set (Fin m)))
    (by rw [Finset.coe_empty]; exact linearIndepOn_empty K (colK A))
    (fun _ _ hJ hIJ => hJ.mono (Finset.coe_subset.2 hIJ))
    (fun _ _ hI hJ hcard => colK_indep_aug A hI hJ hcard)
    (fun _ _ => Set.subset_univ _)

/-- **The column matroid** of `A`: ground set all columns, a set of columns independent iff
the columns are linearly independent over `K`. -/
noncomputable def colMatroid : Matroid (Fin m) := (colIndepMatroid A).matroid

@[simp] theorem colMatroid_E : (colMatroid A).E = Set.univ := rfl

theorem colMatroid_indep (I : Finset (Fin m)) :
    (colMatroid A).Indep (I : Set (Fin m)) ↔ LinearIndepOn K (colK A) (I : Set (Fin m)) := by
  simp [colMatroid, colIndepMatroid]

/-- **The rank of a set of columns is the dimension of their span.** -/
theorem eRk_colMatroid (S : Finset (Fin m)) :
    (colMatroid A).eRk (S : Set (Fin m)) = finrank K (span K (colK A '' (S : Set (Fin m)))) := by
  obtain ⟨I₀, hI⟩ := (colMatroid A).exists_isBasis (S : Set (Fin m)) (by simp)
  obtain ⟨I, rfl⟩ := exists_finset I₀
  have hind := (colMatroid_indep A I).1 hI.indep
  have hspan : span K (colK A '' (S : Set (Fin m))) = span K (colK A '' (I : Set (Fin m))) := by
    refine le_antisymm (span_le.2 ?_) (span_mono (Set.image_mono hI.subset))
    rintro _ ⟨e, he, rfl⟩
    by_cases heI : e ∈ I
    · exact subset_span ⟨e, heI, rfl⟩
    · have hdep := hI.insert_dep ⟨he, by simpa using heI⟩
      by_contra h'
      apply hdep.not_indep
      rw [← Finset.coe_insert, colMatroid_indep, Finset.coe_insert]
      exact (linearIndepOn_insert (Finset.mem_coe.not.2 heI)).2 ⟨hind, h'⟩
  rw [← hI.encard_eq_eRk, hspan, finrank_span_image hind, Set.encard_coe_eq_coe_finsetCard]

/-- **The rank of a set of columns is the rank of the column submatrix.** -/
theorem eRk_colMatroid_eq_rank (S : Finset (Fin m)) :
    (colMatroid A).eRk (S : Set (Fin m)) = (A.submatrix id (fun e : S => (e : Fin m))).rank := by
  have hcols : Set.range (A.submatrix id (fun e : S => (e : Fin m))).col
      = colK A '' (S : Set (Fin m)) := by
    ext v
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨e, e.2, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
  rw [eRk_colMatroid, Matrix.rank_eq_finrank_span_cols, hcols]

end ColumnMatroid

/-! ### The leading position of a Boolean vector -/

/-- The leading position of `v`: `v_p ∧ ¬∃ q < p, v_q`. -/
def leadV (v : Fin r → Bool) (p : Fin r) : Bool := v p && !decide (∃ q < p, v q = true)

/-- The leading position is the least index of a `1`. -/
theorem leadV_eq {v : Fin r → Bool} {q : Fin r} (hq : v q = true)
    (hmin : ∀ i < q, v i = false) (p : Fin r) : leadV v p = decide (p = q) := by
  simp only [leadV]
  by_cases hpq : p = q
  · subst hpq
    simp only [hq, Bool.true_and, decide_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_exists, not_and]
    intro i hi; simp [hmin i hi]
  · rw [decide_eq_false hpq]
    cases hvp : v p
    · rfl
    · simp only [Bool.true_and, Bool.not_eq_false', decide_eq_true_eq]
      rcases lt_or_gt_of_ne hpq with h | h
      · exact absurd hvp (by simp [hmin p h])
      · exact ⟨q, h, hq⟩

/-! ### Elimination without branching, on values -/

section Elimination

/-- The elimination state: which of the `r` slots are occupied, and the stored vectors. -/
abbrev StK (K : Type) (r : ℕ) := (Fin r → Bool) × (Fin r → Fin r → K)

/-- Reduction at slot `p`: `vᵢ ← vᵢ - c b_{p,i}`, with `c = v_p` if slot `p` is occupied and
`c = 0` otherwise. -/
def redStepK (st : StK K r) (v : Fin r → K) (p : Fin r) : Fin r → K :=
  fun i => v i - (if st.1 p then v p else 0) * st.2 p i

/-- Reduction at all slots, in increasing order. -/
def reduceK (st : StK K r) (v : Fin r → K) : Fin r → K :=
  (List.finRange r).foldl (redStepK st) v

/-- Column `e` of `A`, masked by the input bit: `x_e A_{i,e}`. -/
def colValK (A : Matrix (Fin r) (Fin m) K) (e : Fin m) (xe : Bool) : Fin r → K :=
  fun i => if xe then A i e else 0

/-- The empty state. -/
def initK : StK K r := (fun _ => false, fun _ _ => 0)

/-- Occupied slots hold vectors with a leading `1` at the slot index. -/
def EchelonK (st : StK K r) : Prop :=
  ∀ p, st.1 p = true → st.2 p p = 1 ∧ ∀ q < p, st.2 p q = 0

/-- The occupied slots. -/
def occ (f : Fin r → Bool) : Finset (Fin r) := univ.filter fun p => f p = true

/-- The stored vectors. -/
def vecsK (st : StK K r) : Set (Fin r → K) := st.2 '' (occ st.1 : Set (Fin r))

/-- The invariant after processing the columns `T`. -/
def InvK (A : Matrix (Fin r) (Fin m) K) (st : StK K r) (T : Finset (Fin m)) : Prop :=
  EchelonK st ∧ span K (vecsK st) = span K (colK A '' (T : Set (Fin m)))

section Reduce

variable {st : StK K r} (hst : EchelonK st)
include hst

theorem redStepK_of_lt {v : Fin r → K} {p i : Fin r} (hi : i < p) : redStepK st v p i = v i := by
  simp only [redStepK]
  cases hf : st.1 p
  · simp
  · simp [(hst p hf).2 i hi]

theorem redStepK_self {v : Fin r → K} {p : Fin r} (hf : st.1 p = true) :
    redStepK st v p p = 0 := by
  simp [redStepK, hf, (hst p hf).1]

theorem foldl_redStepK_of_lt :
    ∀ (ps : List (Fin r)) (v : Fin r → K) (i : Fin r), (∀ p ∈ ps, i < p) →
      ps.foldl (redStepK st) v i = v i
  | [], _, _, _ => rfl
  | p :: ps, v, i, h => by
    rw [List.foldl_cons, foldl_redStepK_of_lt ps _ i fun q hq => h q (by simp [hq]),
      redStepK_of_lt hst (h p (by simp))]

/-- After reduction, every occupied slot reads `0`. -/
theorem reduceK_occ (v : Fin r → K) {p : Fin r} (hf : st.1 p = true) : reduceK st v p = 0 := by
  obtain ⟨l₁, l₂, hl⟩ := List.mem_iff_append.1 (List.mem_finRange p)
  have hsorted : (List.finRange r).Pairwise (· < ·) := List.pairwise_lt_finRange r
  rw [hl, List.pairwise_append] at hsorted
  have hl₂ : ∀ q ∈ l₂, p < q := fun q hq => (List.pairwise_cons.1 hsorted.2.1).1 q hq
  rw [reduceK, hl, List.foldl_append, List.foldl_cons, foldl_redStepK_of_lt hst l₂ _ p hl₂,
    redStepK_self hst hf]

end Reduce

theorem redStepK_sub_mem (st : StK K r) (v : Fin r → K) (p : Fin r) :
    redStepK st v p - v ∈ span K (vecsK st) := by
  cases hf : st.1 p
  · have : redStepK st v p - v = 0 := by funext i; simp [redStepK, hf]
    rw [this]; exact zero_mem _
  · have : redStepK st v p - v = -(v p • st.2 p) := by funext i; simp [redStepK, hf]
    rw [this, neg_mem_iff]
    exact smul_mem _ _ (subset_span ⟨p, by simp [occ, hf], rfl⟩)

theorem reduceK_sub_mem (st : StK K r) (v : Fin r → K) :
    reduceK st v - v ∈ span K (vecsK st) := by
  suffices ∀ (ps : List (Fin r)) (v : Fin r → K),
      ps.foldl (redStepK st) v - v ∈ span K (vecsK st) from this _ v
  intro ps
  induction ps with
  | nil => intro v; simp
  | cons p ps ih =>
    intro v
    rw [List.foldl_cons]
    have := add_mem (ih (redStepK st v p)) (redStepK_sub_mem st v p)
    rwa [sub_add_sub_cancel] at this

theorem reduceK_zero (st : StK K r) : reduceK st 0 = 0 := by
  suffices ∀ ps : List (Fin r), ps.foldl (redStepK st) 0 = 0 from this _
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, show redStepK st 0 p = 0 by funext i; simp [redStepK]]
    exact ih

/-- Two vectors congruent modulo `span X` span the same space together with `X`. -/
theorem span_insert_congrK {V : Type} [AddCommGroup V] [Module K V] {u w : V} {X : Set V}
    (h : u - w ∈ span K X) : span K (insert u X) = span K (insert w X) := by
  have key : ∀ {u w : V}, u - w ∈ span K X → span K (insert u X) ≤ span K (insert w X) := by
    intro u w h
    refine span_le.2 (Set.insert_subset ?_ fun x hx => subset_span (Set.mem_insert_of_mem _ hx))
    rw [show u = (u - w) + w by abel]
    exact add_mem (span_mono (Set.subset_insert _ _) h) (subset_span (Set.mem_insert _ _))
  exact le_antisymm (key h) (key (by rw [← neg_sub]; exact neg_mem h))

/-- Scaling by a nonzero scalar does not change the span. -/
theorem span_insert_smul {V : Type} [AddCommGroup V] [Module K V] {c : K} (hc : c ≠ 0)
    (u : V) (X : Set V) : span K (insert (c • u) X) = span K (insert u X) := by
  rw [span_insert, span_insert, span_singleton_smul_eq (IsUnit.mk0 c hc)]

/-- Echelon vectors are linearly independent. -/
theorem linearIndepOn_of_echelonK {st : StK K r} (h : EchelonK st) :
    LinearIndepOn K st.2 (occ st.1 : Set (Fin r)) := by
  classical
  rw [linearIndepOn_iff']
  intro t g ht hsum
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hgi₀⟩ := hne
  set t' := t.filter fun i => g i ≠ 0
  have ht' : t'.Nonempty := ⟨i₀, by simp [t', hi₀, hgi₀]⟩
  set p₀ := t'.min' ht'
  have hp₀ : p₀ ∈ t' := t'.min'_mem ht'
  have hp₀t : p₀ ∈ t := (mem_filter.1 hp₀).1
  have hgp₀ : g p₀ ≠ 0 := (mem_filter.1 hp₀).2
  have hcoord := congrFun hsum p₀
  rw [Finset.sum_apply, Finset.sum_eq_single p₀] at hcoord
  · have hflag : st.1 p₀ = true := by simpa [occ] using ht hp₀t
    simp [(h p₀ hflag).1] at hcoord
    exact hgp₀ hcoord
  · intro i hi hip
    by_cases hgi : g i = 0
    · simp [hgi]
    · have hlt : p₀ < i := lt_of_le_of_ne (t'.min'_le i (by simp [t', hi, hgi])) (Ne.symm hip)
      have hflag : st.1 i = true := by simpa [occ] using ht hi
      simp [(h i hflag).2 p₀ hlt]
  · intro h'; exact absurd hp₀t h'

/-- Under the invariant, the number of occupied slots is the rank of the processed columns. -/
theorem card_occ_of_invK {A : Matrix (Fin r) (Fin m) K} {st : StK K r} {T : Finset (Fin m)}
    (h : InvK A st T) : (occ st.1).card = finrank K (span K (colK A '' (T : Set (Fin m)))) := by
  rw [← h.2, vecsK, finrank_span_image (V := Fin r → K) (v := st.2) (s := occ st.1)
    (linearIndepOn_of_echelonK h.1)]

variable [DecidableEq K]

/-- The positions of the nonzero entries. -/
def nzK (v : Fin r → K) : Fin r → Bool := fun i => !decide (v i = 0)

/-- Store `v`, scaled to a leading `1`, in the slot of its leading position. -/
def insertK (st : StK K r) (v : Fin r → K) : StK K r :=
  (fun p => st.1 p || leadV (nzK v) p,
    fun p i => if leadV (nzK v) p then v i * (v p)⁻¹ else st.2 p i)

/-- One column of the elimination. -/
def colStepK (A : Matrix (Fin r) (Fin m) K) (st : StK K r) (e : Fin m) (xe : Bool) : StK K r :=
  insertK st (reduceK st (colValK A e xe))

/-- **The elimination**: all columns, in order, starting from the empty state. -/
def elimK (A : Matrix (Fin r) (Fin m) K) (x : Fin m → Bool) : StK K r :=
  (List.finRange m).foldl (fun st e => colStepK A st e (x e)) initK

theorem insertK_of_zero (st : StK K r) {v : Fin r → K} (hv : ∀ i, v i = 0) :
    insertK st v = st := by
  have hl : ∀ p, leadV (nzK v) p = false := fun p => by simp [leadV, nzK, hv p]
  ext p
  · simp [insertK, hl]
  · simp [insertK, hl]

/-- **One column keeps the invariant.** -/
theorem colStepK_inv {A : Matrix (Fin r) (Fin m) K} {st : StK K r} {T : Finset (Fin m)}
    (h : InvK A st T) (e : Fin m) (xe : Bool) :
    InvK A (colStepK A st e xe) (if xe then insert e T else T) := by
  obtain ⟨hech, hspan⟩ := h
  set v := reduceK st (colValK A e xe) with hv
  have hsub := reduceK_sub_mem st (colValK A e xe)
  rw [← hv] at hsub
  have hcol : colValK A e xe = if xe then colK A e else 0 := by
    funext i; cases xe <;> simp [colValK, colK]
  by_cases hv0 : ∀ i, v i = 0
  · -- the remainder vanishes: the state does not change
    rw [colStepK, ← hv, insertK_of_zero st hv0]
    refine ⟨hech, ?_⟩
    cases xe
    · simpa using hspan
    · simp only [if_true]
      rw [show v = 0 from funext hv0, hcol, if_pos rfl, zero_sub, neg_mem_iff, hspan] at hsub
      rw [hspan, Finset.coe_insert, Set.image_insert_eq]
      exact (span_insert_eq_span hsub).symm
  · -- the remainder has a leading position `q`, which is an empty slot
    push Not at hv0
    obtain ⟨i₀, hi₀⟩ := hv0
    set q := (univ.filter fun i => v i ≠ 0).min' ⟨i₀, by simp [hi₀]⟩
    have hq : v q ≠ 0 := by
      have := Finset.min'_mem (univ.filter fun i => v i ≠ 0) ⟨i₀, by simp [hi₀]⟩
      simpa using this
    have hmin : ∀ i < q, v i = 0 := by
      intro i hi
      by_contra h
      exact absurd hi (not_lt.2 (Finset.min'_le _ _ (by simpa using h)))
    have hqF : st.1 q = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      exact hq (by rw [hv, reduceK_occ hech _ h])
    have hlead : ∀ p, leadV (nzK v) p = decide (p = q) :=
      leadV_eq (by simpa [nzK] using hq) fun i hi => by simp [nzK, hmin i hi]
    have hxe : xe = true := by
      by_contra hx
      rw [Bool.not_eq_true] at hx
      subst hx
      apply hq
      rw [hv, show colValK A e false = 0 from funext fun i => by simp [colValK], reduceK_zero]
      rfl
    subst hxe
    simp only [if_true]
    have hnew1 : (colStepK A st e true).1 = fun p => st.1 p || decide (p = q) := by
      funext p; simp [colStepK, ← hv, insertK, hlead]
    have hnew2 : (colStepK A st e true).2 = fun p => if p = q then (v q)⁻¹ • v else st.2 p := by
      funext p i
      by_cases hpq : p = q
      · subst hpq; simp [colStepK, ← hv, insertK, hlead, mul_comm]
      · simp [colStepK, ← hv, insertK, hlead, hpq]
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [hnew1] at hp
      rw [hnew2]
      by_cases hpq : p = q
      · subst hpq
        exact ⟨by simp [hq], fun i hi => by simp [hmin i hi]⟩
      · have hp' : st.1 p = true := by simpa [hpq] using hp
        simpa [hpq] using hech p hp'
    · have hocc : occ (colStepK A st e true).1 = insert q (occ st.1) := by
        ext p; by_cases hpq : p = q <;> simp [occ, hnew1, hpq]
      have hvecs : vecsK (colStepK A st e true) = insert ((v q)⁻¹ • v) (vecsK st) := by
        rw [vecsK, hocc, Finset.coe_insert, Set.image_insert_eq]
        congr 1
        · simp [hnew2]
        · refine Set.image_congr fun p hp => ?_
          have hpq : p ≠ q := by
            rintro rfl
            simp [occ, hqF] at hp
          simp [hnew2, hpq]
      rw [hcol, if_pos rfl] at hsub
      rw [hvecs, span_insert_smul (inv_ne_zero hq), span_insert_congrK hsub, span_insert, hspan,
        ← span_insert, Finset.coe_insert, Set.image_insert_eq]

/-- The invariant holds after every prefix of the columns. -/
theorem foldl_colStepK_inv (A : Matrix (Fin r) (Fin m) K) (x : Fin m → Bool) :
    ∀ l : List (Fin m), InvK A (l.foldl (fun st e => colStepK A st e (x e)) initK)
      (l.toFinset.filter fun e => x e = true) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨fun p hp => by simp [initK] at hp, ?_⟩
    simp [vecsK, occ, initK]
  | append_singleton l e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hT : ((l ++ [e]).toFinset.filter fun e => x e = true)
        = if x e then insert e (l.toFinset.filter fun e => x e = true)
          else l.toFinset.filter fun e => x e = true := by
      ext e'
      by_cases he : x e = true
      · simp only [he, if_true, mem_filter, List.mem_toFinset, List.mem_append,
          List.mem_singleton, mem_insert]
        constructor
        · rintro ⟨h | rfl, hx⟩
          · exact Or.inr ⟨h, hx⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨h, hx⟩)
          · exact ⟨Or.inr rfl, he⟩
          · exact ⟨Or.inl h, hx⟩
      · simp only [he, Bool.false_eq_true, if_false, mem_filter, List.mem_toFinset,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨h | rfl, hx⟩
          · exact ⟨h, hx⟩
          · exact absurd hx he
        · rintro ⟨h, hx⟩
          exact ⟨Or.inl h, hx⟩
    rw [hT]
    exact colStepK_inv ih e (x e)

/-- **The number of occupied slots is the rank of the selected columns.** -/
theorem card_occ_elimK (A : Matrix (Fin r) (Fin m) K) (S : Finset (Fin m)) :
    (occ (elimK A (indicator S)).1).card = finrank K (span K (colK A '' (S : Set (Fin m)))) := by
  have h := foldl_colStepK_inv A (indicator S) (List.finRange m)
  have hS : ((List.finRange m).toFinset.filter fun e => indicator S e = true) = S := by
    ext e; simp [indicator]
  rw [hS] at h
  exact card_occ_of_invK h

end Elimination

end SignedTropical
