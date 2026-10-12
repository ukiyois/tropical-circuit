import SignedTropical.Elimination
import SignedTropical.TheoremA
import SignedTropical.Converse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Algebra.Field.ZMod

/-!
# Corollary C for binary matroids

`docs/research-direction-2026-10-11.md`, Section 3.2, Corollary C, for the class of binary
matroids (linear matroids over `GF(2)` with a fixed representation).

1. **The binary matroid** of a matrix `A ∈ GF(2)^{r × m}` (`binaryMatroid`): the column
   matroid of `Elimination.lean` over `GF(2)`, so a set of columns is independent iff the
   columns are linearly independent over `GF(2)`.  Its rank function is the dimension of the
   span of the columns (`eRk_binaryMatroid`), which is Mathlib's `Matrix.rank` of the column
   submatrix (`eRk_binaryMatroid_eq_rank`).
2. **Elimination without branching** (`elimV`): the columns are processed in order; each
   is reduced against an echelon basis kept in a fixed array of `r` slots, and a nonzero
   remainder is stored in the slot of its leading position.  Every step is a fixed Boolean
   formula of the input bits, so the whole procedure is a Boolean circuit.  Read over
   `GF(2)`, it is the elimination `elimK` of `Elimination.lean` (`zst_elimV`), so the number
   of occupied slots is the rank (`card_flagSet_elimV`).
3. **The rank circuit** (`binaryRankCircuit`) outputs this number in binary.  It has
   `m (9 r² + 5 r) + 11 r ⌈log₂(r+1)⌉` gates (`binaryRankCircuit_size`).
4. **Corollary C** (`corollaryC_binary`): Theorem A applied to this circuit.
-/

open Finset Module Submodule

namespace SignedTropical

variable {r m n : ℕ}

/-! ### The binary matroid of a matrix -/

section BinaryMatroid

variable (A : Matrix (Fin r) (Fin m) (ZMod 2))

/-- Column `e` of `A`. -/
def colZ (e : Fin m) : Fin r → ZMod 2 := fun i => A i e

/-- **The binary matroid** of `A`: the column matroid of `Elimination.lean` over `GF(2)`, whose
independent sets are the sets of columns that are linearly independent over `GF(2)`. -/
noncomputable def binaryMatroid : Matroid (Fin m) := colMatroid A

@[simp] theorem binaryMatroid_E : (binaryMatroid A).E = Set.univ := rfl

theorem binaryMatroid_indep (I : Finset (Fin m)) :
    (binaryMatroid A).Indep (I : Set (Fin m)) ↔
      LinearIndepOn (ZMod 2) (colZ A) (I : Set (Fin m)) :=
  colMatroid_indep A I

/-- **The rank of a set of columns is the dimension of their span.** -/
theorem eRk_binaryMatroid (S : Finset (Fin m)) :
    (binaryMatroid A).eRk (S : Set (Fin m))
      = finrank (ZMod 2) (span (ZMod 2) (colZ A '' (S : Set (Fin m)))) :=
  eRk_colMatroid A S

/-- **The rank of a set of columns is the rank of the column submatrix.** -/
theorem eRk_binaryMatroid_eq_rank (S : Finset (Fin m)) :
    (binaryMatroid A).eRk (S : Set (Fin m))
      = (A.submatrix id (fun e : S => (e : Fin m))).rank :=
  eRk_colMatroid_eq_rank A S

end BinaryMatroid

/-! ### Elimination without branching, on Boolean values -/

section Elimination

/-- A Boolean vector, read over `GF(2)`. -/
def zvec (u : Fin r → Bool) : Fin r → ZMod 2 := fun i => if u i then 1 else 0

/-- The elimination state: which of the `r` slots are occupied, and the stored vectors. -/
abbrev ESt (r : ℕ) := (Fin r → Bool) × (Fin r → Fin r → Bool)

/-- Reduction at slot `p`: `vᵢ ← vᵢ ⊕ ((v_p ∧ f_p) ∧ b_{p,i})`. -/
def redStep (st : ESt r) (v : Fin r → Bool) (p : Fin r) : Fin r → Bool :=
  fun i => v i ^^ ((v p && st.1 p) && st.2 p i)

/-- Reduction at all slots, in increasing order. -/
def reduceV (st : ESt r) (v : Fin r → Bool) : Fin r → Bool :=
  (List.finRange r).foldl (redStep st) v

/-- Store `v` in the slot of its leading position (`leadV` of `Elimination.lean`). -/
def insertV (st : ESt r) (v : Fin r → Bool) : ESt r :=
  (fun p => st.1 p || leadV v p, fun p i => (leadV v p && v i) || (!leadV v p && st.2 p i))

/-- Column `e` of `A`, masked by the input bit: `x_e ∧ [A_{i,e} = 1]`. -/
def colV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (e : Fin m) (xe : Bool) : Fin r → Bool :=
  fun i => xe && decide (A i e = 1)

/-- One column of the elimination. -/
def colStepV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (st : ESt r) (e : Fin m) (xe : Bool) : ESt r :=
  insertV st (reduceV st (colV A e xe))

/-- The empty state. -/
def initV : ESt r := (fun _ => false, fun _ _ => false)

/-- **The elimination**: all columns, in order, starting from the empty state. -/
def elimV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (x : Fin m → Bool) : ESt r :=
  (List.finRange m).foldl (fun st e => colStepV A st e (x e)) initV

/-- The occupied slots. -/
def flagSet (st : ESt r) : Finset (Fin r) := univ.filter fun p => st.1 p = true

/-- A Boolean state read over `GF(2)`: a state of the elimination of `Elimination.lean`. -/
def zst (st : ESt r) : StK (ZMod 2) r := (st.1, fun p => zvec (st.2 p))

/-- One reduction step commutes with the reading over `GF(2)`. -/
theorem zvec_redStep (st : ESt r) (v : Fin r → Bool) (p : Fin r) :
    zvec (redStep st v p) = redStepK (zst st) (zvec v) p := by
  funext i
  cases h₁ : v i <;> cases h₂ : v p <;> cases h₃ : st.1 p <;> cases h₄ : st.2 p i <;>
    simp only [redStep, redStepK, zst, zvec, h₁, h₂, h₃, h₄] <;> decide

/-- The reduction commutes with the reading over `GF(2)`. -/
theorem zvec_reduceV (st : ESt r) (v : Fin r → Bool) :
    zvec (reduceV st v) = reduceK (zst st) (zvec v) := by
  suffices ∀ (ps : List (Fin r)) (v : Fin r → Bool),
      zvec (ps.foldl (redStep st) v) = ps.foldl (redStepK (zst st)) (zvec v) from this _ v
  intro ps
  induction ps with
  | nil => intro v; rfl
  | cons p ps ih => intro v; rw [List.foldl_cons, List.foldl_cons, ih, zvec_redStep]

/-- The nonzero entries of `zvec v` are the set entries of `v`. -/
theorem nzK_zvec (v : Fin r → Bool) : nzK (zvec v) = v := by
  funext i
  cases h : v i <;> simp [nzK, zvec, h]

/-- Storing a vector commutes with the reading over `GF(2)`: its leading entry is `1`, so the
scaling of `insertK` is the identity. -/
theorem zst_insertV (st : ESt r) (v : Fin r → Bool) :
    zst (insertV st v) = insertK (zst st) (zvec v) := by
  have hl : ∀ p, leadV v p = true → v p = true := fun p h => by
    simp only [leadV, Bool.and_eq_true] at h
    exact h.1
  refine Prod.ext (funext fun p => ?_) (funext fun p => funext fun i => ?_)
  · simp [zst, insertV, insertK, nzK_zvec]
  · simp only [zst, insertV, insertK, nzK_zvec]
    cases h : leadV v p
    · simp [zvec]
    · simp [zvec, hl p h]

/-- The masked column, read over `GF(2)`. -/
theorem zvec_colV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (e : Fin m) (xe : Bool) :
    zvec (colV A e xe) = colValK A e xe := by
  funext i
  simp only [zvec, colV, colValK]
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (A i e) with h | h <;>
    cases xe <;> simp [h]

/-- **One column of the Boolean elimination is one column of the elimination over `GF(2)`.** -/
theorem zst_colStepV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (st : ESt r) (e : Fin m) (xe : Bool) :
    zst (colStepV A st e xe) = colStepK A (zst st) e xe := by
  rw [colStepV, colStepK, zst_insertV, zvec_reduceV, zvec_colV]

theorem zst_initV : zst (initV : ESt r) = initK := by
  refine Prod.ext rfl (funext fun p => funext fun i => ?_)
  simp [zst, initV, initK, zvec]

/-- **The Boolean elimination is the elimination over `GF(2)`.** -/
theorem zst_elimV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (x : Fin m → Bool) :
    zst (elimV A x) = elimK A x := by
  rw [elimV, elimK, ← zst_initV]
  generalize (initV : ESt r) = st
  induction (List.finRange m) generalizing st with
  | nil => rfl
  | cons e l ih => rw [List.foldl_cons, List.foldl_cons, ← zst_colStepV, ih]

/-- **The number of occupied slots is the rank of the selected columns**, by `card_occ_elimK` of
`Elimination.lean` and `zst_elimV`. -/
theorem card_flagSet_elimV (A : Matrix (Fin r) (Fin m) (ZMod 2)) (S : Finset (Fin m)) :
    (flagSet (elimV A (indicator S))).card
      = finrank (ZMod 2) (span (ZMod 2) (colZ A '' (S : Set (Fin m)))) := by
  have h := card_occ_elimK A S
  rw [← zst_elimV] at h
  exact h

end Elimination

/-! ### The rank circuit -/

section Circuit

/-- `mapB` adds `c` gates per element when each builder does. -/
theorem mapB_length {Op β γ : Type} {b : β → Bld Op n γ} {c : ℕ}
    (hc : ∀ a gs, (b a gs).1.length = gs.length + c) :
    ∀ (l : List β) (gs : List (Gate Op n)), (mapB b l gs).1.length = gs.length + c * l.length
  | [], gs => by simp [mapB]
  | a :: l, gs => by
    simp only [mapB, mapB_length hc l, hc, List.length_cons]; ring

/-- One result per slot, in order. -/
def vecB {Op γ : Type} (bld : Fin r → Bld Op n γ) (dflt : γ) : Bld Op n (Fin r → γ) :=
  fun gs =>
    let p := mapB bld (List.finRange r) gs
    (p.1, fun i => p.2.getD i dflt)

theorem vecB_gen {Op γ : Type} {bld : Fin r → Bld Op n γ} (dflt : γ)
    (P : List (Gate Op n) → Prop) (Q : List (Gate Op n) → Fin r → γ → Prop)
    (hQ : ∀ gs gs' i y, gs <+: gs' → Q gs i y → Q gs' i y)
    (hb : ∀ i gs, P gs → gs <+: (bld i gs).1 ∧ P (bld i gs).1 ∧ Q (bld i gs).1 i (bld i gs).2)
    (gs : List (Gate Op n)) (hP : P gs) :
    gs <+: (vecB bld dflt gs).1 ∧ P (vecB bld dflt gs).1 ∧
      ∀ i, Q (vecB bld dflt gs).1 i ((vecB bld dflt gs).2 i) := by
  obtain ⟨hp, hP', hQl⟩ := mapB_gen P Q hQ (List.finRange r) (fun i _ gs' h => hb i gs' h) gs hP
  refine ⟨hp, hP', fun i => ?_⟩
  have hlen : (mapB bld (List.finRange r) gs).2.length = r := by
    rw [← hQl.length_eq]; simp
  have hi : (i : ℕ) < (mapB bld (List.finRange r) gs).2.length := by rw [hlen]; exact i.2
  have := hQl.get (by simp) hi
  simp only [List.get_eq_getElem, List.getElem_finRange] at this
  show Q _ i ((mapB bld (List.finRange r) gs).2.getD i dflt)
  rw [List.getD_eq_getElem _ _ hi]
  exact this

theorem vecB_length {Op γ : Type} {bld : Fin r → Bld Op n γ} (dflt : γ) {c : ℕ}
    (hc : ∀ i gs, (bld i gs).1.length = gs.length + c) (gs : List (Gate Op n)) :
    (vecB bld dflt gs).1.length = gs.length + c * r := by
  simp [vecB, mapB_length hc]

/-- A vector of operands denotes a vector of bits. -/
def VecDen (gs : List (Gate BoolOp m)) (v : Fin r → Arg m) (V : (Fin m → Bool) → Fin r → Bool) :
    Prop :=
  ∀ i, Den boolInterp gs (v i) (fun x => V x i)

theorem VecDen.mono {gs gs' : List (Gate BoolOp m)} {v : Fin r → Arg m}
    {V : (Fin m → Bool) → Fin r → Bool} (h : VecDen gs v V) (hp : gs <+: gs') : VecDen gs' v V :=
  fun i => (h i).mono hp

/-- A scalar builder per slot gives a vector denotation. -/
theorem vecB_den {bld : Fin r → Bld BoolOp m (Arg m)} {gs₀ : List (Gate BoolOp m)}
    {F : Fin r → (Fin m → Bool) → Bool}
    (hb : ∀ i gs, gs₀ <+: gs →
      gs <+: (bld i gs).1 ∧ Den boolInterp (bld i gs).1 (bld i gs).2 (F i)) :
    gs₀ <+: (vecB bld .const gs₀).1 ∧
      VecDen (vecB bld .const gs₀).1 (vecB bld .const gs₀).2 (fun x i => F i x) := by
  obtain ⟨hp, -, hQ⟩ := vecB_gen (bld := bld) .const (fun gs => gs₀ <+: gs)
    (fun gs i a => Den boolInterp gs a (F i)) (fun _ _ _ _ hp h => h.mono hp)
    (fun i gs h => ⟨(hb i gs h).1, h.trans (hb i gs h).1, (hb i gs h).2⟩) gs₀ (List.prefix_refl _)
  exact ⟨hp, hQ⟩

/-- The masked column: input `e` where `A_{i,e} = 1`, the constant `false` elsewhere. -/
def colArg (A : Matrix (Fin r) (Fin m) (ZMod 2)) (e : Fin m) (i : Fin r) : Arg m :=
  if A i e = 1 then .input e else .const

theorem colArg_den (A : Matrix (Fin r) (Fin m) (ZMod 2)) (e : Fin m) (gs : List (Gate BoolOp m)) :
    VecDen gs (colArg A e) (fun x => colV A e (x e)) := by
  intro i
  by_cases h : A i e = 1
  · simp only [colArg, if_pos h]
    exact (den_input gs e).congr fun x => by simp [colV, h]
  · simp only [colArg, if_neg h]
    exact (den_const gs).congr fun x => by simp [colV, h, boolInterp]

/-- Reduction at slot `p`: one gate for `v_p ∧ f_p`, five per entry. -/
def redB (f : Fin r → Arg m) (b : Fin r → Fin r → Arg m) (v : Fin r → Arg m) (p : Fin r) :
    Bld BoolOp m (Fin r → Arg m) := fun gs =>
  let c := emit BoolOp.and (v p) (f p) gs
  vecB (fun i gs => let t := emit BoolOp.and c.2 (b p i) gs; xorB (v i) t.2 t.1) .const c.1

/-- The state operands denote the elimination state. -/
def StDen (gs : List (Gate BoolOp m)) (st : (Fin r → Arg m) × (Fin r → Fin r → Arg m))
    (F : (Fin m → Bool) → ESt r) : Prop :=
  VecDen gs st.1 (fun x => (F x).1) ∧ ∀ p, VecDen gs (st.2 p) (fun x => (F x).2 p)

theorem StDen.mono {gs gs' : List (Gate BoolOp m)} {st : (Fin r → Arg m) × (Fin r → Fin r → Arg m)}
    {F : (Fin m → Bool) → ESt r} (h : StDen gs st F) (hp : gs <+: gs') : StDen gs' st F :=
  ⟨h.1.mono hp, fun p => (h.2 p).mono hp⟩

theorem redB_spec {st : (Fin r → Arg m) × (Fin r → Fin r → Arg m)} {F : (Fin m → Bool) → ESt r}
    {v : Fin r → Arg m} {V : (Fin m → Bool) → Fin r → Bool} {gs : List (Gate BoolOp m)}
    (hst : StDen gs st F) (hv : VecDen gs v V) (p : Fin r) :
    gs <+: (redB st.1 st.2 v p gs).1 ∧ (redB st.1 st.2 v p gs).1.length = gs.length + (1 + 5 * r) ∧
      VecDen (redB st.1 st.2 v p gs).1 (redB st.1 st.2 v p gs).2
        (fun x => redStep (F x) (V x) p) := by
  have hc := den_emit BoolOp.and (hv p) (hst.1 p)
  have pc := isPrefix_emit BoolOp.and (v p) (st.1 p) gs
  obtain ⟨hp, hden⟩ := vecB_den (gs₀ := (emit BoolOp.and (v p) (st.1 p) gs).1)
    (F := fun i x => redStep (F x) (V x) p i) (fun i gs' h => by
      have ht := den_emit BoolOp.and (hc.mono h) ((hst.2 p i).mono (pc.trans h))
      obtain ⟨hp', -, hx⟩ := xorB_spec (((hv i).mono (pc.trans h)).mono (isPrefix_emit _ _ _ _)) ht
      exact ⟨(isPrefix_emit _ _ _ _).trans hp', hx.congr fun x => rfl⟩)
  refine ⟨pc.trans hp, ?_, hden⟩
  simp only [redB, vecB]
  rw [mapB_length (c := 5) (fun i gs' => by simp [xorB, length_emit]), length_emit]
  simp only [List.length_finRange]
  ring

/-- Reduction at the slots `ps`, in order. -/
def reduceB (f : Fin r → Arg m) (b : Fin r → Fin r → Arg m) :
    List (Fin r) → (Fin r → Arg m) → Bld BoolOp m (Fin r → Arg m)
  | [], v => fun gs => (gs, v)
  | p :: ps, v => fun gs =>
    let q := redB f b v p gs
    reduceB f b ps q.2 q.1

theorem reduceB_spec {st : (Fin r → Arg m) × (Fin r → Fin r → Arg m)} {F : (Fin m → Bool) → ESt r} :
    ∀ (ps : List (Fin r)) {v : Fin r → Arg m} {V : (Fin m → Bool) → Fin r → Bool}
      {gs : List (Gate BoolOp m)}, StDen gs st F → VecDen gs v V →
      gs <+: (reduceB st.1 st.2 ps v gs).1 ∧
        (reduceB st.1 st.2 ps v gs).1.length = gs.length + ps.length * (1 + 5 * r) ∧
        VecDen (reduceB st.1 st.2 ps v gs).1 (reduceB st.1 st.2 ps v gs).2
          (fun x => ps.foldl (redStep (F x)) (V x))
  | [], v, V, gs, _, hv => ⟨List.prefix_refl _, by simp [reduceB], hv⟩
  | p :: ps, v, V, gs, hst, hv => by
    obtain ⟨hp, hlen, hden⟩ := redB_spec hst hv p
    obtain ⟨hq, hlen', hden'⟩ := reduceB_spec ps (hst.mono hp) hden
    refine ⟨hp.trans hq, ?_, hden'⟩
    simp only [reduceB, hlen', hlen, List.length_cons]; ring

end Circuit

section Circuit2

/-- Disjunction of a list of operands, one gate per entry. -/
def orB : List (Arg m) → Bld BoolOp m (Arg m)
  | [] => fun gs => (gs, .const)
  | a :: l => fun gs =>
    let p := orB l gs
    emit BoolOp.or a p.2 p.1

theorem orB_spec :
    ∀ {l : List (Arg m)} {F : (Fin m → Bool) → List Bool} {gs : List (Gate BoolOp m)},
      DenL boolInterp gs l F →
      gs <+: (orB l gs).1 ∧ (orB l gs).1.length = gs.length + l.length ∧
        Den boolInterp (orB l gs).1 (orB l gs).2 (fun x => (F x).any id)
  | [], F, gs, h => ⟨List.prefix_refl _, by simp [orB], (den_const gs).congr fun x => by
      rw [show F x = [] by rw [← h.2 x]; rfl]; rfl⟩
  | a :: l, F, gs, h => by
    obtain ⟨ha, hl, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hden⟩ := orB_spec hl
    have hr := den_emit BoolOp.or (ha.mono hp) hden
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), by simp [orB, length_emit, hlen]; ring,
      hr.congr fun x => ?_⟩
    conv_rhs => rw [hF x]
    simp [boolInterp]

/-- The leading-position bit of slot `p`: `v_p ∧ ¬(∨_{q<p} v_q)`, `r + 2` gates. -/
def leadB (v : Fin r → Arg m) (p : Fin r) : Bld BoolOp m (Arg m) := fun gs =>
  let o := orB ((List.finRange r).map fun q => if q < p then v q else .const) gs
  let nt := emit BoolOp.not o.2 .const o.1
  emit BoolOp.and (v p) nt.2 nt.1

theorem leadB_spec {v : Fin r → Arg m} {V : (Fin m → Bool) → Fin r → Bool}
    {gs : List (Gate BoolOp m)} (hv : VecDen gs v V) (p : Fin r) :
    gs <+: (leadB v p gs).1 ∧ (leadB v p gs).1.length = gs.length + (r + 2) ∧
      Den boolInterp (leadB v p gs).1 (leadB v p gs).2 (fun x => leadV (V x) p) := by
  have hl := DenL.map (I := boolInterp) (gs := gs) (g := fun q => if q < p then v q else .const)
    (G := fun q x => if q < p then V x q else false) (List.finRange r) fun q _ => by
      by_cases hq : q < p
      · simp only [hq, if_true]; exact hv q
      · simp only [hq, if_false]; exact (den_const gs).congr fun _ => rfl
  obtain ⟨hp, hlen, ho⟩ := orB_spec hl
  have hn := den_emit BoolOp.not ho (den_const _)
  have pn := isPrefix_emit BoolOp.not (orB ((List.finRange r).map fun q =>
    if q < p then v q else .const) gs).2 .const (orB ((List.finRange r).map fun q =>
    if q < p then v q else .const) gs).1
  have hr := den_emit BoolOp.and ((hv p).mono (hp.trans pn)) hn
  refine ⟨(hp.trans pn).trans (isPrefix_emit _ _ _ _), ?_, hr.congr fun x => ?_⟩
  · simp only [leadB, length_emit, hlen, List.length_map, List.length_finRange]; ring
  · simp only [boolInterp, leadV, List.any_map, Function.comp_def, id]
    congr 2
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨q, -, hq⟩
      by_cases hqp : q < p
      · exact ⟨q, hqp, by simpa [hqp] using hq⟩
      · simp [hqp] at hq
    · rintro ⟨q, hqp, hq⟩
      exact ⟨q, List.mem_finRange q, by simp [hqp, hq]⟩

/-- The new stored vectors: `b'_{p,i} = (ℓ_p ∧ v_i) ∨ (¬ℓ_p ∧ b_{p,i})`, `1 + 3 r` gates per
slot. -/
def updB (b : Fin r → Fin r → Arg m) (l v : Fin r → Arg m) :
    Bld BoolOp m (Fin r → Fin r → Arg m) :=
  vecB (fun p gs =>
    let nl := emit BoolOp.not (l p) .const gs
    vecB (fun i gs =>
      let t₁ := emit BoolOp.and (l p) (v i) gs
      let t₂ := emit BoolOp.and nl.2 (b p i) t₁.1
      emit BoolOp.or t₁.2 t₂.2 t₂.1) .const nl.1) (fun _ => .const)

theorem updB_spec {b : Fin r → Fin r → Arg m} {l v : Fin r → Arg m}
    {Bv : (Fin m → Bool) → Fin r → Fin r → Bool} {L V : (Fin m → Bool) → Fin r → Bool}
    {gs : List (Gate BoolOp m)} (hb : ∀ p, VecDen gs (b p) (fun x => Bv x p))
    (hl : VecDen gs l L) (hv : VecDen gs v V) :
    gs <+: (updB b l v gs).1 ∧
      ∀ p, VecDen (updB b l v gs).1 ((updB b l v gs).2 p)
        (fun x i => (L x p && V x i) || (!L x p && Bv x p i)) := by
  have hinner : ∀ p gs', gs <+: gs' →
      let nl := emit BoolOp.not (l p) .const gs'
      gs' <+: (vecB (fun i gs => let t₁ := emit BoolOp.and (l p) (v i) gs
          let t₂ := emit BoolOp.and nl.2 (b p i) t₁.1
          emit BoolOp.or t₁.2 t₂.2 t₂.1) .const nl.1).1 ∧
        VecDen (vecB (fun i gs => let t₁ := emit BoolOp.and (l p) (v i) gs
          let t₂ := emit BoolOp.and nl.2 (b p i) t₁.1
          emit BoolOp.or t₁.2 t₂.2 t₂.1) .const nl.1).1
          (vecB (fun i gs => let t₁ := emit BoolOp.and (l p) (v i) gs
          let t₂ := emit BoolOp.and nl.2 (b p i) t₁.1
          emit BoolOp.or t₁.2 t₂.2 t₂.1) .const nl.1).2
          (fun x i => (L x p && V x i) || (!L x p && Bv x p i)) := by
    intro p gs' h
    have hnl := den_emit BoolOp.not ((hl p).mono h) (den_const gs')
    have pnl := isPrefix_emit BoolOp.not (l p) .const gs'
    obtain ⟨hp, hden⟩ := vecB_den (gs₀ := (emit BoolOp.not (l p) .const gs').1)
      (F := fun i x => (L x p && V x i) || (!L x p && Bv x p i)) (fun i gs'' h' => by
        have hhh := h.trans (pnl.trans h')
        have h₁ := den_emit BoolOp.and ((hl p).mono hhh) ((hv i).mono hhh)
        have p₁ := isPrefix_emit BoolOp.and (l p) (v i) gs''
        have h₂ := den_emit BoolOp.and ((hnl.mono h').mono p₁) (((hb p) i).mono (hhh.trans p₁))
        have h₃ := den_emit BoolOp.or (h₁.mono (isPrefix_emit _ _ _ _)) h₂
        exact ⟨(p₁.trans (isPrefix_emit _ _ _ _)).trans (isPrefix_emit _ _ _ _),
          h₃.congr fun x => rfl⟩)
    exact ⟨pnl.trans hp, hden⟩
  obtain ⟨hp, -, hQ⟩ := vecB_gen (bld := fun p gs =>
      let nl := emit BoolOp.not (l p) .const gs
      vecB (fun i gs =>
        let t₁ := emit BoolOp.and (l p) (v i) gs
        let t₂ := emit BoolOp.and nl.2 (b p i) t₁.1
        emit BoolOp.or t₁.2 t₂.2 t₂.1) .const nl.1) (fun _ => .const)
    (fun gs' => gs <+: gs') (fun gs' p w => VecDen gs' w
      (fun x i => (L x p && V x i) || (!L x p && Bv x p i)))
    (fun _ _ _ _ hp h => h.mono hp)
    (fun p gs' h => ⟨(hinner p gs' h).1, h.trans (hinner p gs' h).1, (hinner p gs' h).2⟩)
    gs (List.prefix_refl _)
  exact ⟨hp, hQ⟩

/-! Gate counts, structurally. -/

theorem orB_length (l : List (Arg m)) (gs : List (Gate BoolOp m)) :
    (orB l gs).1.length = gs.length + l.length := by
  induction l generalizing gs with
  | nil => simp [orB]
  | cons a l ih => simp [orB, length_emit, ih]; ring

theorem leadB_length (v : Fin r → Arg m) (p : Fin r) (gs : List (Gate BoolOp m)) :
    (leadB v p gs).1.length = gs.length + (r + 2) := by
  simp only [leadB, length_emit, orB_length, List.length_map, List.length_finRange]; ring

theorem updB_length (b : Fin r → Fin r → Arg m) (l v : Fin r → Arg m)
    (gs : List (Gate BoolOp m)) : (updB b l v gs).1.length = gs.length + (1 + 3 * r) * r := by
  simp only [updB, vecB]
  rw [mapB_length (c := 1 + 3 * r) (fun p gs' => by
    rw [mapB_length (c := 3) (fun i gs'' => by simp [length_emit]), length_emit]
    simp only [List.length_finRange]; ring)]
  simp only [List.length_finRange]

/-- One column: reduction, leading positions, occupied slots, stored vectors;
`9 r² + 5 r` gates. -/
def colStepB (A : Matrix (Fin r) (Fin m) (ZMod 2)) (st : (Fin r → Arg m) × (Fin r → Fin r → Arg m))
    (e : Fin m) : Bld BoolOp m ((Fin r → Arg m) × (Fin r → Fin r → Arg m)) := fun gs =>
  let p₁ := reduceB st.1 st.2 (List.finRange r) (colArg A e) gs
  let p₂ := vecB (fun p => leadB p₁.2 p) .const p₁.1
  let p₃ := vecB (fun p => emit BoolOp.or (st.1 p) (p₂.2 p)) .const p₂.1
  let p₄ := updB st.2 p₂.2 p₁.2 p₃.1
  (p₄.1, (p₃.2, p₄.2))

theorem colStepB_spec (A : Matrix (Fin r) (Fin m) (ZMod 2))
    {st : (Fin r → Arg m) × (Fin r → Fin r → Arg m)} {F : (Fin m → Bool) → ESt r}
    {gs : List (Gate BoolOp m)} (hst : StDen gs st F) (e : Fin m) :
    gs <+: (colStepB A st e gs).1 ∧
      (colStepB A st e gs).1.length = gs.length + (9 * r ^ 2 + 5 * r) ∧
      StDen (colStepB A st e gs).1 (colStepB A st e gs).2 (fun x => colStepV A (F x) e (x e)) := by
  obtain ⟨hp₁, hlen₁, hred⟩ := reduceB_spec (List.finRange r) hst (colArg_den A e gs)
  set p₁ := reduceB st.1 st.2 (List.finRange r) (colArg A e) gs
  obtain ⟨hp₂, hlead⟩ := vecB_den (gs₀ := p₁.1) (bld := fun p => leadB p₁.2 p)
    (F := fun p x => leadV ((List.finRange r).foldl (redStep (F x)) (colV A e (x e))) p)
    (fun p gs' h => ⟨(leadB_spec (hred.mono h) p).1, (leadB_spec (hred.mono h) p).2.2⟩)
  set p₂ := vecB (fun p => leadB p₁.2 p) .const p₁.1
  obtain ⟨hp₃, hflag⟩ := vecB_den (gs₀ := p₂.1) (bld := fun p => emit BoolOp.or (st.1 p) (p₂.2 p))
    (F := fun p x => (F x).1 p || leadV ((List.finRange r).foldl (redStep (F x))
      (colV A e (x e))) p)
    (fun p gs' h => ⟨isPrefix_emit _ _ _ _, (den_emit BoolOp.or
      ((hst.1 p).mono ((hp₁.trans hp₂).trans h)) ((hlead p).mono h)).congr fun x => rfl⟩)
  set p₃ := vecB (fun p => emit BoolOp.or (st.1 p) (p₂.2 p)) .const p₂.1
  have hpp := (hp₁.trans hp₂).trans hp₃
  obtain ⟨hp₄, hupd⟩ := updB_spec (fun p => (hst.2 p).mono hpp) (hlead.mono hp₃)
    ((hred.mono hp₂).mono hp₃)
  refine ⟨hpp.trans hp₄, ?_, ⟨hflag.mono hp₄, fun p => hupd p⟩⟩
  have hlen₂ : p₂.1.length = p₁.1.length + (r + 2) * r :=
    vecB_length .const (fun p gs' => leadB_length _ p gs') p₁.1
  have hlen₃ : p₃.1.length = p₂.1.length + 1 * r :=
    vecB_length .const (fun p gs' => length_emit _ _ _ gs') p₂.1
  show (updB st.2 p₂.2 p₁.2 p₃.1).1.length = _
  rw [updB_length, hlen₃, hlen₂, hlen₁, List.length_finRange]
  ring

/-- All columns, in order. -/
def elimB (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    List (Fin m) → (Fin r → Arg m) × (Fin r → Fin r → Arg m) →
      Bld BoolOp m ((Fin r → Arg m) × (Fin r → Fin r → Arg m))
  | [], st => fun gs => (gs, st)
  | e :: es, st => fun gs =>
    let q := colStepB A st e gs
    elimB A es q.2 q.1

theorem elimB_spec (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    ∀ (es : List (Fin m)) {st : (Fin r → Arg m) × (Fin r → Fin r → Arg m)}
      {F : (Fin m → Bool) → ESt r} {gs : List (Gate BoolOp m)}, StDen gs st F →
      gs <+: (elimB A es st gs).1 ∧
        (elimB A es st gs).1.length = gs.length + es.length * (9 * r ^ 2 + 5 * r) ∧
        StDen (elimB A es st gs).1 (elimB A es st gs).2
          (fun x => es.foldl (fun s e => colStepV A s e (x e)) (F x))
  | [], st, F, gs, hst => ⟨List.prefix_refl _, by simp [elimB], hst⟩
  | e :: es, st, F, gs, hst => by
    obtain ⟨hp, hlen, hden⟩ := colStepB_spec A hst e
    obtain ⟨hq, hlen', hden'⟩ := elimB_spec A es hden
    refine ⟨hp.trans hq, ?_, hden'⟩
    simp only [elimB, hlen', hlen, List.length_cons]; ring

/-- The binary count of the occupied slots: one ripple-carry increment of `W` bits per
slot. -/
def countB (W : ℕ) (f : Fin r → Arg m) : List (Fin r) → List (Arg m) → Bld BoolOp m (List (Arg m))
  | [], acc => fun gs => (gs, acc)
  | p :: ps, acc => fun gs =>
    let q := rcaB acc (List.replicate W .const) (f p) gs
    countB W f ps q.2.1 q.1

theorem ofNat_add_ofBool (W c : ℕ) (b : Bool) :
    BitVec.ofNat W c + BitVec.ofNat W 0 + BitVec.setWidth W (BitVec.ofBool b)
      = BitVec.ofNat W (c + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> simp [Nat.add_mod]

theorem countB_spec (W : ℕ) {f : Fin r → Arg m} {Fv : (Fin m → Bool) → Fin r → Bool} :
    ∀ (ps : List (Fin r)) {acc : List (Arg m)} {c : (Fin m → Bool) → ℕ}
      {gs : List (Gate BoolOp m)}, VecDen gs f Fv →
      BitRep W gs acc (fun x => BitVec.ofNat W (c x)) →
      gs <+: (countB W f ps acc gs).1 ∧
        (countB W f ps acc gs).1.length = gs.length + ps.length * (11 * W) ∧
        BitRep W (countB W f ps acc gs).1 (countB W f ps acc gs).2
          (fun x => BitVec.ofNat W (c x + (ps.filter (Fv x)).length))
  | [], acc, c, gs, _, hacc => ⟨List.prefix_refl _, by simp [countB],
      DenL.congr hacc fun x => by simp⟩
  | p :: ps, acc, c, gs, hf, hacc => by
    have hzero : DenL boolInterp gs (List.replicate W .const)
        (fun x => bitsOf (BitVec.ofNat W 0)) :=
      ⟨by simp [Arg.Valid], fun x => by
        show _ = bitsOf (0 : BitVec W)
        rw [bitsOf_zero]; simp [Arg.read, boolInterp]⟩
    obtain ⟨hp, hlen, hs, -⟩ := rcaB_spec hacc hzero (hf p)
    have hstep : BitRep W (rcaB acc (List.replicate W .const) (f p) gs).1
        (rcaB acc (List.replicate W .const) (f p) gs).2.1
        (fun x => BitVec.ofNat W (c x + (Fv x p).toNat)) :=
      hs.congr fun x => by rw [rcaV_bitsOf, ofNat_add_ofBool]
    obtain ⟨hq, hlen', hden⟩ := countB_spec W ps (hf.mono hp) hstep
    have hacc_len : acc.length = W := by
      rw [← hacc.length_eq (fun _ => false), length_bitsOf]
    refine ⟨hp.trans hq, ?_, hden.congr fun x => ?_⟩
    · show (countB W f ps (rcaB acc (List.replicate W .const) (f p) gs).2.1
        (rcaB acc (List.replicate W .const) (f p) gs).1).1.length = _
      rw [hlen', hlen, hacc_len, List.length_replicate, min_self, List.length_cons]
      ring
    · cases h : Fv x p
      · simp [h]
      · simp only [h, Bool.toNat_true, List.filter_cons_of_pos, List.length_cons]
        congr 2
        omega

/-- **The rank circuit of `A`.**  On the indicator vector of `S` it outputs, in binary, the
number of occupied slots after the elimination. -/
def binaryRankCircuit (A : Matrix (Fin r) (Fin m) (ZMod 2)) : Circuit BoolOp m :=
  let p := elimB A (List.finRange m) (fun _ => .const, fun _ _ => .const) []
  let q := countB (Nat.size r) p.2.1 (List.finRange r) (List.replicate (Nat.size r) .const) p.1
  ⟨q.1, q.2⟩

theorem filter_finRange_length (P : Fin r → Bool) :
    ((List.finRange r).filter P).length = (univ.filter fun p => P p = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange r).filter _)]
  congr 1
  ext p
  simp

/-- **The rank circuit computes the rank.** -/
theorem binaryRankCircuit_spec (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    (binaryRankCircuit A).size = m * (9 * r ^ 2 + 5 * r) + r * (11 * Nat.size r) ∧
      ∀ S : Finset (Fin m), bitsVal ((binaryRankCircuit A).eval boolInterp (indicator S))
        = (flagSet (elimV A (indicator S))).card := by
  have hinit : StDen ([] : List (Gate BoolOp m)) (fun _ => .const, fun _ _ => .const)
      (fun _ => (initV : ESt r)) :=
    ⟨fun p => (den_const _).congr fun x => rfl, fun p i => (den_const _).congr fun x => rfl⟩
  obtain ⟨-, hlen, hden⟩ := elimB_spec A (List.finRange m) hinit
  set p := elimB A (List.finRange m) (fun _ => .const, fun _ _ => .const) []
  have hacc : BitRep (Nat.size r) p.1 (List.replicate (Nat.size r) .const)
      (fun _ => BitVec.ofNat (Nat.size r) 0) :=
    ⟨by simp [Arg.Valid], fun x => by
      show _ = bitsOf (0 : BitVec (Nat.size r))
      rw [bitsOf_zero]
      simp [Arg.read, boolInterp]⟩
  obtain ⟨-, hlen', hcnt⟩ := countB_spec (Nat.size r) (List.finRange r) hden.1 hacc
  refine ⟨?_, fun S => ?_⟩
  · show (countB (Nat.size r) p.2.1 (List.finRange r) (List.replicate (Nat.size r) .const)
      p.1).1.length = _
    rw [hlen', hlen, List.length_nil, zero_add, List.length_finRange, List.length_finRange]
  · have h := hcnt.2 (indicator S)
    simp only [Circuit.eval, binaryRankCircuit]
    rw [h, bitsVal_bitsOf, BitVec.toNat_ofNat, zero_add, filter_finRange_length]
    apply Nat.mod_eq_of_lt
    calc (univ.filter fun q => (elimV A (indicator S)).1 q = true).card
        ≤ r := (Finset.card_filter_le _ _).trans (by simp)
      _ < 2 ^ Nat.size r := Nat.lt_size_self r

end Circuit2

/-! ### Corollary C -/

/-- **The rank circuit computes the rank of the binary matroid**, in binary. -/
theorem binaryRankCircuit_rank (A : Matrix (Fin r) (Fin m) (ZMod 2)) (S : Finset (Fin m)) :
    (bitsVal ((binaryRankCircuit A).eval boolInterp (indicator S)) : ℕ∞)
      = (binaryMatroid A).eRk (S : Set (Fin m)) := by
  rw [(binaryRankCircuit_spec A).2 S, card_flagSet_elimV, eRk_binaryMatroid]

theorem binaryRankCircuit_size (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    (binaryRankCircuit A).size = m * (9 * r ^ 2 + 5 * r) + r * (11 * Nat.size r) :=
  (binaryRankCircuit_spec A).1

/-- **Corollary C, binary matroids.**  For every matrix `A ∈ GF(2)^{r × m}`, maximum-weight
bases of the binary matroid of `A` are computed at every `w ∈ ℝ^m` by a signed tropical
circuit of size at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`, where
`s = m (9 r² + 5 r) + 11 r ⌈log₂(r+1)⌉` is the size of the rank circuit and
`L = ⌈log₂(k+1)⌉` for the rank `k`. -/
theorem corollaryC_binary (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3 * m * (m * (9 * r ^ 2 + 5 * r) + r * (11 * Nat.size r))
          + m * Nat.size (rank (binaryMatroid A)) + 9 * m ^ 2 + 4 * m
          + 4 * Nat.size (rank (binaryMatroid A)) + 1 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (binaryMatroid A) w] := by
  have h := theoremA (binaryMatroid A) (binaryMatroid_E A) (binaryRankCircuit A)
    (binaryRankCircuit_rank A)
  rwa [binaryRankCircuit_size] at h

/-- The rank of a binary matroid with `r` rows is at most `r`. -/
theorem rank_binaryMatroid_le (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    rank (binaryMatroid A) ≤ r := by
  rw [← rk_univ _ (binaryMatroid_E A)]
  have h := eRk_binaryMatroid A univ
  rw [← coe_rk] at h
  have h2 : finrank (ZMod 2) (span (ZMod 2) (colZ A '' ((univ : Finset (Fin m)) : Set (Fin m))))
      ≤ r := (Submodule.finrank_le _).trans (by simp)
  have h3 : rk (binaryMatroid A) univ
      = finrank (ZMod 2) (span (ZMod 2) (colZ A '' ((univ : Finset (Fin m)) : Set (Fin m)))) := by
    exact_mod_cast h
  omega

/-- **Corollary C, binary matroids, as a polynomial**: at most `100 (m+1)² (r+1)²` gates. -/
theorem corollaryC_binary_poly (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    ∃ C : Circuit STOp m, C.size ≤ 100 * (m + 1) ^ 2 * (r + 1) ^ 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (binaryMatroid A) w] := by
  obtain ⟨C, hC, heval⟩ := corollaryC_binary A
  refine ⟨C, hC.trans ?_, heval⟩
  have hsr : Nat.size r ≤ r := Nat.size_le.2 Nat.lt_two_pow_self
  have hsk : Nat.size (rank (binaryMatroid A)) ≤ r :=
    (Nat.size_le.2 Nat.lt_two_pow_self).trans (rank_binaryMatroid_le A)
  have h1 : 3 * m * (m * (9 * r ^ 2 + 5 * r) + r * (11 * Nat.size r))
      ≤ 3 * m * (m * (9 * r ^ 2 + 5 * r) + r * (11 * r)) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ hsr)) _)
  have h2 : m * Nat.size (rank (binaryMatroid A)) ≤ m * r := Nat.mul_le_mul_left _ hsk
  have h3 : 3 * m * (m * (9 * r ^ 2 + 5 * r) + r * (11 * r)) + m * r + 9 * m ^ 2 + 4 * m
      + 4 * r + 1 ≤ 100 * (m + 1) ^ 2 * (r + 1) ^ 2 := by
    nlinarith [Nat.zero_le (m * r), Nat.zero_le (m * m * r * r), Nat.zero_le (m * m * r),
      Nat.zero_le (m * r * r), Nat.zero_le (m * m), Nat.zero_le (r * r)]
  omega

end SignedTropical
