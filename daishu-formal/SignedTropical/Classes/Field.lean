import SignedTropical.Binary

/-!
# Matroids represented over a finite field

`greedy_intersection.tex`, Corollary `cor:classes`, item 2, for matroids represented over a
finite field.

1. **The column matroid** of a matrix `A ∈ K^{r × m}` over a field `K` (`colMatroid`) and
   **elimination without branching** (`elimK`, the number of occupied slots is the rank,
   `card_occ_elimK`) are in `Elimination.lean`; over `GF(2)` the column matroid is the binary
   matroid of `Binary.lean`, by definition.
2. **One-hot codes.**  A field element is carried by `q = |K|` wires, exactly one of them
   `true` (`OH`).  Every binary operation of `K` costs `2 q²` gates (`op2B`), inversion is a
   permutation of the wires (`OH.inv`), and masking and selection cost `q` and `3 q` gates.
3. **The rank circuit** (`fieldRankCircuit`) runs the elimination on one-hot codes and counts
   the occupied slots in binary.  It has
   `m (6 q² r² + 3 q r² + r² + q r + 6 r + 1) + 11 r ⌈log₂(r+1)⌉ + 1` gates, at most
   `8 q² (m+1) (r+1)²` (`fieldRankCircuit_spec`, `fieldSize_le`), and it outputs the rank
   (`fieldRankCircuit_rank`, `field_rankCircuit`).
4. **Theorem A** for these matroids (`theoremA_field`): a signed tropical circuit for `h_M`
   with at most `25 q² (m+1)² (r+1)²` gates; for `q = 2` this is the bound
   `100 (m+1)² (r+1)²` of `corollaryC_binary_poly`.
-/

open Finset Module Submodule

namespace SignedTropical.Classes

variable {K : Type} [Field K] {r m n : ℕ}

/-! ### One-hot codes -/

section OneHot

variable {α β γ : Type}

/-- `mapB` with a cost that depends on the element. -/
theorem mapB_length_sum {Op β γ : Type} {b : β → Bld Op n γ} (cost : β → ℕ)
    (hc : ∀ a gs, (b a gs).1.length = gs.length + cost a) :
    ∀ (l : List β) (gs : List (Gate Op n)),
      (mapB b l gs).1.length = gs.length + (l.map cost).sum
  | [], gs => by simp [mapB]
  | a :: l, gs => by
    simp only [mapB, mapB_length_sum cost hc l, hc, List.map_cons, List.sum_cons]; ring

/-- Splitting a list by the value of `f`. -/
theorem sum_length_filter [Fintype γ] [DecidableEq γ] (f : α → γ) :
    ∀ L : List α, ∑ c, (L.filter fun a => f a = c).length = L.length
  | [] => by simp
  | a :: L => by
    have h : ∀ c, ((a :: L).filter fun a => f a = c).length
        = (if f a = c then 1 else 0) + (L.filter fun a => f a = c).length := by
      intro c
      by_cases hc : f a = c
      · simp [hc]; ring
      · simp [hc]
    rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_add_distrib, sum_length_filter f L,
      Finset.sum_ite_eq]
    simp; ring

/-- `u` is a one-hot code of `U`: operand `u a` carries `[U x = a]`. -/
def OH [DecidableEq α] (gs : List (Gate BoolOp m)) (u : α → Arg m) (U : (Fin m → Bool) → α) :
    Prop :=
  ∀ a, Den boolInterp gs (u a) (fun x => decide (U x = a))

theorem OH.mono [DecidableEq α] {gs gs' : List (Gate BoolOp m)} {u : α → Arg m}
    {U : (Fin m → Bool) → α} (h : OH gs u U) (hp : gs <+: gs') : OH gs' u U :=
  fun a => (h a).mono hp

/-- One operand per element of a finite type, built in a fixed order. -/
noncomputable def perB [Fintype α] (bld : α → Bld BoolOp m (Arg m)) : Bld BoolOp m (α → Arg m) :=
  fun gs =>
    let p := vecB (fun j => bld ((Fintype.equivFin α).symm j)) .const gs
    (p.1, fun a => p.2 (Fintype.equivFin α a))

theorem perB_spec [Fintype α] {bld : α → Bld BoolOp m (Arg m)} {gs₀ : List (Gate BoolOp m)}
    {F : α → (Fin m → Bool) → Bool}
    (hb : ∀ a gs, gs₀ <+: gs →
      gs <+: (bld a gs).1 ∧ Den boolInterp (bld a gs).1 (bld a gs).2 (F a)) :
    gs₀ <+: (perB bld gs₀).1 ∧ ∀ a, Den boolInterp (perB bld gs₀).1 ((perB bld gs₀).2 a) (F a) := by
  obtain ⟨hp, hden⟩ := vecB_den (gs₀ := gs₀) (bld := fun j => bld ((Fintype.equivFin α).symm j))
    (F := fun j => F ((Fintype.equivFin α).symm j)) (fun j gs h => hb _ gs h)
  exact ⟨hp, fun a => (hden (Fintype.equivFin α a)).congr fun x => by simp⟩

theorem perB_length [Fintype α] {bld : α → Bld BoolOp m (Arg m)} (cost : α → ℕ)
    (hc : ∀ a gs, (bld a gs).1.length = gs.length + cost a) (gs : List (Gate BoolOp m)) :
    (perB bld gs).1.length = gs.length + ∑ a, cost a := by
  show (mapB _ (List.finRange _) gs).1.length = _
  rw [mapB_length_sum (fun j => cost ((Fintype.equivFin α).symm j)) (fun j gs => hc _ gs),
    ← Fin.sum_univ_def, Equiv.sum_comp (Fintype.equivFin α).symm cost]

/-- `⋁ⱼ (aⱼ ∧ bⱼ)` over a list of operand pairs, two gates per pair. -/
def orAndB : List (Arg m × Arg m) → Bld BoolOp m (Arg m)
  | [] => fun gs => (gs, .const)
  | ab :: l => fun gs =>
    let p := emit BoolOp.and ab.1 ab.2 gs
    let q := orAndB l p.1
    emit BoolOp.or p.2 q.2 q.1

theorem orAndB_length :
    ∀ (l : List (Arg m × Arg m)) (gs : List (Gate BoolOp m)),
      (orAndB l gs).1.length = gs.length + 2 * l.length
  | [], gs => by simp [orAndB]
  | ab :: l, gs => by
    simp only [orAndB, length_emit, orAndB_length l, List.length_cons]; ring

theorem orAndB_spec [DecidableEq α] [DecidableEq β] {u : α → Arg m} {v : β → Arg m}
    {U : (Fin m → Bool) → α} {V : (Fin m → Bool) → β} :
    ∀ (L : List (α × β)) {gs : List (Gate BoolOp m)}, OH gs u U → OH gs v V →
      gs <+: (orAndB (L.map fun ab => (u ab.1, v ab.2)) gs).1 ∧
        Den boolInterp (orAndB (L.map fun ab => (u ab.1, v ab.2)) gs).1
          (orAndB (L.map fun ab => (u ab.1, v ab.2)) gs).2 (fun x => decide ((U x, V x) ∈ L))
  | [], gs, _, _ => ⟨List.prefix_refl _, (den_const gs).congr fun x => by simp [boolInterp]⟩
  | ab :: L, gs, hu, hv => by
    have h₁ := den_emit BoolOp.and (hu ab.1) (hv ab.2)
    have p₁ := isPrefix_emit BoolOp.and (u ab.1) (v ab.2) gs
    obtain ⟨p₂, h₂⟩ := orAndB_spec L (hu.mono p₁) (hv.mono p₁)
    have h₃ := den_emit BoolOp.or (h₁.mono p₂) h₂
    refine ⟨(p₁.trans p₂).trans (isPrefix_emit _ _ _ _), h₃.congr fun x => ?_⟩
    simp [boolInterp, Prod.ext_iff]

/-- **A binary operation on one-hot codes**: output `c` is the disjunction of `u a ∧ v b` over
the pairs with `g a b = c`. -/
noncomputable def op2B [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ] (g : α → β → γ)
    (u : α → Arg m) (v : β → Arg m) : Bld BoolOp m (γ → Arg m) :=
  perB fun c => orAndB ((((univ : Finset (α × β)).toList.filter fun ab => g ab.1 ab.2 = c)).map
    fun ab => (u ab.1, v ab.2))

theorem op2B_spec [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] {g : α → β → γ} {u : α → Arg m} {v : β → Arg m} {U : (Fin m → Bool) → α}
    {V : (Fin m → Bool) → β} {gs : List (Gate BoolOp m)} (hu : OH gs u U) (hv : OH gs v V) :
    gs <+: (op2B g u v gs).1 ∧ OH (op2B g u v gs).1 (op2B g u v gs).2 fun x => g (U x) (V x) :=
  perB_spec fun c gs' h => by
    obtain ⟨hp, hd⟩ := orAndB_spec _ (hu.mono h) (hv.mono h)
    exact ⟨hp, hd.congr fun x => by simp⟩

/-- A binary operation costs `2 |α| |β|` gates. -/
theorem op2B_length [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ] (g : α → β → γ)
    (u : α → Arg m) (v : β → Arg m) (gs : List (Gate BoolOp m)) :
    (op2B g u v gs).1.length = gs.length + 2 * (Fintype.card α * Fintype.card β) := by
  rw [op2B, perB_length (fun c => 2 * (((univ : Finset (α × β)).toList.filter
    fun ab => g ab.1 ab.2 = c)).length) (fun c gs => by rw [orAndB_length, List.length_map]),
    ← Finset.mul_sum, sum_length_filter, Finset.length_toList, Finset.card_univ,
    Fintype.card_prod]

/-- Selection `if l then u else b`, from `l`, `nl = ¬l` and two codes: three gates per
element. -/
noncomputable def muxB [Fintype α] (l nl : Arg m) (u b : α → Arg m) : Bld BoolOp m (α → Arg m) :=
  perB fun a gs =>
    let p₁ := emit BoolOp.and l (u a) gs
    let p₂ := emit BoolOp.and nl (b a) p₁.1
    emit BoolOp.or p₁.2 p₂.2 p₂.1

theorem muxB_spec [Fintype α] [DecidableEq α] {l nl : Arg m} {u b : α → Arg m}
    {L : (Fin m → Bool) → Bool} {U B : (Fin m → Bool) → α} {gs : List (Gate BoolOp m)}
    (hl : Den boolInterp gs l L) (hnl : Den boolInterp gs nl fun x => !L x) (hu : OH gs u U)
    (hb : OH gs b B) :
    gs <+: (muxB l nl u b gs).1 ∧
      OH (muxB l nl u b gs).1 (muxB l nl u b gs).2 fun x => if L x then U x else B x :=
  perB_spec fun a gs' h => by
    have p₁ := isPrefix_emit BoolOp.and l (u a) gs'
    have h₁ := den_emit BoolOp.and (hl.mono h) ((hu a).mono h)
    have h₂ := den_emit BoolOp.and ((hnl.mono h).mono p₁) (((hb a).mono h).mono p₁)
    have h₃ := den_emit BoolOp.or (h₁.mono (isPrefix_emit _ _ _ _)) h₂
    refine ⟨p₁.trans ((isPrefix_emit _ _ _ _).trans (isPrefix_emit _ _ _ _)), h₃.congr fun x => ?_⟩
    cases hL : L x <;> simp [boolInterp, hL]

theorem muxB_length [Fintype α] (l nl : Arg m) (u b : α → Arg m) (gs : List (Gate BoolOp m)) :
    (muxB l nl u b gs).1.length = gs.length + 3 * Fintype.card α := by
  rw [muxB, perB_length (fun _ => 3) (fun a gs => by simp [length_emit])]
  simp [mul_comm]

end OneHot

/-! ### The rank circuit -/

section Circuit

variable [Fintype K] [DecidableEq K]

omit [Fintype K] in
theorem OH.inv {gs : List (Gate BoolOp m)} {u : K → Arg m} {U : (Fin m → Bool) → K}
    (h : OH gs u U) : OH gs (fun a => u a⁻¹) fun x => (U x)⁻¹ :=
  fun a => (h a⁻¹).congr fun _ => decide_eq_decide.2 inv_eq_iff_eq_inv.symm

/-- Masking `if f then v else 0`, from `f`, `nf = ¬f` and the code of `v`: one gate per
element. -/
noncomputable def maskB (f nf : Arg m) (v : K → Arg m) : Bld BoolOp m (K → Arg m) :=
  perB fun a => if a = 0 then emit BoolOp.or nf (v 0) else emit BoolOp.and f (v a)

theorem maskB_spec {f nf : Arg m} {v : K → Arg m} {F : (Fin m → Bool) → Bool}
    {V : (Fin m → Bool) → K} {gs : List (Gate BoolOp m)} (hf : Den boolInterp gs f F)
    (hnf : Den boolInterp gs nf fun x => !F x) (hv : OH gs v V) :
    gs <+: (maskB f nf v gs).1 ∧
      OH (maskB f nf v gs).1 (maskB f nf v gs).2 fun x => if F x then V x else 0 :=
  perB_spec fun a gs' h => by
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl]
      refine ⟨isPrefix_emit _ _ _ _,
        (den_emit BoolOp.or (hnf.mono h) ((hv 0).mono h)).congr fun x => ?_⟩
      by_cases hF : F x = true <;> simp [boolInterp, hF]
    · rw [if_neg ha]
      refine ⟨isPrefix_emit _ _ _ _,
        (den_emit BoolOp.and (hf.mono h) ((hv a).mono h)).congr fun x => ?_⟩
      by_cases hF : F x = true <;> simp [boolInterp, hF, Ne.symm ha]

theorem maskB_length (f nf : Arg m) (v : K → Arg m) (gs : List (Gate BoolOp m)) :
    (maskB f nf v gs).1.length = gs.length + Fintype.card K := by
  rw [maskB, perB_length (fun _ => 1) (fun a gs => by split_ifs <;> exact length_emit _ _ _ _)]
  simp

/-- The one-hot code of `x_e A_{i,e}`, read from operands `t = 1` and `nx = ¬x_e`; no
gates. -/
def colOH (A : Matrix (Fin r) (Fin m) K) (t nx : Arg m) (e : Fin m) (i : Fin r) (a : K) : Arg m :=
  if a = A i e then (if a = 0 then t else .input e) else (if a = 0 then nx else .const)

omit [Fintype K] in
theorem colOH_spec (A : Matrix (Fin r) (Fin m) K) {t nx : Arg m} {e : Fin m}
    {gs : List (Gate BoolOp m)} (ht : Den boolInterp gs t fun _ => true)
    (hnx : Den boolInterp gs nx fun x => !x e) (i : Fin r) :
    OH gs (colOH A t nx e i) fun x => colValK A e (x e) i := by
  intro a
  unfold colOH
  split_ifs with h₁ h₂ h₂
  · subst h₂
    exact ht.congr fun x => by simp [colValK, ← h₁]
  · exact (den_input gs e).congr fun x => by
      cases hx : x e <;> simp [colValK, hx, ← h₁, Ne.symm h₂]
  · subst h₂
    exact hnx.congr fun x => by cases hx : x e <;> simp [colValK, hx, Ne.symm h₁]
  · exact (den_const gs).congr fun x => by
      cases hx : x e <;> simp [colValK, boolInterp, hx, Ne.symm h₁, Ne.symm h₂]

/-- One-hot codes of a vector. -/
def OHV (gs : List (Gate BoolOp m)) (v : Fin r → K → Arg m) (V : (Fin m → Bool) → Fin r → K) :
    Prop :=
  ∀ i, OH gs (v i) fun x => V x i

omit [Field K] [Fintype K] in
theorem OHV.mono {gs gs' : List (Gate BoolOp m)} {v : Fin r → K → Arg m}
    {V : (Fin m → Bool) → Fin r → K} (h : OHV gs v V) (hp : gs <+: gs') : OHV gs' v V :=
  fun i => (h i).mono hp

/-- The state operands carry the elimination state. -/
def StKDen (gs : List (Gate BoolOp m)) (st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m))
    (F : (Fin m → Bool) → StK K r) : Prop :=
  VecDen gs st.1 (fun x => (F x).1) ∧ ∀ p, OHV gs (st.2 p) fun x => (F x).2 p

omit [Field K] [Fintype K] in
theorem StKDen.mono {gs gs' : List (Gate BoolOp m)}
    {st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)} {F : (Fin m → Bool) → StK K r}
    (h : StKDen gs st F) (hp : gs <+: gs') : StKDen gs' st F :=
  ⟨h.1.mono hp, fun p => (h.2 p).mono hp⟩

omit [Field K] [Fintype K] in
/-- A vector of one-hot codes, one builder per entry. -/
theorem vecB_ohv {bld : Fin r → Bld BoolOp m (K → Arg m)} {gs₀ : List (Gate BoolOp m)}
    {F : (Fin m → Bool) → Fin r → K}
    (hb : ∀ i gs, gs₀ <+: gs → gs <+: (bld i gs).1 ∧ OH (bld i gs).1 (bld i gs).2 fun x => F x i) :
    gs₀ <+: (vecB bld (fun _ => .const) gs₀).1 ∧
      OHV (vecB bld (fun _ => .const) gs₀).1 (vecB bld (fun _ => .const) gs₀).2 F := by
  obtain ⟨hp, -, hQ⟩ := vecB_gen (bld := bld) (fun _ => .const) (fun gs => gs₀ <+: gs)
    (fun gs i w => OH gs w fun x => F x i) (fun _ _ _ _ hp h => h.mono hp)
    (fun i gs h => ⟨(hb i gs h).1, h.trans (hb i gs h).1, (hb i gs h).2⟩) gs₀ (List.prefix_refl _)
  exact ⟨hp, hQ⟩

/-- `vᵢ - c bᵢ` for every `i`, from the codes of `c`, `b` and `v`: `4 r q²` gates. -/
noncomputable def axpyKB (c : K → Arg m) (b v : Fin r → K → Arg m) :
    Bld BoolOp m (Fin r → K → Arg m) :=
  vecB (fun i gs => let t := op2B (· * ·) c (b i) gs; op2B (· - ·) (v i) t.2 t.1)
    (fun _ => .const)

theorem axpyKB_spec {c : K → Arg m} {b v : Fin r → K → Arg m} {C : (Fin m → Bool) → K}
    {Bv V : (Fin m → Bool) → Fin r → K} {gs : List (Gate BoolOp m)} (hc : OH gs c C)
    (hb : OHV gs b Bv) (hv : OHV gs v V) :
    gs <+: (axpyKB c b v gs).1 ∧
      OHV (axpyKB c b v gs).1 (axpyKB c b v gs).2 fun x i => V x i - C x * Bv x i :=
  vecB_ohv fun i gs' h => by
    obtain ⟨pt, ht⟩ := op2B_spec (g := (· * ·)) (hc.mono h) ((hb i).mono h)
    obtain ⟨pr, hr⟩ := op2B_spec (g := (· - ·)) (((hv i).mono h).mono pt) ht
    exact ⟨pt.trans pr, hr⟩

theorem axpyKB_length (c : K → Arg m) (b v : Fin r → K → Arg m) (gs : List (Gate BoolOp m)) :
    (axpyKB c b v gs).1.length = gs.length + 4 * Fintype.card K ^ 2 * r := by
  rw [axpyKB, vecB_length (c := 4 * Fintype.card K ^ 2) _ (fun i gs => by
    simp only [op2B_length]; ring)]

/-- Reduction at slot `p`: `1 + q + 4 r q²` gates, `q = |K|`. -/
noncomputable def redKB (f : Fin r → Arg m) (b : Fin r → Fin r → K → Arg m)
    (v : Fin r → K → Arg m) (p : Fin r) : Bld BoolOp m (Fin r → K → Arg m) := fun gs =>
  let nf := emit BoolOp.not (f p) .const gs
  let c := maskB (f p) nf.2 (v p) nf.1
  axpyKB c.2 (b p) v c.1

theorem redKB_spec {st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)}
    {F : (Fin m → Bool) → StK K r} {v : Fin r → K → Arg m} {V : (Fin m → Bool) → Fin r → K}
    {gs : List (Gate BoolOp m)} (hst : StKDen gs st F) (hv : OHV gs v V) (p : Fin r) :
    gs <+: (redKB st.1 st.2 v p gs).1 ∧
      OHV (redKB st.1 st.2 v p gs).1 (redKB st.1 st.2 v p gs).2
        fun x => redStepK (F x) (V x) p := by
  have pn := isPrefix_emit BoolOp.not (st.1 p) .const gs
  have hnf := den_emit BoolOp.not (hst.1 p) (den_const (I := boolInterp) gs)
  obtain ⟨pc, hc⟩ := maskB_spec ((hst.1 p).mono pn) hnf ((hv p).mono pn)
  obtain ⟨pa, ha⟩ := axpyKB_spec hc ((hst.2 p).mono (pn.trans pc)) ((hv.mono pn).mono pc)
  exact ⟨(pn.trans pc).trans pa, ha⟩

theorem redKB_length (f : Fin r → Arg m) (b : Fin r → Fin r → K → Arg m) (v : Fin r → K → Arg m)
    (p : Fin r) (gs : List (Gate BoolOp m)) :
    (redKB f b v p gs).1.length
      = gs.length + (1 + Fintype.card K + r * (4 * Fintype.card K ^ 2)) := by
  simp only [redKB]
  rw [axpyKB_length, maskB_length, length_emit]
  ring

/-- Reduction at the slots `ps`, in order. -/
noncomputable def reduceKB (f : Fin r → Arg m) (b : Fin r → Fin r → K → Arg m) :
    List (Fin r) → (Fin r → K → Arg m) → Bld BoolOp m (Fin r → K → Arg m)
  | [], v => fun gs => (gs, v)
  | p :: ps, v => fun gs =>
    let q := redKB f b v p gs
    reduceKB f b ps q.2 q.1

theorem reduceKB_spec {st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)}
    {F : (Fin m → Bool) → StK K r} :
    ∀ (ps : List (Fin r)) {v : Fin r → K → Arg m} {V : (Fin m → Bool) → Fin r → K}
      {gs : List (Gate BoolOp m)}, StKDen gs st F → OHV gs v V →
      gs <+: (reduceKB st.1 st.2 ps v gs).1 ∧
        OHV (reduceKB st.1 st.2 ps v gs).1 (reduceKB st.1 st.2 ps v gs).2
          fun x => ps.foldl (redStepK (F x)) (V x)
  | [], v, V, gs, _, hv => ⟨List.prefix_refl _, hv⟩
  | p :: ps, v, V, gs, hst, hv => by
    obtain ⟨hp, hden⟩ := redKB_spec hst hv p
    obtain ⟨hq, hden'⟩ := reduceKB_spec ps (hst.mono hp) hden
    exact ⟨hp.trans hq, hden'⟩

theorem reduceKB_length (f : Fin r → Arg m) (b : Fin r → Fin r → K → Arg m) :
    ∀ (ps : List (Fin r)) (v : Fin r → K → Arg m) (gs : List (Gate BoolOp m)),
      (reduceKB f b ps v gs).1.length
        = gs.length + ps.length * (1 + Fintype.card K + r * (4 * Fintype.card K ^ 2))
  | [], v, gs => by simp [reduceKB]
  | p :: ps, v, gs => by
    simp only [reduceKB, reduceKB_length f b ps, redKB_length, List.length_cons]; ring

/-- The new stored vectors, `b'_{p,i} = if ℓ_p then v_i v_p⁻¹ else b_{p,i}`:
`1 + r (2 q² + 3 q)` gates per slot. -/
noncomputable def updKB (b : Fin r → Fin r → K → Arg m) (l : Fin r → Arg m)
    (v : Fin r → K → Arg m) : Bld BoolOp m (Fin r → Fin r → K → Arg m) :=
  vecB (fun p gs =>
    let nl := emit BoolOp.not (l p) .const gs
    vecB (fun i gs =>
      let u := op2B (· * ·) (v i) (fun a => v p a⁻¹) gs
      muxB (l p) nl.2 u.2 (b p i) u.1) (fun _ => .const) nl.1) (fun _ _ => .const)

theorem updKB_spec {b : Fin r → Fin r → K → Arg m} {l : Fin r → Arg m} {v : Fin r → K → Arg m}
    {Bv : (Fin m → Bool) → Fin r → Fin r → K} {L : (Fin m → Bool) → Fin r → Bool}
    {V : (Fin m → Bool) → Fin r → K} {gs : List (Gate BoolOp m)}
    (hb : ∀ p, OHV gs (b p) fun x => Bv x p) (hl : VecDen gs l L) (hv : OHV gs v V) :
    gs <+: (updKB b l v gs).1 ∧
      ∀ p, OHV (updKB b l v gs).1 ((updKB b l v gs).2 p)
        fun x i => if L x p then V x i * (V x p)⁻¹ else Bv x p i := by
  obtain ⟨hp, -, hQ⟩ := vecB_gen (bld := fun p gs =>
      let nl := emit BoolOp.not (l p) .const gs
      vecB (fun i gs =>
        let u := op2B (· * ·) (v i) (fun a => v p a⁻¹) gs
        muxB (l p) nl.2 u.2 (b p i) u.1) (fun _ => .const) nl.1) (fun _ _ => .const)
    (fun gs' => gs <+: gs')
    (fun gs' p w => OHV gs' w fun x i => if L x p then V x i * (V x p)⁻¹ else Bv x p i)
    (fun _ _ _ _ hp h => h.mono hp)
    (fun p gs' h => by
      have pnl := isPrefix_emit BoolOp.not (l p) .const gs'
      have hnl := den_emit BoolOp.not ((hl p).mono h) (den_const (I := boolInterp) gs')
      obtain ⟨pv, hden⟩ := vecB_ohv (gs₀ := (emit BoolOp.not (l p) .const gs').1)
        (F := fun x i => if L x p then V x i * (V x p)⁻¹ else Bv x p i) fun i gs'' h' => by
          have hh := h.trans (pnl.trans h')
          obtain ⟨pu, hu⟩ := op2B_spec (g := (· * ·)) ((hv i).mono hh) ((hv p).mono hh).inv
          obtain ⟨pm, hm⟩ := muxB_spec (((hl p).mono hh).mono pu) ((hnl.mono h').mono pu) hu
            (((hb p i).mono hh).mono pu)
          exact ⟨pu.trans pm, hm⟩
      exact ⟨pnl.trans pv, h.trans (pnl.trans pv), hden⟩)
    gs (List.prefix_refl _)
  exact ⟨hp, hQ⟩

theorem updKB_length (b : Fin r → Fin r → K → Arg m) (l : Fin r → Arg m) (v : Fin r → K → Arg m)
    (gs : List (Gate BoolOp m)) :
    (updKB b l v gs).1.length
      = gs.length + r * (1 + r * (2 * Fintype.card K ^ 2 + 3 * Fintype.card K)) := by
  simp only [updKB]
  rw [vecB_length (c := 1 + r * (2 * Fintype.card K ^ 2 + 3 * Fintype.card K)) _ (fun p gs => by
    rw [vecB_length (c := 2 * Fintype.card K ^ 2 + 3 * Fintype.card K) _ (fun i gs => by
      rw [muxB_length, op2B_length]; ring), length_emit]; ring)]
  ring

/-- Gates of one column step. -/
def colCostK (q r : ℕ) : ℕ := 6 * q ^ 2 * r ^ 2 + 3 * q * r ^ 2 + r ^ 2 + q * r + 6 * r + 1

/-- One column: the masked column, reduction, leading positions, occupied slots, stored
vectors; `colCostK q r` gates. -/
noncomputable def colStepKB (A : Matrix (Fin r) (Fin m) K) (t : Arg m)
    (st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)) (e : Fin m) :
    Bld BoolOp m ((Fin r → Arg m) × (Fin r → Fin r → K → Arg m)) := fun gs =>
  let p₀ := emit BoolOp.not (.input e) .const gs
  let p₁ := reduceKB st.1 st.2 (List.finRange r) (colOH A t p₀.2 e) p₀.1
  let p₂ := vecB (fun p => emit BoolOp.not (p₁.2 p 0) .const) .const p₁.1
  let p₃ := vecB (fun p => leadB p₂.2 p) .const p₂.1
  let p₄ := vecB (fun p => emit BoolOp.or (st.1 p) (p₃.2 p)) .const p₃.1
  let p₅ := updKB st.2 p₃.2 p₁.2 p₄.1
  (p₅.1, (p₄.2, p₅.2))

theorem colStepKB_spec (A : Matrix (Fin r) (Fin m) K) {t : Arg m}
    {st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)} {F : (Fin m → Bool) → StK K r}
    {gs : List (Gate BoolOp m)} (ht : Den boolInterp gs t fun _ => true) (hst : StKDen gs st F)
    (e : Fin m) :
    gs <+: (colStepKB A t st e gs).1 ∧
      StKDen (colStepKB A t st e gs).1 (colStepKB A t st e gs).2
        fun x => colStepK A (F x) e (x e) := by
  have p₀ := isPrefix_emit BoolOp.not (.input e) .const gs
  have hnx := den_emit BoolOp.not (den_input (I := boolInterp) gs e) (den_const gs)
  obtain ⟨hp₁, hred⟩ := reduceKB_spec (List.finRange r) (hst.mono p₀)
    (fun i => colOH_spec A (ht.mono p₀) hnx i)
  set p₁ := reduceKB st.1 st.2 (List.finRange r) (colOH A t (emit BoolOp.not (.input e) .const
    gs).2 e) (emit BoolOp.not (.input e) .const gs).1
  set V := fun x => (List.finRange r).foldl (redStepK (F x)) (colValK A e (x e))
  obtain ⟨hp₂, hnz⟩ := vecB_den (gs₀ := p₁.1) (bld := fun p => emit BoolOp.not (p₁.2 p 0) .const)
    (F := fun p x => nzK (V x) p)
    (fun p gs' h => ⟨isPrefix_emit _ _ _ _, (den_emit BoolOp.not ((hred p 0).mono h)
      (den_const gs')).congr fun x => rfl⟩)
  set p₂ := vecB (fun p => emit BoolOp.not (p₁.2 p 0) .const) .const p₁.1
  obtain ⟨hp₃, hlead⟩ := vecB_den (gs₀ := p₂.1) (bld := fun p => leadB p₂.2 p)
    (F := fun p x => leadV (nzK (V x)) p)
    (fun p gs' h => ⟨(leadB_spec (hnz.mono h) p).1, (leadB_spec (hnz.mono h) p).2.2⟩)
  set p₃ := vecB (fun p => leadB p₂.2 p) .const p₂.1
  obtain ⟨hp₄, hflag⟩ := vecB_den (gs₀ := p₃.1)
    (bld := fun p => emit BoolOp.or (st.1 p) (p₃.2 p))
    (F := fun p x => (F x).1 p || leadV (nzK (V x)) p)
    (fun p gs' h => ⟨isPrefix_emit _ _ _ _, (den_emit BoolOp.or
      ((hst.1 p).mono (((p₀.trans hp₁).trans hp₂).trans (hp₃.trans h))) ((hlead p).mono h)).congr
        fun x => rfl⟩)
  set p₄ := vecB (fun p => emit BoolOp.or (st.1 p) (p₃.2 p)) .const p₃.1
  have hpp := (((p₀.trans hp₁).trans hp₂).trans hp₃).trans hp₄
  obtain ⟨hp₅, hupd⟩ := updKB_spec (fun p => (hst.2 p).mono hpp) (hlead.mono hp₄)
    (((hred.mono hp₂).mono hp₃).mono hp₄)
  exact ⟨hpp.trans hp₅, hflag.mono hp₅, hupd⟩

theorem colStepKB_length (A : Matrix (Fin r) (Fin m) K) (t : Arg m)
    (st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)) (e : Fin m)
    (gs : List (Gate BoolOp m)) :
    (colStepKB A t st e gs).1.length = gs.length + colCostK (Fintype.card K) r := by
  simp only [colStepKB]
  rw [updKB_length, vecB_length (c := 1) _ (fun p gs => length_emit _ _ _ _),
    vecB_length (c := r + 2) _ (fun p gs => leadB_length _ p gs),
    vecB_length (c := 1) _ (fun p gs => length_emit _ _ _ _), reduceKB_length, length_emit,
    List.length_finRange, colCostK]
  ring

/-- All columns, in order. -/
noncomputable def elimKB (A : Matrix (Fin r) (Fin m) K) (t : Arg m) :
    List (Fin m) → (Fin r → Arg m) × (Fin r → Fin r → K → Arg m) →
      Bld BoolOp m ((Fin r → Arg m) × (Fin r → Fin r → K → Arg m))
  | [], st => fun gs => (gs, st)
  | e :: es, st => fun gs =>
    let q := colStepKB A t st e gs
    elimKB A t es q.2 q.1

theorem elimKB_spec (A : Matrix (Fin r) (Fin m) K) {t : Arg m} :
    ∀ (es : List (Fin m)) {st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m)}
      {F : (Fin m → Bool) → StK K r} {gs : List (Gate BoolOp m)},
      Den boolInterp gs t (fun _ => true) → StKDen gs st F →
      gs <+: (elimKB A t es st gs).1 ∧
        StKDen (elimKB A t es st gs).1 (elimKB A t es st gs).2
          fun x => es.foldl (fun s e => colStepK A s e (x e)) (F x)
  | [], st, F, gs, _, hst => ⟨List.prefix_refl _, hst⟩
  | e :: es, st, F, gs, ht, hst => by
    obtain ⟨hp, hden⟩ := colStepKB_spec A ht hst e
    obtain ⟨hq, hden'⟩ := elimKB_spec A es (ht.mono hp) hden
    exact ⟨hp.trans hq, hden'⟩

theorem elimKB_length (A : Matrix (Fin r) (Fin m) K) (t : Arg m) :
    ∀ (es : List (Fin m)) (st : (Fin r → Arg m) × (Fin r → Fin r → K → Arg m))
      (gs : List (Gate BoolOp m)),
      (elimKB A t es st gs).1.length = gs.length + es.length * colCostK (Fintype.card K) r
  | [], st, gs => by simp [elimKB]
  | e :: es, st, gs => by
    simp only [elimKB, elimKB_length A t es, colStepKB_length, List.length_cons]; ring

/-- **The rank circuit of `A`.**  On the indicator vector of `S` it outputs, in binary, the
number of occupied slots after the elimination. -/
noncomputable def fieldRankCircuit (A : Matrix (Fin r) (Fin m) K) : Circuit BoolOp m :=
  let p₀ := emit BoolOp.not (Arg.const : Arg m) .const []
  let p := elimKB A p₀.2 (List.finRange m)
    (fun _ => .const, fun _ _ a => if a = 0 then p₀.2 else .const) p₀.1
  let q := countB (Nat.size r) p.2.1 (List.finRange r) (List.replicate (Nat.size r) .const) p.1
  ⟨q.1, q.2⟩

/-- **The rank circuit counts the occupied slots**, and its size. -/
theorem fieldRankCircuit_spec (A : Matrix (Fin r) (Fin m) K) :
    (fieldRankCircuit A).size
        = m * colCostK (Fintype.card K) r + r * (11 * Nat.size r) + 1 ∧
      ∀ S : Finset (Fin m), bitsVal ((fieldRankCircuit A).eval boolInterp (indicator S))
        = (occ (elimK A (indicator S)).1).card := by
  set p₀ := emit BoolOp.not (Arg.const : Arg m) .const []
  have ht : Den boolInterp p₀.1 p₀.2 fun _ => true :=
    (den_emit BoolOp.not (den_const []) (den_const [])).congr fun _ => rfl
  have hinit : StKDen p₀.1 (fun _ => .const, fun _ _ a => if a = 0 then p₀.2 else .const)
      (fun _ => (initK : StK K r)) := by
    refine ⟨fun p => (den_const _).congr fun x => rfl, fun p i a => ?_⟩
    by_cases ha : a = 0
    · subst ha
      show Den boolInterp p₀.1 (if (0 : K) = 0 then p₀.2 else .const) _
      rw [if_pos rfl]
      exact ht.congr fun x => by simp [initK]
    · show Den boolInterp p₀.1 (if a = 0 then p₀.2 else .const) _
      rw [if_neg ha]
      exact (den_const _).congr fun x => by simp [initK, boolInterp, Ne.symm ha]
  obtain ⟨-, hden⟩ := elimKB_spec A (List.finRange m) ht hinit
  set p := elimKB A p₀.2 (List.finRange m)
    (fun _ => .const, fun _ _ a => if a = 0 then p₀.2 else .const) p₀.1
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
    rw [hlen', elimKB_length, List.length_finRange, List.length_finRange,
      show p₀.1.length = 1 from rfl]
    ring
  · have h := hcnt.2 (indicator S)
    simp only [Circuit.eval, fieldRankCircuit]
    rw [h, bitsVal_bitsOf, BitVec.toNat_ofNat, zero_add, filter_finRange_length]
    apply Nat.mod_eq_of_lt
    calc (univ.filter fun q => (elimK A (indicator S)).1 q = true).card
        ≤ r := (Finset.card_filter_le _ _).trans (by simp)
      _ < 2 ^ Nat.size r := Nat.lt_size_self r

/-- **The rank circuit computes the rank of the column matroid**, in binary. -/
theorem fieldRankCircuit_rank (A : Matrix (Fin r) (Fin m) K) (S : Finset (Fin m)) :
    (bitsVal ((fieldRankCircuit A).eval boolInterp (indicator S)) : ℕ∞)
      = (colMatroid A).eRk (S : Set (Fin m)) := by
  rw [(fieldRankCircuit_spec A).2 S, card_occ_elimK, eRk_colMatroid]

end Circuit

/-! ### Explicit sizes -/

/-- The rank circuit has at most `8 q² (m+1) (r+1)²` gates when `q ≥ 2`. -/
theorem fieldSize_le {q : ℕ} (hq : 2 ≤ q) (m r : ℕ) :
    m * colCostK q r + r * (11 * Nat.size r) + 1 ≤ 8 * q ^ 2 * (m + 1) * (r + 1) ^ 2 := by
  have hsr : Nat.size r ≤ r := Nat.size_le.2 Nat.lt_two_pow_self
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  calc m * colCostK (q + 2) r + r * (11 * Nat.size r) + 1
      ≤ m * colCostK (q + 2) r + r * (11 * r) + 1 := by gcongr
    _ ≤ 8 * (q + 2) ^ 2 * (m + 1) * (r + 1) ^ 2 := Nat.le.intro (k := m * (2 * q ^ 2 * r ^ 2
          + 16 * q ^ 2 * r + 8 * q ^ 2 + 5 * q * r ^ 2 + 63 * q * r + 32 * q + r ^ 2 + 56 * r
          + 31) + (8 * q ^ 2 * r ^ 2 + 16 * q ^ 2 * r + 8 * q ^ 2 + 32 * q * r ^ 2 + 64 * q * r
          + 32 * q + 21 * r ^ 2 + 64 * r + 31)) (by simp only [colCostK]; ring)

/-- The bound of Theorem A for the rank circuit is at most `25 q² (m+1)² (r+1)²` when `q ≥ 2`
and the rank `k` is at most `r`. -/
theorem theoremA_fieldSize_le {q : ℕ} (hq : 2 ≤ q) (m r k : ℕ) (hk : k ≤ r) :
    3 * m * (m * colCostK q r + r * (11 * Nat.size r) + 1) + m * Nat.size k + 9 * m ^ 2
      + 4 * m + 4 * Nat.size k + 1 ≤ 25 * q ^ 2 * (m + 1) ^ 2 * (r + 1) ^ 2 := by
  have hsr : Nat.size r ≤ r := Nat.size_le.2 Nat.lt_two_pow_self
  have hsk : Nat.size k ≤ r := (Nat.size_le.2 Nat.lt_two_pow_self).trans hk
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  calc 3 * m * (m * colCostK (q + 2) r + r * (11 * Nat.size r) + 1) + m * Nat.size k
        + 9 * m ^ 2 + 4 * m + 4 * Nat.size k + 1
      ≤ 3 * m * (m * colCostK (q + 2) r + r * (11 * r) + 1) + m * r + 9 * m ^ 2 + 4 * m
        + 4 * r + 1 := by gcongr
    _ ≤ 25 * (q + 2) ^ 2 * (m + 1) ^ 2 * (r + 1) ^ 2 := Nat.le.intro (k := m ^ 2 * (7 * q ^ 2
          * r ^ 2 + 50 * q ^ 2 * r + 25 * q ^ 2 + 19 * q * r ^ 2 + 197 * q * r + 100 * q
          + 7 * r ^ 2 + 176 * r + 88) + m * (50 * q ^ 2 * r ^ 2 + 100 * q ^ 2 * r + 50 * q ^ 2
          + 200 * q * r ^ 2 + 400 * q * r + 200 * q + 167 * r ^ 2 + 399 * r + 193)
          + (25 * q ^ 2 * r ^ 2 + 50 * q ^ 2 * r + 25 * q ^ 2 + 100 * q * r ^ 2 + 200 * q * r
          + 100 * q + 100 * r ^ 2 + 196 * r + 99)) (by simp only [colCostK]; ring)

/-! ### Matroids represented over a finite field -/

/-- The rank of the column matroid is at most the number of rows. -/
theorem rank_colMatroid_le (A : Matrix (Fin r) (Fin m) K) : rank (colMatroid A) ≤ r := by
  rw [← rk_univ _ (colMatroid_E A)]
  have h := eRk_colMatroid A univ
  rw [← coe_rk] at h
  have h2 : finrank K (span K (colK A '' ((univ : Finset (Fin m)) : Set (Fin m)))) ≤ r :=
    (Submodule.finrank_le _).trans (by simp)
  have h3 : rk (colMatroid A) univ
      = finrank K (span K (colK A '' ((univ : Finset (Fin m)) : Set (Fin m)))) := by
    exact_mod_cast h
  omega

/-- **Matroids represented over a finite field: Boolean rank circuits**
(`greedy_intersection.tex`, Corollary `cor:classes`, item 2).  Let `K` be a finite field with
`q` elements and `A ∈ K^{r × m}`.  A Boolean circuit of size
`m (6 q² r² + 3 q r² + r² + q r + 6 r + 1) + 11 r ⌈log₂(r+1)⌉ + 1`, which is at most
`8 q² (m+1) (r+1)²`, outputs in binary, from the indicator vector of `S ⊆ E`, the rank of the
columns of `A` indexed by `S`: Mathlib's `Matrix.rank` of the column submatrix, which is the
rank of `S` in the column matroid of `A`. -/
theorem field_rankCircuit [Fintype K] (A : Matrix (Fin r) (Fin m) K) :
    ∃ B : Circuit BoolOp m,
      B.size = m * (6 * Fintype.card K ^ 2 * r ^ 2 + 3 * Fintype.card K * r ^ 2 + r ^ 2
          + Fintype.card K * r + 6 * r + 1) + 11 * r * Nat.size r + 1 ∧
      B.size ≤ 8 * Fintype.card K ^ 2 * (m + 1) * (r + 1) ^ 2 ∧
      ∀ S : Finset (Fin m),
        bitsVal (B.eval boolInterp (indicator S))
            = (A.submatrix id (fun e : S => (e : Fin m))).rank ∧
        (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞)
            = (colMatroid A).eRk (S : Set (Fin m)) := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  refine ⟨fieldRankCircuit A, ?_, ?_, fun S => ⟨?_, fieldRankCircuit_rank A S⟩⟩
  · rw [(fieldRankCircuit_spec A).1, colCostK]; ring
  · rw [(fieldRankCircuit_spec A).1]; exact fieldSize_le hq m r
  · have h := fieldRankCircuit_rank A S
    rw [eRk_colMatroid_eq_rank] at h
    exact_mod_cast h

/-- **Matroids represented over a finite field: signed tropical circuits** (Theorem A applied
to `field_rankCircuit`).  Let `K` be a finite field with `q` elements, `A ∈ K^{r × m}` and `M`
the column matroid of `A`.  Then `h_M(w) = max_{B ∈ Bases(M)} w(B)` is computed at every
`w ∈ ℝ^m` by a signed tropical circuit of size at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`,
where `s = m (6 q² r² + 3 q r² + r² + q r + 6 r + 1) + 11 r ⌈log₂(r+1)⌉ + 1` and
`L = ⌈log₂(k+1)⌉` for the rank `k` of `M`; this is at most `25 q² (m+1)² (r+1)²`. -/
theorem theoremA_field [Fintype K] (A : Matrix (Fin r) (Fin m) K) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3 * m * (m * (6 * Fintype.card K ^ 2 * r ^ 2 + 3 * Fintype.card K * r ^ 2 + r ^ 2
          + Fintype.card K * r + 6 * r + 1) + 11 * r * Nat.size r + 1)
          + m * Nat.size (rank (colMatroid A)) + 9 * m ^ 2 + 4 * m
          + 4 * Nat.size (rank (colMatroid A)) + 1 ∧
      C.size ≤ 25 * Fintype.card K ^ 2 * (m + 1) ^ 2 * (r + 1) ^ 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (colMatroid A) w] := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨C, hC, heval⟩ := theoremA (colMatroid A) (colMatroid_E A) (fieldRankCircuit A)
    (fieldRankCircuit_rank A)
  have hs : (fieldRankCircuit A).size = m * colCostK (Fintype.card K) r + r * (11 * Nat.size r)
      + 1 := (fieldRankCircuit_spec A).1
  refine ⟨C, hC.trans (le_of_eq ?_), hC.trans ?_, heval⟩
  · rw [hs, colCostK]; ring
  · rw [hs]
    exact theoremA_fieldSize_le hq m r _ (rank_colMatroid_le A)

end SignedTropical.Classes
