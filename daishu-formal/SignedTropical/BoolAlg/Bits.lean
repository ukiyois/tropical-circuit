import SignedTropical.BoolAlg.Impl
import SignedTropical.Binary

/-!
# Bits and vectors of bits

Boolean representations and gadgets over `BoolOp` (gates `∧`, `∨`, `¬`; constant source
`false`), in the form `Impl R₁ R₂ b c F` of `BoolAlg/Impl.lean`: the builder `b` appends exactly
`c` gates and its result carries `F` of what its argument carries.

* Representations: one bit (`bitR`); a vector of `r` bits, that is a subset of `Fin r`
  (`vecR r`); a relation on `Fin r` as `r²` bits (`relR r`); an `r × s` matrix of bits
  (`matR r s`); a list of `L` bits (`bitsR L`).
* One gate: `emit_impl`, read as `emitAnd_impl`, `emitOr_impl`, `emitNot_impl`; exclusive or,
  four gates (`xorB_impl`); the constants `true`, one gate (`true_impl`), and `false`, none
  (`false_impl`).
* Vectors of `r` bits: bitwise `¬`, `∧`, `∨` (`r` gates each) and `⊕` (`4r`); a bit and every
  entry (`vecMaskB`, `r`); selection `if s then u else v` (`vecMuxB`, `3r + 1`); some entry
  (`vecAnyB`, `r`); every entry (`vecAllB`, `r + 1`); some `aᵢ ∧ bᵢ` (`dotAccB`, `2r`).
* **Least-index selection** (`vecFirstB`, `3r` gates): the one-hot vector of the least set
  entry, `leadV` of `Binary.lean`, with `leadV_eq_true_iff`, `leadV_unique`,
  `exists_leadV_iff`, `leadV_eq_min'` (the entry marked is the `min'` of the set entries),
  `leadV_eq_find` (over indices `d < r` of a predicate on `ℕ`, the entry marked is `Nat.find`)
  and `leadV_of_forall_false`.
* Circuits with bit outputs: an implementation of `L` bits from the input operands
  (`input_rep`) is a circuit with these `L` outputs (`vecCircuit`, `vecCircuit_spec`).
-/

namespace SignedTropical.BoolAlg

open Finset

variable {n r : ℕ} {σ τ : Type}

/-! ### Representations -/

/-- One operand carrying one bit. -/
abbrev bitR : Rep BoolOp Bool n (Arg n) Bool := Rep.arg boolInterp

/-- `r` operands carrying a vector of `r` bits, that is a subset of `Fin r`. -/
abbrev vecR (r : ℕ) : Rep BoolOp Bool n (Fin r → Arg n) (Fin r → Bool) := Rep.pi (Fin r) bitR

/-- `r²` operands carrying a relation on `Fin r`. -/
abbrev relR (r : ℕ) : Rep BoolOp Bool n (Fin r → Fin r → Arg n) (Fin r → Fin r → Bool) :=
  Rep.pi (Fin r) (vecR r)

/-- `r s` operands carrying an `r × s` matrix of bits, a relation from `Fin r` to `Fin s`. -/
abbrev matR (r s : ℕ) : Rep BoolOp Bool n (Fin r → Fin s → Arg n) (Fin r → Fin s → Bool) :=
  Rep.pi (Fin r) (vecR s)

/-- `L` operands carrying a list of `L` bits. -/
abbrev bitsR (L : ℕ) : Rep BoolOp Bool n (List (Arg n)) (List Bool) := Rep.list boolInterp L

/-! ### One gate -/

/-- **One gate** `o` on two bits. -/
theorem emit_impl (o : BoolOp) :
    Impl (bitR.prod bitR) (bitR (n := n)) (fun p => emit o p.1 p.2) 1
      (fun p => boolInterp.op o p.1 p.2) :=
  fun _ _ _ hs => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, den_emit o hs.1 hs.2⟩

/-- One `∧` gate. -/
theorem emitAnd_impl :
    Impl (bitR.prod bitR) (bitR (n := n)) (fun p => emit .and p.1 p.2) 1 (fun p => p.1 && p.2) :=
  emit_impl .and

/-- One `∨` gate. -/
theorem emitOr_impl :
    Impl (bitR.prod bitR) (bitR (n := n)) (fun p => emit .or p.1 p.2) 1 (fun p => p.1 || p.2) :=
  emit_impl .or

/-- One `¬` gate. -/
theorem emitNot_impl : Impl bitR (bitR (n := n)) (fun a => emit .not a .const) 1 (!·) :=
  fun gs _ _ hs => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
    den_emit BoolOp.not hs (den_const gs)⟩

/-- Exclusive or, four gates (`xorB` of `Converse.lean`). -/
theorem xorB_impl :
    Impl (bitR.prod bitR) (bitR (n := n)) (fun p => xorB p.1 p.2) 4 (fun p => p.1 ^^ p.2) :=
  fun _ _ _ hs => xorB_spec hs.1 hs.2

/-- The constant `true`, one gate `¬false`. -/
theorem true_impl (R : Rep BoolOp Bool n σ τ) :
    Impl R bitR (fun _ => emit .not .const .const) 1 (fun _ => true) :=
  fun gs _ _ _ => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
    den_emit (I := boolInterp) BoolOp.not (den_const gs) (den_const gs)⟩

/-- The constant `false` is the constant source: no gate. -/
theorem false_impl (R : Rep BoolOp Bool n σ τ) :
    Impl R bitR (pureB fun _ => .const) 0 (fun _ => false) :=
  Impl.free fun gs _ _ _ => den_const gs

/-! ### Bitwise operations on vectors -/

/-- Bitwise negation, `r` gates. -/
def vecNotB (v : Fin r → Arg n) : Bld BoolOp n (Fin r → Arg n) :=
  tabB fun i => emit .not (v i) .const

/-- **Bitwise negation**, `r` gates. -/
theorem vecNotB_impl : Impl (vecR r) (vecR (n := n) r) vecNotB r (fun V i => !V i) :=
  (emitNot_impl.map r).cost (mul_one r)

/-- Bitwise conjunction, `r` gates. -/
def vecAndB (p : (Fin r → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  tabB fun i => emit .and (p.1 i) (p.2 i)

/-- **Bitwise conjunction**, `r` gates. -/
theorem vecAndB_impl :
    Impl ((vecR r).prod (vecR r)) (vecR (n := n) r) vecAndB r (fun P i => P.1 i && P.2 i) :=
  (emitAnd_impl.map₂ r).cost (mul_one r)

/-- Bitwise disjunction, `r` gates. -/
def vecOrB (p : (Fin r → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  tabB fun i => emit .or (p.1 i) (p.2 i)

/-- **Bitwise disjunction**, `r` gates. -/
theorem vecOrB_impl :
    Impl ((vecR r).prod (vecR r)) (vecR (n := n) r) vecOrB r (fun P i => P.1 i || P.2 i) :=
  (emitOr_impl.map₂ r).cost (mul_one r)

/-- Bitwise exclusive or, `4r` gates. -/
def vecXorB (p : (Fin r → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  tabB fun i => xorB (p.1 i) (p.2 i)

/-- **Bitwise exclusive or** (`lem:augment`, Step 1: the exchange `I ∆ P`), `4r` gates. -/
theorem vecXorB_impl :
    Impl ((vecR r).prod (vecR r)) (vecR (n := n) r) vecXorB (4 * r) (fun P i => P.1 i ^^ P.2 i) :=
  (xorB_impl.map₂ r).cost (mul_comm r 4)

/-- A bit and every entry of a vector, `r` gates. -/
def vecMaskB (p : Arg n × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  tabB fun i => emit .and p.1 (p.2 i)

/-- **A bit and every entry**, `r` gates. -/
theorem vecMaskB_impl :
    Impl (bitR.prod (vecR r)) (vecR (n := n) r) vecMaskB r (fun P i => P.1 && P.2 i) :=
  (Impl.tab fun i => emitAnd_impl.pre (R := bitR.prod (vecR r)) (g := fun p => (p.1, p.2 i))
    (G := fun P => (P.1, P.2 i)) fun _ _ _ hs => ⟨hs.1, hs.2 i⟩).cost (mul_one r)

/-- **Selection** `if s then u else v`, entrywise `(s ∧ uᵢ) ∨ (¬s ∧ vᵢ)`: `3r + 1` gates. -/
def vecMuxB (p : Arg n × (Fin r → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  fun gs =>
    let t := emit .not p.1 .const gs
    tabB (fun i gs =>
      let a := emit .and p.1 (p.2.1 i) gs
      let b := emit .and t.2 (p.2.2 i) a.1
      emit .or a.2 b.2 b.1) t.1

/-- **Selection of vectors** `if s then u else v`, `3r + 1` gates. -/
theorem vecMuxB_impl :
    Impl (bitR.prod ((vecR r).prod (vecR r))) (vecR (n := n) r) vecMuxB (3 * r + 1)
      (fun P i => if P.1 then P.2.1 i else P.2.2 i) := by
  intro gs p P hp
  have ht := den_emit BoolOp.not hp.1 (den_const gs)
  have pt := isPrefix_emit BoolOp.not p.1 .const gs
  obtain ⟨hp', hl, hr⟩ := tabB_spec (R₂ := bitR) (c := 3) (gs₀ := (emit .not p.1 .const gs).1)
    (F := fun i x => if (P x).1 then (P x).2.1 i else (P x).2.2 i)
    (b := fun i gs' =>
      let a := emit .and p.1 (p.2.1 i) gs'
      let b := emit .and (emit .not p.1 .const gs).2 (p.2.2 i) a.1
      emit .or a.2 b.2 b.1) fun i gs' hgs => by
      have pa := isPrefix_emit BoolOp.and p.1 (p.2.1 i) gs'
      have ha := den_emit BoolOp.and (hp.1.mono (pt.trans hgs)) ((hp.2.1 i).mono (pt.trans hgs))
      have pb := isPrefix_emit BoolOp.and (emit .not p.1 .const gs).2 (p.2.2 i)
        (emit .and p.1 (p.2.1 i) gs').1
      have hb := den_emit BoolOp.and ((ht.mono hgs).mono pa)
        (((hp.2.2 i).mono (pt.trans hgs)).mono pa)
      have hc := den_emit BoolOp.or (ha.mono pb) hb
      refine ⟨pa.trans (pb.trans (isPrefix_emit _ _ _ _)), by simp [length_emit],
        hc.congr fun x => ?_⟩
      cases (P x).1 <;> simp [boolInterp]
  exact ⟨pt.trans hp', hl.trans (by rw [length_emit]; ring), hr⟩

/-! ### Reductions of a vector -/

/-- `acc ∨ v₀ ∨ ⋯ ∨ v_{r-1}`, one gate per entry. -/
def anyAccB : {r : ℕ} → (Fin r → Arg n) → Arg n → Bld BoolOp n (Arg n)
  | 0, _, acc => fun gs => (gs, acc)
  | _ + 1, v, acc => fun gs =>
    let p := emit .or acc (v 0) gs
    anyAccB (fun i => v i.succ) p.2 p.1

/-- `anyAccB`: one gate per entry, the accumulator or some entry. -/
theorem anyAccB_spec : ∀ {r : ℕ} {v : Fin r → Arg n} {acc : Arg n}
    {V : (Fin n → Bool) → Fin r → Bool} {A : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
    (vecR r).rep gs v V → bitR.rep gs acc A →
      gs <+: (anyAccB v acc gs).1 ∧ (anyAccB v acc gs).1.length = gs.length + r ∧
        bitR.rep (anyAccB v acc gs).1 (anyAccB v acc gs).2
          (fun x => A x || decide (∃ i, V x i = true))
  | 0, _, _, _, _, _, _, ha => ⟨List.prefix_refl _, rfl, Rep.congr _ ha fun x => by simp⟩
  | r + 1, v, acc, V, A, gs, hv, ha => by
    have p₁ := isPrefix_emit BoolOp.or acc (v 0) gs
    obtain ⟨hp, hl, hr⟩ := anyAccB_spec (v := fun i => v i.succ) (V := fun x i => V x i.succ)
      (fun i => (hv i.succ).mono p₁) (den_emit BoolOp.or ha (hv 0))
    refine ⟨p₁.trans hp, hl.trans (by rw [length_emit]; ring), Rep.congr _ hr fun x => ?_⟩
    simp [boolInterp, Fin.exists_fin_succ, Bool.or_assoc]

/-- `acc ∧ v₀ ∧ ⋯ ∧ v_{r-1}`, one gate per entry. -/
def allAccB : {r : ℕ} → (Fin r → Arg n) → Arg n → Bld BoolOp n (Arg n)
  | 0, _, acc => fun gs => (gs, acc)
  | _ + 1, v, acc => fun gs =>
    let p := emit .and acc (v 0) gs
    allAccB (fun i => v i.succ) p.2 p.1

/-- `allAccB`: one gate per entry, the accumulator and every entry. -/
theorem allAccB_spec : ∀ {r : ℕ} {v : Fin r → Arg n} {acc : Arg n}
    {V : (Fin n → Bool) → Fin r → Bool} {A : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
    (vecR r).rep gs v V → bitR.rep gs acc A →
      gs <+: (allAccB v acc gs).1 ∧ (allAccB v acc gs).1.length = gs.length + r ∧
        bitR.rep (allAccB v acc gs).1 (allAccB v acc gs).2
          (fun x => A x && decide (∀ i, V x i = true))
  | 0, _, _, _, _, _, _, ha => ⟨List.prefix_refl _, rfl, Rep.congr _ ha fun x => by simp⟩
  | r + 1, v, acc, V, A, gs, hv, ha => by
    have p₁ := isPrefix_emit BoolOp.and acc (v 0) gs
    obtain ⟨hp, hl, hr⟩ := allAccB_spec (v := fun i => v i.succ) (V := fun x i => V x i.succ)
      (fun i => (hv i.succ).mono p₁) (den_emit BoolOp.and ha (hv 0))
    refine ⟨p₁.trans hp, hl.trans (by rw [length_emit]; ring), Rep.congr _ hr fun x => ?_⟩
    simp [boolInterp, Fin.forall_fin_succ, Bool.and_assoc]

/-- `acc ∨ (a₀ ∧ b₀) ∨ ⋯ ∨ (a_{r-1} ∧ b_{r-1})`, two gates per entry. -/
def dotAccB : {r : ℕ} → (Fin r → Arg n) → (Fin r → Arg n) → Arg n → Bld BoolOp n (Arg n)
  | 0, _, _, acc => fun gs => (gs, acc)
  | _ + 1, a, b, acc => fun gs =>
    let p := emit .and (a 0) (b 0) gs
    let q := emit .or acc p.2 p.1
    dotAccB (fun i => a i.succ) (fun i => b i.succ) q.2 q.1

/-- `dotAccB`: two gates per entry, the accumulator or some `aᵢ ∧ bᵢ`. -/
theorem dotAccB_spec : ∀ {r : ℕ} {a b : Fin r → Arg n} {acc : Arg n}
    {P Q : (Fin n → Bool) → Fin r → Bool} {A : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
    (vecR r).rep gs a P → (vecR r).rep gs b Q → bitR.rep gs acc A →
      gs <+: (dotAccB a b acc gs).1 ∧ (dotAccB a b acc gs).1.length = gs.length + 2 * r ∧
        bitR.rep (dotAccB a b acc gs).1 (dotAccB a b acc gs).2
          (fun x => A x || decide (∃ i, P x i = true ∧ Q x i = true))
  | 0, _, _, _, _, _, _, _, _, _, ha => ⟨List.prefix_refl _, rfl, Rep.congr _ ha fun x => by simp⟩
  | r + 1, a, b, acc, P, Q, A, gs, hP, hQ, ha => by
    have p₁ := isPrefix_emit BoolOp.and (a 0) (b 0) gs
    have h₁ := den_emit BoolOp.and (hP 0) (hQ 0)
    have p₂ := isPrefix_emit BoolOp.or acc (emit .and (a 0) (b 0) gs).2
      (emit .and (a 0) (b 0) gs).1
    have h₂ := den_emit BoolOp.or (ha.mono p₁) h₁
    obtain ⟨hp, hl, hr⟩ := dotAccB_spec (a := fun i => a i.succ) (b := fun i => b i.succ)
      (P := fun x i => P x i.succ) (Q := fun x i => Q x i.succ)
      (fun i => (hP i.succ).mono (p₁.trans p₂)) (fun i => (hQ i.succ).mono (p₁.trans p₂)) h₂
    refine ⟨(p₁.trans p₂).trans hp, hl.trans (by rw [length_emit, length_emit]; ring),
      Rep.congr _ hr fun x => ?_⟩
    simp [boolInterp, Fin.exists_fin_succ, Bool.or_assoc]

/-- **Some entry is set**, `r` gates. -/
def vecAnyB (v : Fin r → Arg n) : Bld BoolOp n (Arg n) := anyAccB v .const

/-- **Some entry is set**, `r` gates. -/
theorem vecAnyB_impl :
    Impl (vecR r) (bitR (n := n)) vecAnyB r (fun V => decide (∃ i, V i = true)) := by
  intro gs v V hv
  obtain ⟨hp, hl, hr⟩ := anyAccB_spec hv (den_const gs)
  exact ⟨hp, hl, Rep.congr _ hr fun x => by simp [boolInterp]⟩

/-- **Every entry is set**, `r + 1` gates. -/
def vecAllB (v : Fin r → Arg n) : Bld BoolOp n (Arg n) := fun gs =>
  let t := emit .not .const .const gs
  allAccB v t.2 t.1

/-- **Every entry is set**, `r + 1` gates. -/
theorem vecAllB_impl :
    Impl (vecR r) (bitR (n := n)) vecAllB (r + 1) (fun V => decide (∀ i, V i = true)) := by
  intro gs v V hv
  have pt := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const gs
  obtain ⟨hp, hl, hr⟩ := allAccB_spec (fun i => (hv i).mono pt)
    (den_emit BoolOp.not (den_const gs) (den_const gs))
  exact ⟨pt.trans hp, hl.trans (by rw [length_emit]; ring), Rep.congr _ hr fun x => by
    simp [boolInterp]⟩

/-! ### Least-index selection -/

/-- Entry `j` of `leadV v` is set iff `v j` is set and no earlier entry of `v` is. -/
theorem leadV_eq_true_iff {v : Fin r → Bool} {j : Fin r} :
    leadV v j = true ↔ v j = true ∧ ∀ i < j, v i = false := by
  simp [leadV]

/-- At most one entry of `leadV v` is set. -/
theorem leadV_unique {v : Fin r → Bool} {i j : Fin r} (hi : leadV v i = true)
    (hj : leadV v j = true) : i = j := by
  rw [leadV_eq_true_iff] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hj.2 i h) (by simp [hi.1])
  · exact absurd (hi.2 j h) (by simp [hj.1])

/-- `leadV v` has a set entry iff `v` has one. -/
theorem exists_leadV_iff {v : Fin r → Bool} : (∃ j, leadV v j = true) ↔ ∃ j, v j = true := by
  refine ⟨fun ⟨j, hj⟩ => ⟨j, (leadV_eq_true_iff.1 hj).1⟩, fun ⟨j₀, hj₀⟩ => ?_⟩
  have hne : (univ.filter fun i => v i = true).Nonempty := ⟨j₀, by simp [hj₀]⟩
  refine ⟨(univ.filter fun i => v i = true).min' hne, leadV_eq_true_iff.2 ⟨?_, fun i hi => ?_⟩⟩
  · simpa using Finset.min'_mem _ hne
  · by_contra h
    exact absurd (Finset.min'_le _ i (by simpa using h)) (not_le.2 hi)

/-- `leadV v` marks the least set entry of `v`, the `min'` of the set entries. -/
theorem leadV_eq_min' {v : Fin r → Bool} (h : (univ.filter fun i => v i = true).Nonempty)
    (p : Fin r) : leadV v p = decide (p = (univ.filter fun i => v i = true).min' h) := by
  refine leadV_eq (by simpa using min'_mem _ h) (fun i hi => ?_) p
  by_contra hvi
  exact absurd (min'_le _ i (by simpa using hvi)) (not_le.2 hi)

/-- Least-index selection over the indices `d < r` of a predicate on `ℕ` marks `Nat.find`, when
the least `d` lies below `r`. -/
theorem leadV_eq_find {P : ℕ → Prop} [DecidablePred P] (h : ∃ d, P d) (hr : Nat.find h < r)
    (j : Fin r) : leadV (fun d : Fin r => decide (P d)) j = decide ((j : ℕ) = Nat.find h) := by
  rw [leadV_eq (q := ⟨Nat.find h, hr⟩) (by simpa using Nat.find_spec h)
    (fun i hi => by simpa using Nat.find_min h (Fin.lt_def.1 hi)) j]
  exact decide_eq_decide.2 Fin.ext_iff

/-- `leadV v` has no set entry when `v` has none. -/
theorem leadV_of_forall_false {v : Fin r → Bool} (h : ∀ i, v i = false) (p : Fin r) :
    leadV v p = false := by
  simp [leadV, h p]

/-- Least-index selection after the entries counted in the accumulator `acc`. -/
def firstAccB : {r : ℕ} → (Fin r → Arg n) → Arg n → Bld BoolOp n (Fin r → Arg n)
  | 0, _, _ => fun gs => (gs, Fin.elim0)
  | _ + 1, v, acc => fun gs =>
    let p₁ := emit .not acc .const gs
    let p₂ := emit .and (v 0) p₁.2 p₁.1
    let p₃ := emit .or acc (v 0) p₂.1
    let q := firstAccB (fun i => v i.succ) p₃.2 p₃.1
    (q.1, Fin.cons p₂.2 q.2)

/-- `firstAccB`: three gates per entry; entry `j` is set iff `vⱼ` is set and neither the
accumulator nor an earlier entry is. -/
theorem firstAccB_spec : ∀ {r : ℕ} {v : Fin r → Arg n} {acc : Arg n}
    {V : (Fin n → Bool) → Fin r → Bool} {A : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
    (vecR r).rep gs v V → bitR.rep gs acc A →
      gs <+: (firstAccB v acc gs).1 ∧ (firstAccB v acc gs).1.length = gs.length + 3 * r ∧
        (vecR r).rep (firstAccB v acc gs).1 (firstAccB v acc gs).2
          (fun x j => V x j && !(A x || decide (∃ i < j, V x i = true)))
  | 0, _, _, _, _, _, _, _ => ⟨List.prefix_refl _, rfl, fun i => i.elim0⟩
  | r + 1, v, acc, V, A, gs, hv, ha => by
    have p₁ := isPrefix_emit BoolOp.not acc .const gs
    have h₁ := den_emit BoolOp.not ha (den_const gs)
    have p₂ := isPrefix_emit BoolOp.and (v 0) (emit .not acc .const gs).2
      (emit .not acc .const gs).1
    have h₂ := den_emit BoolOp.and ((hv 0).mono p₁) h₁
    have p₃ := isPrefix_emit BoolOp.or acc (v 0) (emit .and (v 0) (emit .not acc .const gs).2
      (emit .not acc .const gs).1).1
    have h₃ := den_emit BoolOp.or ((ha.mono p₁).mono p₂) (((hv 0).mono p₁).mono p₂)
    have p₁₂₃ := (p₁.trans p₂).trans p₃
    obtain ⟨hp, hl, hr⟩ := firstAccB_spec (v := fun i => v i.succ) (V := fun x i => V x i.succ)
      (fun i => (hv i.succ).mono p₁₂₃) h₃
    refine ⟨p₁₂₃.trans hp, hl.trans (by simp only [length_emit]; ring), fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Rep.congr _ ((h₂.mono p₃).mono hp) fun x => by simp [boolInterp]
    · refine Rep.congr _ (hr j) fun x => ?_
      have : (∃ i < j.succ, V x i = true) ↔ V x 0 = true ∨ ∃ i < j, V x i.succ = true := by
        rw [Fin.exists_fin_succ]
        simp [Fin.succ_lt_succ_iff]
      simp [boolInterp, this, Bool.or_assoc]

/-- **Least-index selection**: the one-hot vector of the least set entry
(`vᵢ ∧ ¬(v₀ ∨ ⋯ ∨ v_{i-1})`), `3r` gates. -/
def vecFirstB (v : Fin r → Arg n) : Bld BoolOp n (Fin r → Arg n) := firstAccB v .const

/-- **Least-index selection** (`lem:observer`, Step 2 "its element of least index" and Step 4
"the sink of least index ..., then predecessors of least index"): the one-hot vector `leadV`
of the least set entry, `3r` gates. -/
theorem vecFirstB_impl : Impl (vecR r) (vecR (n := n) r) vecFirstB (3 * r) leadV := by
  intro gs v V hv
  obtain ⟨hp, hl, hr⟩ := firstAccB_spec hv (den_const gs)
  exact ⟨hp, hl, fun j => Rep.congr _ (hr j) fun x => by simp [boolInterp, leadV]⟩

/-! ### Circuits with bit outputs -/

/-- The input operands carry the input. -/
theorem input_rep (gs : List (Gate BoolOp n)) : (vecR n).rep gs (fun i => .input i) (fun x => x) :=
  fun i => den_input gs i

/-- The circuit that a builder of `L` bits makes from the input operands. -/
def vecCircuit {L : ℕ} (b : (Fin n → Arg n) → Bld BoolOp n (Fin L → Arg n)) : Circuit BoolOp n :=
  circuitOf (seqB b (pureB List.ofFn))

/-- **An implementation of `L` bits from the inputs is a circuit** of size `c` whose `L`
outputs are these bits. -/
theorem vecCircuit_spec {L c : ℕ} {b : (Fin n → Arg n) → Bld BoolOp n (Fin L → Arg n)}
    {F : (Fin n → Bool) → Fin L → Bool} (h : Impl (vecR n) (vecR L) b c F) :
    (vecCircuit b).size = c ∧ (vecCircuit b).outs.length = L ∧
      ∀ x, (vecCircuit b).eval boolInterp x = List.ofFn (F x) :=
  circuitOf_spec ((h.comp (ofFn_impl boolInterp L)).cost (Nat.add_zero c))

end SignedTropical.BoolAlg
