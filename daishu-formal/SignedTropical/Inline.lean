import SignedTropical.Circuit
import Mathlib.Data.List.Forall2

/-!
# Inlining a circuit, one gadget per gate

Given a circuit `C` over a gate set `Op` and, for each operation, a gadget that builds
gates of another gate set `Op'`, `inline` appends to a gate list the gadgets for the gates
of `C` in order and returns the representations of the outputs of `C`.  A source wire is
represented by a value of an arbitrary type `ρ`: one operand for amplitude lifting
(`Lift.lean`) and for Corollary F (`Subtractionfree.lean`), a list of operands carrying the
bits of an integer for the converse simulation (`Converse.lean`).

`inline_spec` is the only correctness statement: if every gadget implements the
corresponding operation of a reading `J x` of `Op` (which may depend on the input `x` of
the outer circuit), then every output representation carries the corresponding output of
`C` read through `J x`.  `length_inline` counts the appended gates.
-/

namespace SignedTropical

variable {Op Op' α γ ρ : Type} {n m : ℕ}

/-- Translate an operand of the inlined circuit: input `i` to `inp i`, the constant to
`c`, and wire `j` to the representation of wire `j` built so far. -/
def Arg.tr (inp : Fin m → ρ) (c : ρ) (outs : List ρ) : Arg m → ρ
  | .input i => inp i
  | .const => c
  | .wire j => outs.getD j c

/-- Append the gadgets of a list of gates; `outs` holds the representations of the wires
already translated. -/
def inlineGates (gad : Op → ρ → ρ → Bld Op' n ρ) (inp : Fin m → ρ) (c : ρ) :
    List (Gate Op m) → List ρ → Bld Op' n (List ρ)
  | [], outs => fun gs => (gs, outs)
  | g :: rest, outs => fun gs =>
    let p := gad g.op (g.a.tr inp c outs) (g.b.tr inp c outs) gs
    inlineGates gad inp c rest (outs ++ [p.2]) p.1

/-- Inline a circuit: append the gadgets of its gates and return the representations of its
outputs. -/
def inline (gad : Op → ρ → ρ → Bld Op' n ρ) (inp : Fin m → ρ) (c : ρ) (C : Circuit Op m) :
    Bld Op' n (List ρ) := fun gs =>
  let p := inlineGates gad inp c C.gates [] gs
  (p.1, C.outs.map (Arg.tr inp c p.2))

section Spec

variable (R : List (Gate Op' n) → ρ → ((Fin n → γ) → α) → Prop)
  (J : (Fin n → γ) → Interp Op α) (φ : Fin m → (Fin n → γ) → α)

/-- `outs` represents, in the gate list `gs`, the source wire values `W x`. -/
def RepWires (gs : List (Gate Op' n)) (outs : List ρ) (W : (Fin n → γ) → List α) : Prop :=
  (∀ x, (W x).length = outs.length) ∧
    ∀ j (hj : j < outs.length), R gs outs[j] (fun x => (W x).getD j (J x).zero)

variable {R J φ} {gad : Op → ρ → ρ → Bld Op' n ρ} {inp : Fin m → ρ} {c : ρ}

theorem tr_spec {gs : List (Gate Op' n)} {outs : List ρ} {W : (Fin n → γ) → List α}
    (hc : R gs c (fun x => (J x).zero)) (hinp : ∀ i, R gs (inp i) (φ i))
    (hW : RepWires R J gs outs W) (a : Arg m) :
    R gs (a.tr inp c outs) (fun x => a.read (J x) (fun i => φ i x) (W x)) := by
  cases a with
  | input i => exact hinp i
  | const => exact hc
  | wire j =>
    simp only [Arg.tr, Arg.read]
    by_cases hj : j < outs.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hW.2 j hj
    · rw [List.getD_eq_default _ _ (by omega)]
      have : (fun x => (W x).getD j (J x).zero) = fun x => (J x).zero :=
        funext fun x => List.getD_eq_default _ _ (by rw [hW.1 x]; omega)
      rwa [this]

variable (hR : ∀ gs gs' r f, gs <+: gs' → R gs r f → R gs' r f)
  {gs₀ : List (Gate Op' n)} (hc : R gs₀ c (fun x => (J x).zero))
  (hinp : ∀ i, R gs₀ (inp i) (φ i))
  (hgad : ∀ o r₁ r₂ f₁ f₂ gs, gs₀ <+: gs → R gs r₁ f₁ → R gs r₂ f₂ →
    gs <+: (gad o r₁ r₂ gs).1 ∧
      R (gad o r₁ r₂ gs).1 (gad o r₁ r₂ gs).2 (fun x => (J x).op o (f₁ x) (f₂ x)))
include hR hc hinp hgad

theorem inlineGates_spec :
    ∀ (rest : List (Gate Op m)) (outs : List ρ) (W : (Fin n → γ) → List α)
      (gs : List (Gate Op' n)), gs₀ <+: gs → RepWires R J gs outs W →
      gs <+: (inlineGates gad inp c rest outs gs).1 ∧
        RepWires R J (inlineGates gad inp c rest outs gs).1
          (inlineGates gad inp c rest outs gs).2
          (fun x => rest.foldl (fun ws g => ws ++ [g.eval (J x) (fun i => φ i x) ws]) (W x)) := by
  intro rest
  induction rest with
  | nil => intro outs W gs _ hW; exact ⟨List.prefix_refl _, hW⟩
  | cons g rest ih =>
    intro outs W gs h0 hW
    have hc' := hR _ _ _ _ h0 hc
    have hinp' := fun i => hR _ _ _ _ h0 (hinp i)
    obtain ⟨hp, hval⟩ := hgad g.op _ _ _ _ gs h0 (tr_spec hc' hinp' hW g.a)
      (tr_spec hc' hinp' hW g.b)
    set p := gad g.op (g.a.tr inp c outs) (g.b.tr inp c outs) gs
    have hW' : RepWires R J p.1 (outs ++ [p.2])
        (fun x => W x ++ [g.eval (J x) (fun i => φ i x) (W x)]) := by
      refine ⟨fun x => by simp [hW.1 x], fun j hj => ?_⟩
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [List.getElem_append_left hj]
        have : (fun x => (W x ++ [g.eval (J x) (fun i => φ i x) (W x)]).getD j (J x).zero)
            = fun x => (W x).getD j (J x).zero :=
          funext fun x => List.getD_append _ _ _ _ (by rw [hW.1 x]; exact hj)
        rw [this]
        exact hR _ _ _ _ hp (hW.2 j hj)
      · rw [List.getElem_append_right (Nat.le_refl _)]
        have : (fun x => (W x ++ [g.eval (J x) (fun i => φ i x) (W x)]).getD outs.length
            (J x).zero) = fun x => (J x).op g.op (g.a.read (J x) (fun i => φ i x) (W x))
              (g.b.read (J x) (fun i => φ i x) (W x)) := by
          funext x
          rw [List.getD_append_right _ _ _ _ (by rw [hW.1 x]; exact Nat.le_refl _), hW.1 x,
            Nat.sub_self]
          rfl
        rw [this]
        simpa using hval
    obtain ⟨h1, h2⟩ := ih (outs ++ [p.2]) _ p.1 (h0.trans hp) hW'
    exact ⟨hp.trans h1, h2⟩

/-- **Inlining is correct.**  Every output representation carries the corresponding output
of the inlined circuit, read through `J x` at the inputs `φ i x`. -/
theorem inline_spec (C : Circuit Op m) :
    gs₀ <+: (inline gad inp c C gs₀).1 ∧
      List.Forall₂ (fun r f => R (inline gad inp c C gs₀).1 r f) (inline gad inp c C gs₀).2
        (C.outs.map fun o x => o.read (J x) (fun i => φ i x)
          (wires (J x) (fun i => φ i x) C.gates)) := by
  obtain ⟨h1, h2⟩ := inlineGates_spec hR hc hinp hgad C.gates [] (fun _ => []) gs₀
    (List.prefix_refl _) ⟨fun _ => rfl, fun j hj => absurd hj (by simp)⟩
  refine ⟨h1, ?_⟩
  simp only [inline, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun o _ => ?_
  exact tr_spec (hR _ _ _ _ h1 hc) (fun i => hR _ _ _ _ h1 (hinp i)) h2 o

end Spec

/-- Gate count of an inlined circuit, when the gadget for `o` always appends `cost o`
gates. -/
theorem length_inline {gad : Op → ρ → ρ → Bld Op' n ρ} {inp : Fin m → ρ} {c : ρ}
    (cost : Op → ℕ) (hcost : ∀ o r₁ r₂ gs, (gad o r₁ r₂ gs).1.length = gs.length + cost o)
    (C : Circuit Op m) (gs : List (Gate Op' n)) :
    (inline gad inp c C gs).1.length = gs.length + (C.gates.map fun g => cost g.op).sum := by
  suffices ∀ (rest : List (Gate Op m)) outs (gs : List (Gate Op' n)),
      (inlineGates gad inp c rest outs gs).1.length
        = gs.length + (rest.map fun g => cost g.op).sum from this C.gates [] gs
  intro rest
  induction rest with
  | nil => intro _ _; simp [inlineGates]
  | cons g rest ih =>
    intro outs gs
    simp only [inlineGates, ih, hcost, List.map_cons, List.sum_cons]
    omega

/-- Scalar form: with one operand per wire and `Den` as the representation relation, the
returned operands denote the outputs of the inlined circuit. -/
theorem DenL.of_forall₂ {I : Interp Op' γ} {gs : List (Gate Op' n)} :
    ∀ {as : List (Arg n)} {fs : List ((Fin n → γ) → γ)},
      List.Forall₂ (fun r f => Den I gs r f) as fs → DenL I gs as (fun x => fs.map (· x))
  | [], [], _ => denL_nil gs
  | _ :: _, _ :: _, List.Forall₂.cons h hs => (DenL.of_forall₂ hs).cons h

end SignedTropical
