import SignedTropical.Inline
import SignedTropical.Models
import Mathlib.Tactic.Linarith

/-!
# Lifting a Boolean circuit to amplitude `Δ`

`signed_assignment.tex`, Lemma `lem:lift`.  Represent the Boolean value `b` by `Δ·b`
(`ampl`).  Then

* `Δ(b₁ ∧ b₂) = max(Δb₁ + Δb₂ - Δ, 0)`,
* `Δ(b₁ ∨ b₂) = max(Δb₁, Δb₂)`,
* `Δ(¬b) = Δ - Δb`,

for every `Δ ≥ 0` (`ampl_op`), which is the case check of the homomorphism lemma for the
lifted reading `liftInterp Δ` of the Boolean gates (`eval_liftInterp`).  The lifted
circuit replaces each Boolean gate by the corresponding gadget of three, one or one signed
tropical gates (`liftGad`), so it has at most `3 s` gates.

At `Δ = 0` all inputs are `0`, and a signed tropical circuit whose inputs are all `0`
carries `0` on every wire (`wires_eq_zero`); this is the vanishing statement of
`lem:lift`, and it is also the instance `Δ = 0` of `eval_liftInterp`.
-/

namespace SignedTropical

variable {n m : ℕ}

/-- The Boolean value `b` at amplitude `Δ`: `Δ` if `b`, else `0`. -/
def ampl (Δ : ℝ) (b : Bool) : ℝ := if b then Δ else 0

@[simp] theorem ampl_true (Δ : ℝ) : ampl Δ true = Δ := rfl
@[simp] theorem ampl_false (Δ : ℝ) : ampl Δ false = 0 := rfl

/-- Boolean gates read at amplitude `Δ`. -/
noncomputable def liftInterp (Δ : ℝ) : Interp BoolOp ℝ where
  zero := 0
  op
    | .and, a, b => max (a + b - Δ) 0
    | .or, a, b => max a b
    | .not, a, _ => Δ - a

/-- The case check: at `Δ ≥ 0`, `ampl Δ` carries Boolean gates to lifted gates. -/
theorem ampl_op {Δ : ℝ} (hΔ : 0 ≤ Δ) (o : BoolOp) (a b : Bool) :
    ampl Δ (boolInterp.op o a b) = (liftInterp Δ).op o (ampl Δ a) (ampl Δ b) := by
  cases o <;> cases a <;> cases b <;>
    simp [ampl, boolInterp, liftInterp, hΔ]

/-- **Lifted evaluation.**  At `Δ ≥ 0`, the lifted reading of a Boolean circuit at the
inputs `Δ·βᵢ` returns `Δ` times its Boolean outputs. -/
theorem eval_liftInterp {Δ : ℝ} (hΔ : 0 ≤ Δ) (B : Circuit BoolOp m) (β : Fin m → Bool) :
    B.eval (liftInterp Δ) (fun i => ampl Δ (β i)) = (B.eval boolInterp β).map (ampl Δ) :=
  B.eval_map (ampl Δ) β rfl (ampl_op hΔ)

/-- The gadget for one Boolean gate, reading the amplitude from the operand `amp`. -/
def liftGad (amp : Arg n) : BoolOp → Arg n → Arg n → Bld STOp n (Arg n)
  | .and, a, b => fun gs =>
    let p₁ := emit .add a b gs
    let p₂ := emit .sub p₁.2 amp p₁.1
    emit .max p₂.2 .const p₂.1
  | .or, a, b => emit .max a b
  | .not, a, _ => emit .sub amp a

/-- Gates per lifted Boolean gate. -/
def liftCost : BoolOp → ℕ
  | .and => 3
  | .or => 1
  | .not => 1

theorem length_liftGad (amp : Arg n) (o : BoolOp) (a b : Arg n) (gs : List (Gate STOp n)) :
    (liftGad amp o a b gs).1.length = gs.length + liftCost o := by
  cases o <;> simp [liftGad, liftCost, length_emit]

theorem liftGad_spec {gs : List (Gate STOp n)} {amp a b : Arg n} {δ f g : (Fin n → ℝ) → ℝ}
    (hamp : Den (stInterp ℝ) gs amp δ) (ha : Den (stInterp ℝ) gs a f)
    (hb : Den (stInterp ℝ) gs b g) (o : BoolOp) :
    gs <+: (liftGad amp o a b gs).1 ∧ Den (stInterp ℝ) (liftGad amp o a b gs).1
      (liftGad amp o a b gs).2 (fun x => (liftInterp (δ x)).op o (f x) (g x)) := by
  cases o with
  | and =>
    have p₁ : gs <+: (emit STOp.add a b gs).1 := isPrefix_emit _ _ _ _
    have h₁ := den_emit STOp.add ha hb
    have p₂ : (emit STOp.add a b gs).1 <+:
        (emit STOp.sub (emit STOp.add a b gs).2 amp (emit STOp.add a b gs).1).1 :=
      isPrefix_emit _ _ _ _
    have h₂ := den_emit STOp.sub h₁ (hamp.mono p₁)
    have h₃ := den_emit STOp.max h₂ (den_const _)
    exact ⟨(p₁.trans p₂).trans (isPrefix_emit _ _ _ _), h₃.congr fun x => rfl⟩
  | or => exact ⟨isPrefix_emit _ _ _ _, (den_emit STOp.max ha hb).congr fun x => rfl⟩
  | not => exact ⟨isPrefix_emit _ _ _ _, (den_emit STOp.sub hamp ha).congr fun x => rfl⟩

/-- Lift a Boolean circuit: inline it with the gadgets `liftGad amp`, reading its inputs
from the operands `inp`. -/
def liftB (B : Circuit BoolOp m) (inp : Fin m → Arg n) (amp : Arg n) :
    Bld STOp n (List (Arg n)) :=
  inline (liftGad amp) inp .const B

/-- Gate count of the lifted circuit. -/
theorem length_liftB (B : Circuit BoolOp m) (inp : Fin m → Arg n) (amp : Arg n)
    (gs : List (Gate STOp n)) :
    (liftB B inp amp gs).1.length = gs.length + (B.gates.map fun g => liftCost g.op).sum :=
  length_inline liftCost (length_liftGad amp) B gs

theorem liftCost_sum_le (B : Circuit BoolOp m) :
    (B.gates.map fun g => liftCost g.op).sum ≤ 3 * B.size := by
  simp only [Circuit.size]
  induction B.gates with
  | nil => simp
  | cons g l ih =>
    have : liftCost g.op ≤ 3 := by cases g.op <;> simp [liftCost]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- **Correctness of the lifted builder.**  Its outputs denote the lifted reading of the
Boolean circuit at the amplitude read from `amp` and the inputs read from `inp`. -/
theorem liftB_spec {B : Circuit BoolOp m} {inp : Fin m → Arg n} {amp : Arg n}
    {gs : List (Gate STOp n)} {δ : (Fin n → ℝ) → ℝ} {φ : Fin m → (Fin n → ℝ) → ℝ}
    (hamp : Den (stInterp ℝ) gs amp δ) (hinp : ∀ i, Den (stInterp ℝ) gs (inp i) (φ i)) :
    gs <+: (liftB B inp amp gs).1 ∧
      DenL (stInterp ℝ) (liftB B inp amp gs).1 (liftB B inp amp gs).2
        (fun x => B.eval (liftInterp (δ x)) (fun i => φ i x)) := by
  obtain ⟨hp, h⟩ := inline_spec (R := Den (stInterp ℝ)) (J := fun x => liftInterp (δ x))
    (φ := φ) (gad := liftGad amp) (inp := inp) (c := .const)
    (fun _ _ _ _ hp h => h.mono hp) (den_const gs) hinp
    (fun o _ _ _ _ gs' hgs h₁ h₂ => liftGad_spec (hamp.mono hgs) h₁ h₂ o) B
  refine ⟨hp, (DenL.of_forall₂ h).congr fun x => ?_⟩
  simp [Circuit.eval]

/-- The lifted circuit as a circuit on `m + 1` inputs: inputs `0, …, m - 1` carry the
inputs of the Boolean circuit at amplitude `Δ`, and input `m` carries `Δ`. -/
def liftCircuit (B : Circuit BoolOp m) : Circuit STOp (m + 1) :=
  let p := liftB B (fun i => .input i.castSucc) (.input (Fin.last m)) []
  ⟨p.1, p.2⟩

/-- **Lemma `lem:lift` (lifting a Boolean circuit).**  The lifted circuit has at most
`3 s` gates and, given the inputs of the Boolean circuit as values `Δ·βᵢ` for a value
`Δ ≥ 0` supplied as input `m`, outputs `Δ` times the Boolean outputs. -/
theorem lift (B : Circuit BoolOp m) :
    (liftCircuit B).size ≤ 3 * B.size ∧
      ∀ (Δ : ℝ), 0 ≤ Δ → ∀ β : Fin m → Bool,
        (liftCircuit B).eval (stInterp ℝ) (Fin.snoc (fun i => ampl Δ (β i)) Δ)
          = (B.eval boolInterp β).map (ampl Δ) := by
  refine ⟨by simpa [liftCircuit, Circuit.size, length_liftB] using liftCost_sum_le B,
    fun Δ hΔ β => ?_⟩
  have h := ((liftB_spec (B := B) (hamp := den_input [] (Fin.last m))
    (hinp := fun i => den_input [] i.castSucc)).2.eval (Fin.snoc (fun i => ampl Δ (β i)) Δ))
  simp only [Fin.snoc_last, Fin.snoc_castSucc] at h
  exact h.trans (eval_liftInterp hΔ B β)

/-- A signed tropical circuit whose inputs are all `0` carries `0` on every wire. -/
theorem wires_eq_zero (gs : List (Gate STOp n)) :
    ∀ v ∈ wires (stInterp ℝ) (fun _ => 0) gs, v = 0 := by
  have h := wires_map (fun _ : Unit => (0 : ℝ)) (I := ⟨(), fun _ _ _ => ()⟩)
    (J := stInterp ℝ) (fun _ => ()) rfl (fun o _ _ => by cases o <;> simp [stInterp]) gs
  intro v hv
  rw [show (fun _ : Fin n => (0 : ℝ)) = (fun _ : Unit => (0 : ℝ)) ∘ fun _ => () from rfl,
    h] at hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv
  rfl

/-- **Vanishing at `Δ = 0`** (`lem:lift`): every wire of the lifted circuit carries `0`. -/
theorem lift_vanish (B : Circuit BoolOp m) (β : Fin m → Bool) :
    ∀ v ∈ wires (stInterp ℝ) (Fin.snoc (fun i => ampl 0 (β i)) 0) (liftCircuit B).gates,
      v = 0 := by
  have : (Fin.snoc (fun i => ampl 0 (β i)) 0 : Fin (m + 1) → ℝ) = fun _ => 0 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · cases β j <;> simp [ampl]
  rw [this]
  exact wires_eq_zero _

end SignedTropical
