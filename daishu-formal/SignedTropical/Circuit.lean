import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction

/-!
# Circuits

`signed_assignment.tex`, Definition `def:models`: a circuit is a finite directed acyclic
graph with unrestricted fan-out whose sources are the input coordinates and one constant;
size is the number of gates.

Here a circuit on `n` inputs is a list of gates together with a list of output operands.
Gate `k` produces wire `k`.  An operand (`Arg`) is an input coordinate, the constant
source, or a wire.  Sources are operands, not gates, so `Circuit.size` is exactly the
number of operation gates.  Sharing is free: any number of gates may read the same wire.

Evaluation is total: a wire that does not exist yet reads the constant.  Such a reference
can be replaced by the constant source without changing any value or the size, so for gate
sets that contain a constant source this convention adds no expressive power.  Lattice
circuits have no constant source; for them `Lattice.lean` imposes well-formedness.

The main result is the homomorphism lemma `wires_map`: a map that sends the constant to
the constant and commutes with every operation commutes with evaluation.  Its form
`wires_map_of` only asks for commutation on values satisfying a predicate that holds at
every wire.

The second half sets up the builder discipline used for every construction: gates are
only ever appended, and `Den I gs a f` records that operand `a` carries `f x` at every
input `x` in the gate list `gs`; this is stable under appending (`Den.mono`).
-/

namespace SignedTropical

/-- An operand of a gate: an input coordinate, the constant source, or the wire produced
by gate `j`. -/
inductive Arg (n : ℕ) where
  | input (i : Fin n)
  | const
  | wire (j : ℕ)
  deriving DecidableEq, Repr

/-- A gate: an operation applied to two operands.  Unary operations ignore `b`. -/
structure Gate (Op : Type) (n : ℕ) where
  op : Op
  a : Arg n
  b : Arg n
  deriving DecidableEq, Repr

/-- A circuit on `n` inputs: gates in order, gate `k` producing wire `k`, and the list of
output operands. -/
structure Circuit (Op : Type) (n : ℕ) where
  gates : List (Gate Op n)
  outs : List (Arg n)
  deriving DecidableEq, Repr

/-- A reading of a gate set in a carrier `α`: the value of the constant source and the
meaning of each operation. -/
structure Interp (Op α : Type) where
  zero : α
  op : Op → α → α → α

variable {Op Op' α β : Type} {n : ℕ}

namespace Arg

/-- The value of an operand, given the input `x` and the values `ws` of the wires built so
far.  A wire that does not exist reads the constant. -/
def read (I : Interp Op α) (x : Fin n → α) (ws : List α) : Arg n → α
  | input i => x i
  | const => I.zero
  | wire j => ws.getD j I.zero

/-- An operand is valid after `k` gates if it is not a wire with index `≥ k`. -/
def Valid (k : ℕ) : Arg n → Prop
  | wire j => j < k
  | _ => True

theorem Valid.mono {a : Arg n} {k k' : ℕ} (h : a.Valid k) (hk : k ≤ k') : a.Valid k' := by
  cases a <;> simp_all [Valid]; omega

end Arg

/-- The value of a gate, given the values `ws` of the earlier wires. -/
def Gate.eval (I : Interp Op α) (x : Fin n → α) (ws : List α) (g : Gate Op n) : α :=
  I.op g.op (g.a.read I x ws) (g.b.read I x ws)

/-- The values of all wires, in order. -/
def wires (I : Interp Op α) (x : Fin n → α) (gs : List (Gate Op n)) : List α :=
  gs.foldl (fun ws g => ws ++ [g.eval I x ws]) []

namespace Circuit

/-- The size of a circuit is the number of its gates. -/
def size (C : Circuit Op n) : ℕ := C.gates.length

/-- The values of the outputs. -/
def eval (I : Interp Op α) (C : Circuit Op n) (x : Fin n → α) : List α :=
  C.outs.map (Arg.read I x (wires I x C.gates))

end Circuit

section Wires

variable (I : Interp Op α) (x : Fin n → α)

@[simp] theorem wires_nil : wires I x ([] : List (Gate Op n)) = [] := rfl

theorem wires_concat (gs : List (Gate Op n)) (g : Gate Op n) :
    wires I x (gs ++ [g]) = wires I x gs ++ [g.eval I x (wires I x gs)] := by
  simp [wires, List.foldl_append]

@[simp] theorem length_wires (gs : List (Gate Op n)) : (wires I x gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [wires_concat, ih]

theorem wires_isPrefix {gs gs' : List (Gate Op n)} (h : gs <+: gs') :
    wires I x gs <+: wires I x gs' := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t g ih =>
    rw [← List.append_assoc, wires_concat]
    exact ih.trans (List.prefix_append _ _)

/-- A valid operand reads the same value after more gates are appended. -/
theorem Arg.read_of_isPrefix {gs gs' : List (Gate Op n)} {a : Arg n}
    (ha : a.Valid gs.length) (h : gs <+: gs') :
    a.read I x (wires I x gs') = a.read I x (wires I x gs) := by
  cases a with
  | input i => rfl
  | const => rfl
  | wire j =>
    obtain ⟨t, ht⟩ := wires_isPrefix I x h
    simp only [Arg.read, ← ht]
    exact List.getD_append _ _ _ _ (by simpa [Arg.Valid] using ha)

end Wires

section Homomorphism

/-- **Homomorphism lemma, relative form.**  If `φ` sends the constant to the constant and
commutes with every operation on arguments satisfying `P`, and `P` holds at the constant,
at every input and at every wire, then evaluating over the image is the image of
evaluating. -/
theorem wires_map_of (φ : α → β) {I : Interp Op α} {J : Interp Op β} {x : Fin n → α}
    (P : α → Prop) (hz : φ I.zero = J.zero) (hPz : P I.zero) (hPx : ∀ i, P (x i))
    (hop : ∀ o a b, P a → P b → φ (I.op o a b) = J.op o (φ a) (φ b))
    (gs : List (Gate Op n)) (hP : ∀ v ∈ wires I x gs, P v) :
    wires J (φ ∘ x) gs = (wires I x gs).map φ := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wires_concat] at hP
    have ih := ih fun v hv => hP v (List.mem_append_left _ hv)
    have hread : ∀ a : Arg n, a.read J (φ ∘ x) ((wires I x gs).map φ)
        = φ (a.read I x (wires I x gs)) ∧ P (a.read I x (wires I x gs)) := by
      intro a
      cases a with
      | input i => exact ⟨rfl, hPx i⟩
      | const => exact ⟨hz.symm, hPz⟩
      | wire j =>
        simp only [Arg.read]
        by_cases hj : j < (wires I x gs).length
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
          exact ⟨List.getElem_map _, hP _ (List.mem_append_left _ (List.getElem_mem hj))⟩
        · rw [List.getD_eq_default _ _ (by simpa using hj),
            List.getD_eq_default _ _ (by simpa using hj)]
          exact ⟨hz.symm, hPz⟩
    rw [wires_concat, wires_concat, ih, List.map_append]
    simp only [List.map_cons, List.map_nil, Gate.eval, (hread g.a).1, (hread g.b).1]
    rw [hop _ _ _ (hread g.a).2 (hread g.b).2]

/-- **Homomorphism lemma.**  Evaluation commutes with any map that sends the constant to the
constant and commutes with every operation (`signed_assignment.tex`, the common source of
the threshold identity in the proof of Thm. `thm:lattice` and of amplitude lifting,
Lemma `lem:lift`). -/
theorem wires_map (φ : α → β) {I : Interp Op α} {J : Interp Op β} (x : Fin n → α)
    (hz : φ I.zero = J.zero) (hop : ∀ o a b, φ (I.op o a b) = J.op o (φ a) (φ b))
    (gs : List (Gate Op n)) :
    wires J (φ ∘ x) gs = (wires I x gs).map φ :=
  wires_map_of φ (fun _ => True) hz trivial (fun _ => trivial) (fun o a b _ _ => hop o a b) gs
    (fun _ _ => trivial)

theorem Arg.read_map (φ : α → β) {I : Interp Op α} {J : Interp Op β} (x : Fin n → α)
    (hz : φ I.zero = J.zero) (ws : List α) (a : Arg n) :
    a.read J (φ ∘ x) (ws.map φ) = φ (a.read I x ws) := by
  cases a with
  | input i => rfl
  | const => exact hz.symm
  | wire j =>
    simp only [Arg.read]
    by_cases hj : j < ws.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
      exact List.getElem_map _
    · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
      exact hz.symm

/-- **Homomorphism lemma for outputs**, relative form. -/
theorem Circuit.eval_map_of (φ : α → β) {I : Interp Op α} {J : Interp Op β} {x : Fin n → α}
    (P : α → Prop) (hz : φ I.zero = J.zero) (hPz : P I.zero) (hPx : ∀ i, P (x i))
    (hop : ∀ o a b, P a → P b → φ (I.op o a b) = J.op o (φ a) (φ b))
    (C : Circuit Op n) (hP : ∀ v ∈ wires I x C.gates, P v) :
    C.eval J (φ ∘ x) = (C.eval I x).map φ := by
  simp only [Circuit.eval, wires_map_of φ P hz hPz hPx hop C.gates hP, List.map_map]
  exact List.map_congr_left fun a _ => Arg.read_map φ x hz _ a

/-- **Homomorphism lemma for outputs.** -/
theorem Circuit.eval_map (φ : α → β) {I : Interp Op α} {J : Interp Op β} (x : Fin n → α)
    (hz : φ I.zero = J.zero) (hop : ∀ o a b, φ (I.op o a b) = J.op o (φ a) (φ b))
    (C : Circuit Op n) :
    C.eval J (φ ∘ x) = (C.eval I x).map φ :=
  C.eval_map_of φ (fun _ => True) hz trivial (fun _ => trivial) (fun o a b _ _ => hop o a b)
    (fun _ _ => trivial)

end Homomorphism

section Builder

/-! ### Builders

A builder extends a gate list and returns a result, typically operands.  All
constructions in this development are builders, and their specifications are stated
with `Den`. -/

/-- A builder over the gate set `Op` on `n` inputs. -/
abbrev Bld (Op : Type) (n : ℕ) (γ : Type) := List (Gate Op n) → List (Gate Op n) × γ

/-- Append one gate and return its wire. -/
def emit (o : Op) (a b : Arg n) : Bld Op n (Arg n) := fun gs =>
  (gs ++ [⟨o, a, b⟩], .wire gs.length)

/-- In the gate list `gs`, operand `a` is valid and carries `f x` at every input `x`. -/
def Den (I : Interp Op α) (gs : List (Gate Op n)) (a : Arg n) (f : (Fin n → α) → α) :
    Prop :=
  a.Valid gs.length ∧ ∀ x, a.read I x (wires I x gs) = f x

variable {I : Interp Op α}

theorem Den.mono {gs gs' : List (Gate Op n)} {a : Arg n} {f : (Fin n → α) → α}
    (h : Den I gs a f) (hp : gs <+: gs') : Den I gs' a f :=
  ⟨h.1.mono hp.length_le, fun x => (Arg.read_of_isPrefix I x h.1 hp).trans (h.2 x)⟩

theorem den_input (gs : List (Gate Op n)) (i : Fin n) : Den I gs (.input i) (fun x => x i) :=
  ⟨trivial, fun _ => rfl⟩

theorem den_const (gs : List (Gate Op n)) : Den I gs .const (fun _ => I.zero) :=
  ⟨trivial, fun _ => rfl⟩

theorem emit_fst (o : Op) (a b : Arg n) (gs : List (Gate Op n)) :
    (emit o a b gs).1 = gs ++ [⟨o, a, b⟩] := rfl

theorem isPrefix_emit (o : Op) (a b : Arg n) (gs : List (Gate Op n)) :
    gs <+: (emit o a b gs).1 := List.prefix_append _ _

theorem length_emit (o : Op) (a b : Arg n) (gs : List (Gate Op n)) :
    (emit o a b gs).1.length = gs.length + 1 := by simp [emit]

theorem den_emit {gs : List (Gate Op n)} {a b : Arg n} {f g : (Fin n → α) → α} (o : Op)
    (ha : Den I gs a f) (hb : Den I gs b g) :
    Den I (emit o a b gs).1 (emit o a b gs).2 (fun x => I.op o (f x) (g x)) := by
  refine ⟨by simp [emit, Arg.Valid], fun x => ?_⟩
  simp only [emit, Arg.read, wires_concat]
  rw [List.getD_append_right _ _ _ _ (by simp), length_wires, Nat.sub_self]
  simp [Gate.eval, ha.2 x, hb.2 x]

/-- A list of operands, read in the gate list `gs`, carries the list `F x`. -/
def DenL (I : Interp Op α) (gs : List (Gate Op n)) (as : List (Arg n))
    (F : (Fin n → α) → List α) : Prop :=
  (∀ a ∈ as, a.Valid gs.length) ∧ ∀ x, as.map (Arg.read I x (wires I x gs)) = F x

theorem DenL.mono {gs gs' : List (Gate Op n)} {as : List (Arg n)} {F : (Fin n → α) → List α}
    (h : DenL I gs as F) (hp : gs <+: gs') : DenL I gs' as F := by
  refine ⟨fun a ha => (h.1 a ha).mono hp.length_le, fun x => ?_⟩
  rw [← h.2 x]
  exact List.map_congr_left fun a ha => Arg.read_of_isPrefix I x (h.1 a ha) hp

theorem denL_nil (gs : List (Gate Op n)) : DenL I gs [] (fun _ => []) :=
  ⟨by simp, fun _ => rfl⟩

theorem DenL.cons {gs : List (Gate Op n)} {a : Arg n} {as : List (Arg n)}
    {f : (Fin n → α) → α} {F : (Fin n → α) → List α} (ha : Den I gs a f)
    (has : DenL I gs as F) : DenL I gs (a :: as) (fun x => f x :: F x) :=
  ⟨by simpa using ⟨ha.1, has.1⟩, fun x => by simp [ha.2 x, ← has.2 x]⟩

/-- Splitting a denoted list into its head and tail. -/
theorem DenL.uncons {gs : List (Gate Op n)} {a : Arg n} {as : List (Arg n)}
    {F : (Fin n → α) → List α} (h : DenL I gs (a :: as) F) :
    Den I gs a (fun x => (F x).headD I.zero) ∧ DenL I gs as (fun x => (F x).tail) ∧
      ∀ x, F x = (F x).headD I.zero :: (F x).tail := by
  refine ⟨⟨h.1 a (by simp), fun x => ?_⟩, ⟨fun c hc => h.1 c (by simp [hc]), fun x => ?_⟩,
    fun x => ?_⟩
  · show _ = (F x).headD I.zero
    rw [← h.2 x]; rfl
  · show _ = (F x).tail
    rw [← h.2 x]; rfl
  · rw [← h.2 x]; rfl

theorem DenL.congr {gs : List (Gate Op n)} {as : List (Arg n)} {F G : (Fin n → α) → List α}
    (h : DenL I gs as F) (hFG : ∀ x, F x = G x) : DenL I gs as G :=
  ⟨h.1, fun x => (h.2 x).trans (hFG x)⟩

theorem Den.congr {gs : List (Gate Op n)} {a : Arg n} {f g : (Fin n → α) → α}
    (h : Den I gs a f) (hfg : ∀ x, f x = g x) : Den I gs a g :=
  ⟨h.1, fun x => (h.2 x).trans (hfg x)⟩

/-- A list of operands, each denoting its own value, denotes the list of values. -/
theorem DenL.map {β : Type} {gs : List (Gate Op n)} {g : β → Arg n}
    {G : β → (Fin n → α) → α} :
    ∀ (l : List β), (∀ b ∈ l, Den I gs (g b) (G b)) →
      DenL I gs (l.map g) (fun x => l.map fun b => G b x)
  | [], _ => denL_nil gs
  | b :: l, h => DenL.cons (h b (by simp)) (DenL.map l fun c hc => h c (by simp [hc]))

theorem DenL.append {gs : List (Gate Op n)} {as bs : List (Arg n)}
    {F G : (Fin n → α) → List α} (ha : DenL I gs as F) (hb : DenL I gs bs G) :
    DenL I gs (as ++ bs) (fun x => F x ++ G x) := by
  refine ⟨fun a h => ?_, fun x => by simp [← ha.2 x, ← hb.2 x]⟩
  rcases List.mem_append.1 h with h | h
  exacts [ha.1 a h, hb.1 a h]

theorem DenL.length_eq {gs : List (Gate Op n)} {as : List (Arg n)}
    {F : (Fin n → α) → List α} (h : DenL I gs as F) (x : Fin n → α) :
    (F x).length = as.length := by
  rw [← h.2 x, List.length_map]

/-- The `j`-th operand of a list carries the `j`-th entry. -/
theorem DenL.getD {gs : List (Gate Op n)} {as : List (Arg n)} {F : (Fin n → α) → List α}
    (h : DenL I gs as F) (j : ℕ) :
    Den I gs (as.getD j .const) (fun x => (F x).getD j I.zero) := by
  by_cases hj : j < as.length
  · rw [List.getD_eq_getElem _ _ hj]
    refine ⟨h.1 _ (List.getElem_mem hj), fun x => ?_⟩
    show _ = (F x).getD j I.zero
    rw [← h.2 x, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega)]
    refine ⟨trivial, fun x => ?_⟩
    show I.zero = (F x).getD j I.zero
    rw [List.getD_eq_default _ _ (by rw [h.length_eq x]; omega)]

/-- The circuit made of a gate list and output operands evaluates to what the operands
denote. -/
theorem DenL.eval {gs : List (Gate Op n)} {as : List (Arg n)} {F : (Fin n → α) → List α}
    (h : DenL I gs as F) (x : Fin n → α) : (Circuit.mk gs as).eval I x = F x :=
  h.2 x

end Builder

end SignedTropical
