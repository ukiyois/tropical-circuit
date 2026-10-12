import SignedTropical.Circuit
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# Gate sets

`signed_assignment.tex`, Definition `def:models` and Definition `def:lattice`.

* A *signed tropical* circuit has binary `max`, `+` and `-` gates; its sources are the
  inputs and the constant `0` (`STOp`, `stInterp`).
* A *Boolean* circuit has `∧`, `∨` and `¬` gates; its sources are the input bits and the
  constant `false` (`BoolOp`, `boolInterp`).  The negation gate reads its first operand.
* A *lattice* circuit has binary `min` and `max` gates and no constants (`LatOp`,
  `latInterp`).  Read over `Bool`, where `min` is `∧` and `max` is `∨`, the same circuits
  are the monotone Boolean circuits without constants of Definition `def:lattice`.  The
  absence of constants is the predicate `IsLattice` of `Lattice.lean`.
* The *subtraction-free* gate set of Corollary F has `min`, `+` and `max` gates (`TropOp`,
  `tropInterp`), with the same sources as the signed tropical one.

Size is the number of gates in every model (`Circuit.size`).
-/

namespace SignedTropical

/-- Signed tropical gates. -/
inductive STOp
  | max
  | add
  | sub
  deriving DecidableEq, Repr

/-- Signed tropical gates read in an ordered ring, with constant source `0`. -/
def stInterp (R : Type) [Zero R] [Add R] [Sub R] [Max R] : Interp STOp R where
  zero := 0
  op
    | .max, a, b => max a b
    | .add, a, b => a + b
    | .sub, a, b => a - b

/-- Boolean gates.  `not` reads its first operand. -/
inductive BoolOp
  | and
  | or
  | not
  deriving DecidableEq, Repr

instance : Fintype BoolOp :=
  ⟨{.and, .or, .not}, fun o => by cases o <;> simp⟩

theorem card_boolOp : Fintype.card BoolOp = 3 := rfl

/-- Boolean gates read in `Bool`, with constant source `false`. -/
def boolInterp : Interp BoolOp Bool where
  zero := false
  op
    | .and, a, b => a && b
    | .or, a, b => a || b
    | .not, a, _ => !a

/-- Lattice gates. -/
inductive LatOp
  | min
  | max
  deriving DecidableEq, Repr

/-- Lattice gates read in a linear order.  The constant `z` is never read by a lattice
circuit (`IsLattice`); it only completes the structure. -/
def latInterp (α : Type) [LinearOrder α] (z : α) : Interp LatOp α where
  zero := z
  op
    | .min, a, b => min a b
    | .max, a, b => max a b

/-- The gates of the subtraction-free fragment `(min, +, max)`. -/
inductive TropOp
  | min
  | max
  | add
  deriving DecidableEq, Repr

/-- `(min, +, max)` gates read in `ℝ`, with constant source `0`. -/
noncomputable def tropInterp : Interp TropOp ℝ where
  zero := 0
  op
    | .min, a, b => min a b
    | .max, a, b => max a b
    | .add, a, b => a + b

/-- The indicator vector of a set of coordinates. -/
def indicator {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun e => decide (e ∈ S)

/-- Every vector of bits is the indicator vector of the set of its set entries. -/
theorem indicator_filter {m : ℕ} (V : Fin m → Bool) :
    indicator (Finset.univ.filter fun i => V i = true) = V := by
  funext i; simp [indicator]

/-- The set of set entries of `indicator J` is `J`. -/
theorem filter_indicator {m : ℕ} (J : Finset (Fin m)) :
    (Finset.univ.filter fun i => indicator J i = true) = J := by
  ext i; simp [indicator]

/-- The value of a little-endian list of bits: `bitsVal [b₀, b₁, …] = ∑ⱼ 2ʲ bⱼ`. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bitsVal l

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (b : Bool) (l : List Bool) :
    bitsVal (b :: l) = b.toNat + 2 * bitsVal l := rfl

theorem bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [pow_succ] <;> omega

/-- Splitting a bit list after `L` bits. -/
theorem bitsVal_eq_take_add (L : ℕ) (l : List Bool) :
    bitsVal l = bitsVal (l.take L) + 2 ^ L * bitsVal (l.drop L) := by
  induction L generalizing l with
  | zero => simp
  | succ L ih =>
    cases l with
    | nil => simp
    | cons b l => simp [ih l, pow_succ]; ring

/-- Truncating to `L` bits does not change a value below `2 ^ L`. -/
theorem bitsVal_take_of_lt {L : ℕ} {l : List Bool} (h : bitsVal l < 2 ^ L) :
    bitsVal (l.take L) = bitsVal l := by
  have := bitsVal_eq_take_add L l
  rcases Nat.eq_zero_or_pos (bitsVal (l.drop L)) with h0 | h0
  · simp [h0] at this; omega
  · have : 2 ^ L ≤ 2 ^ L * bitsVal (l.drop L) := Nat.le_mul_of_pos_right _ h0
    omega

end SignedTropical
