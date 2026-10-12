import SignedTropical.Models
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# A sorting network over `max`, `+`, `-`

`signed_assignment.tex`, Section `sec:amplitude`: the compiler needs the order statistics
of `D`, computed by a fixed comparator network.  The network used here is insertion sort:
inserting `a` into a list `b₁ ≤ b₂ ≤ ⋯` by the comparators
`(a, b₁), (max a b₁, b₂), …` (`insV`), and sorting by inserting the entries one at a time
(`isortV`).  On a list of length `k` it has `k (k - 1) / 2` comparators.

A comparator costs three signed tropical gates: `max a b`, `a + b`, and
`min a b = (a + b) - max a b` (`cmpB`).

The network computes `List.insertionSort` exactly (`isortV_eq_insertionSort`), so its
correctness is Mathlib's `List.sortedLE_insertionSort` and `List.perm_insertionSort`; no
0-1 principle is needed.  The paper uses Batcher's network at `O(m log² m)` comparators;
`BLUEPRINT.md` planned odd-even transposition.  Both have a quadratic or smaller cost,
which the `m²` term of the compiler already absorbs.
-/

namespace SignedTropical

variable {n : ℕ}

/-! ### The network on values -/

/-- Insert `a` by a chain of comparators. -/
def insV {α : Type} [LinearOrder α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => min a b :: insV (max a b) l

/-- Insertion sort as a comparator network. -/
def isortV {α : Type} [LinearOrder α] : List α → List α
  | [] => []
  | a :: l => insV a (isortV l)

section Values

variable {α : Type} [LinearOrder α]

theorem insV_of_forall_le {a : α} :
    ∀ {l : List α}, l.Pairwise (· ≤ ·) → (∀ b ∈ l, a ≤ b) → insV a l = a :: l
  | [], _, _ => rfl
  | b :: l, hl, ha => by
    have hab : a ≤ b := ha b (by simp)
    have hbl : ∀ c ∈ l, b ≤ c := (List.pairwise_cons.1 hl).1
    simp only [insV, min_eq_left hab, max_eq_right hab,
      insV_of_forall_le (List.pairwise_cons.1 hl).2 hbl]

theorem insV_eq_orderedInsert (a : α) :
    ∀ {l : List α}, l.Pairwise (· ≤ ·) → insV a l = l.orderedInsert (· ≤ ·) a
  | [], _ => rfl
  | b :: l, hl => by
    by_cases hab : a ≤ b
    · rw [List.orderedInsert_cons_of_le _ _ hab, insV, min_eq_left hab, max_eq_right hab,
        insV_of_forall_le (List.pairwise_cons.1 hl).2 (List.pairwise_cons.1 hl).1]
    · have hba : b ≤ a := le_of_not_ge hab
      rw [List.orderedInsert_of_not_le _ _ hab, insV, min_eq_right hba, max_eq_left hba,
        insV_eq_orderedInsert a (List.pairwise_cons.1 hl).2]

/-- **The network computes insertion sort.** -/
theorem isortV_eq_insertionSort : ∀ l : List α, isortV l = l.insertionSort (· ≤ ·)
  | [] => rfl
  | a :: l => by
    rw [isortV, isortV_eq_insertionSort l, List.insertionSort_cons,
      insV_eq_orderedInsert a (List.pairwise_insertionSort _ l)]

end Values

/-! ### The network as a signed tropical builder -/

/-- A comparator: returns `(min a b, max a b)` at three gates. -/
def cmpB (a b : Arg n) : Bld STOp n (Arg n × Arg n) := fun gs =>
  let p₁ := emit .max a b gs
  let p₂ := emit .add a b p₁.1
  let p₃ := emit .sub p₂.2 p₁.2 p₂.1
  (p₃.1, (p₃.2, p₁.2))

/-- Insertion of `a` into a list of operands. -/
def insB (a : Arg n) : List (Arg n) → Bld STOp n (List (Arg n))
  | [] => fun gs => (gs, [a])
  | b :: l => fun gs =>
    let p := cmpB a b gs
    let q := insB p.2.2 l p.1
    (q.1, p.2.1 :: q.2)

/-- The insertion-sort network on a list of operands. -/
def isortB : List (Arg n) → Bld STOp n (List (Arg n))
  | [] => fun gs => (gs, [])
  | a :: l => fun gs =>
    let p := isortB l gs
    insB a p.2 p.1

section Spec

variable {gs : List (Gate STOp n)}

theorem cmpB_spec {a b : Arg n} {f g : (Fin n → ℝ) → ℝ} (ha : Den (stInterp ℝ) gs a f)
    (hb : Den (stInterp ℝ) gs b g) :
    gs <+: (cmpB a b gs).1 ∧ (cmpB a b gs).1.length = gs.length + 3 ∧
      Den (stInterp ℝ) (cmpB a b gs).1 (cmpB a b gs).2.1 (fun x => min (f x) (g x)) ∧
      Den (stInterp ℝ) (cmpB a b gs).1 (cmpB a b gs).2.2 (fun x => max (f x) (g x)) := by
  have p₁ : gs <+: (emit STOp.max a b gs).1 := isPrefix_emit _ _ _ _
  have h₁ := den_emit STOp.max ha hb
  have p₂ : (emit STOp.max a b gs).1 <+: (emit STOp.add a b (emit STOp.max a b gs).1).1 :=
    isPrefix_emit _ _ _ _
  have h₂ := den_emit STOp.add (ha.mono p₁) (hb.mono p₁)
  have h₃ := den_emit STOp.sub h₂ (h₁.mono p₂)
  refine ⟨(p₁.trans p₂).trans (isPrefix_emit _ _ _ _), by simp [cmpB, length_emit],
    h₃.congr fun x => ?_, h₁.mono (p₂.trans (isPrefix_emit _ _ _ _))⟩
  simp only [stInterp]
  linarith [min_add_max (f x) (g x)]

theorem insB_spec {a : Arg n} {f : (Fin n → ℝ) → ℝ} :
    ∀ {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      Den (stInterp ℝ) gs a f → DenL (stInterp ℝ) gs l F →
      gs <+: (insB a l gs).1 ∧ (insB a l gs).1.length = gs.length + 3 * l.length ∧
        DenL (stInterp ℝ) (insB a l gs).1 (insB a l gs).2 (fun x => insV (f x) (F x))
  | [], F, gs, ha, hl => by
    refine ⟨List.prefix_refl _, by simp [insB], (DenL.cons ha (denL_nil gs)).congr fun x => ?_⟩
    rw [show F x = [] by rw [← hl.2 x]; rfl]
    rfl
  | b :: l, F, gs, ha, hbl => by
    obtain ⟨hb, hl, hF⟩ := hbl.uncons
    obtain ⟨hp, hlen, hmin, hmax⟩ := cmpB_spec ha hb
    obtain ⟨hq, hlen', hrest⟩ := insB_spec hmax (hl.mono hp)
    refine ⟨hp.trans hq, by simp [insB, hlen', hlen]; ring,
      (DenL.cons (hmin.mono hq) hrest).congr fun x => ?_⟩
    rw [hF x, insV]
    rfl

theorem isortB_spec :
    ∀ {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs l F →
      gs <+: (isortB l gs).1 ∧
        (isortB l gs).1.length = gs.length + 3 * (List.range l.length).sum ∧
        DenL (stInterp ℝ) (isortB l gs).1 (isortB l gs).2 (fun x => isortV (F x))
  | [], F, gs, hl => by
    refine ⟨List.prefix_refl _, by simp [isortB], hl.congr fun x => ?_⟩
    rw [show F x = [] by rw [← hl.2 x]; rfl]
    rfl
  | a :: l, F, gs, hal => by
    obtain ⟨ha, hl, hF⟩ := hal.uncons
    obtain ⟨hp, hlen, hsort⟩ := isortB_spec hl
    have hlen2 : (isortB l gs).2.length = l.length := by
      rw [← hsort.length_eq (fun _ => 0), ← hl.length_eq (fun _ => 0), isortV_eq_insertionSort,
        List.length_insertionSort]
    obtain ⟨hq, hlen', hins⟩ := insB_spec (ha.mono hp) hsort
    refine ⟨hp.trans hq, ?_, hins.congr fun x => ?_⟩
    · simp only [isortB, hlen', hlen, hlen2, List.length_cons, List.range_succ, List.sum_append,
        List.sum_singleton]
      ring
    · rw [hF x, isortV]
      rfl

end Spec

end SignedTropical
