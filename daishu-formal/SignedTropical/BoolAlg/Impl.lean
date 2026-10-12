import SignedTropical.Inline
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Composing builders: representations and implementations

The algorithms of Phase 2 (`greedy_intersection.tex`, Lemma `lem:observer` and the proof of
Theorem `thm:D`) are built as Boolean circuits by appending gadgets to a gate list, in the
builder style of `Circuit.lean`.  This module is the composition layer, for any gate set.

* A *representation* `R : Rep Op α n σ τ` says when an object `s : σ` made of operands carries
  a value `T x : τ` at every input `x` in a given gate list (`R.rep gs s T`); it survives
  appending gates (`R.mono`).  Basic representations: one operand (`Rep.arg`, which is `Den`),
  a list of `L` operands (`Rep.list`, which is `DenL`), pairs (`Rep.prod`) and families
  (`Rep.pi`).
* `Impl R₁ R₂ b c F`: the builder `b` *implements* `F : τ₁ → τ₂` from `R₁` to `R₂` with exactly
  `c` gates.  Whenever `s` carries `T` in `gs`, `b s gs` extends `gs` by exactly `c` gates and
  returns an object carrying `x ↦ F (T x)`.  Unfolded, this is the Phase 1 form of a gadget
  specification: prefix, gate count, `Den`/`DenL`.
* Composition, with sizes added or multiplied exactly: `Impl.comp` (sequential composition,
  functions compose), `Impl.pair` (two builders on the same object), `Impl.extend` (keep the
  object and add a computed value), `Impl.free` (rearranging operands costs no gate),
  `Impl.pre` and `Impl.post` (rearranging before or after), `Impl.tab` (one builder per index
  `i < r`; `Impl.tabSum` when the cost depends on the index), `Impl.map` and `Impl.map₂` (a
  gadget at every index), `Impl.iterate` (`k` rounds, `F^[k]`), `Impl.fold` (one round per
  element of a list), `Impl.scan` (`k` rounds, keeping every intermediate object).
* Rounds of an algorithm that reads a fixed context `a` (for instance its input) and updates a
  state: `Impl.iterateCtx` (`k` rounds, `(F a)^[k]`), `Impl.scanCtx` (every intermediate
  state) and `Impl.foldCtx` (one round per element of a list, the round depending on the
  element).
* Running a circuit `C` on operands computed inside the circuit (`runB`, `runB_impl`): `C.size`
  gates, and the value is `C` evaluated at the carried values.
* Back to circuits: `circuitOf b` applies `b` to the input operands; an implementation of `F`
  from the inputs is a circuit of size `c` computing `F` (`circuitOf_spec`).  Sequential
  composition of two circuits (`seqCircuit`, `seqCircuit_spec`) is the special case of two
  `runB`.
-/

namespace SignedTropical.BoolAlg

variable {Op α σ σ₁ σ₂ σ₃ τ τ₁ τ₂ τ₃ β γ : Type} {n : ℕ}

/-! ### Representations -/

/-- A representation of values of type `τ` by objects of type `σ` made of operands: in the gate
list `gs`, `s` carries `T x` at every input `x` (`rep gs s T`).  Appending gates keeps a
representation. -/
structure Rep (Op α : Type) (n : ℕ) (σ τ : Type) where
  /-- In the gate list `gs`, the object `s` carries `T x` at every input `x`. -/
  rep : List (Gate Op n) → σ → ((Fin n → α) → τ) → Prop
  /-- Appending gates keeps a representation. -/
  mono : ∀ {gs gs' : List (Gate Op n)} {s : σ} {T : (Fin n → α) → τ}, gs <+: gs' →
    rep gs s T → rep gs' s T

namespace Rep

/-- One operand carrying one value: `Den`. -/
def arg (I : Interp Op α) : Rep Op α n (Arg n) α :=
  ⟨Den I, fun hp h => h.mono hp⟩

/-- A list of `L` operands carrying a list of values: `DenL`. -/
def list (I : Interp Op α) (L : ℕ) : Rep Op α n (List (Arg n)) (List α) :=
  ⟨fun gs as A => as.length = L ∧ DenL I gs as A, fun hp h => ⟨h.1, h.2.mono hp⟩⟩

/-- Pairs, componentwise. -/
def prod (R₁ : Rep Op α n σ₁ τ₁) (R₂ : Rep Op α n σ₂ τ₂) : Rep Op α n (σ₁ × σ₂) (τ₁ × τ₂) :=
  ⟨fun gs s T => R₁.rep gs s.1 (fun x => (T x).1) ∧ R₂.rep gs s.2 (fun x => (T x).2),
    fun hp h => ⟨R₁.mono hp h.1, R₂.mono hp h.2⟩⟩

/-- Families indexed by `ι`, entrywise. -/
def pi (ι : Type) (R : Rep Op α n σ τ) : Rep Op α n (ι → σ) (ι → τ) :=
  ⟨fun gs s T => ∀ i, R.rep gs (s i) (fun x => T x i), fun hp h i => R.mono hp (h i)⟩

/-- Rewriting the carried values pointwise. -/
theorem congr (R : Rep Op α n σ τ) {gs : List (Gate Op n)} {s : σ} {T T' : (Fin n → α) → τ}
    (h : R.rep gs s T) (hT : ∀ x, T x = T' x) : R.rep gs s T' :=
  funext hT ▸ h

end Rep

/-! ### Implementations -/

/-- The builder `b` *implements* `F` from `R₁` to `R₂` with exactly `c` gates: whenever `s`
carries `T` in a gate list `gs`, `b s gs` extends `gs` by exactly `c` gates and returns an
object carrying `x ↦ F (T x)`. -/
def Impl (R₁ : Rep Op α n σ₁ τ₁) (R₂ : Rep Op α n σ₂ τ₂) (b : σ₁ → Bld Op n σ₂) (c : ℕ)
    (F : τ₁ → τ₂) : Prop :=
  ∀ ⦃gs : List (Gate Op n)⦄ ⦃s : σ₁⦄ ⦃T : (Fin n → α) → τ₁⦄, R₁.rep gs s T →
    gs <+: (b s gs).1 ∧ (b s gs).1.length = gs.length + c ∧
      R₂.rep (b s gs).1 (b s gs).2 (fun x => F (T x))

/-! ### Builders -/

/-- Run `b₁`, then `b₂` on its result. -/
def seqB (b₁ : σ₁ → Bld Op n σ₂) (b₂ : σ₂ → Bld Op n σ₃) : σ₁ → Bld Op n σ₃ := fun s gs =>
  let p := b₁ s gs
  b₂ p.2 p.1

/-- Run `b₁` and then `b₂` on the same object, and pair the results. -/
def pairB (b₁ : σ → Bld Op n σ₁) (b₂ : σ → Bld Op n σ₂) : σ → Bld Op n (σ₁ × σ₂) :=
  fun s gs =>
    let p := b₁ s gs
    let q := b₂ s p.1
    (q.1, (p.2, q.2))

/-- Rearrange operands, appending no gate. -/
def pureB (g : σ₁ → σ₂) : σ₁ → Bld Op n σ₂ := fun s gs => (gs, g s)

/-- Run `b 0, …, b (r-1)` in this order and collect the results. -/
def tabB : {r : ℕ} → (Fin r → Bld Op n γ) → Bld Op n (Fin r → γ)
  | 0, _ => fun gs => (gs, Fin.elim0)
  | _ + 1, b => fun gs =>
    let p := b 0 gs
    let q := tabB (fun i => b i.succ) p.1
    (q.1, Fin.cons p.2 q.2)

/-- `k` rounds of `b`. -/
def iterB (b : σ → Bld Op n σ) : ℕ → σ → Bld Op n σ
  | 0 => pureB fun s => s
  | k + 1 => seqB b (iterB b k)

/-- One round of `b a` for each element `a` of a list, in order. -/
def foldB (b : β → σ → Bld Op n σ) : List β → σ → Bld Op n σ
  | [] => pureB fun s => s
  | a :: l => seqB (b a) (foldB b l)

/-- `k` rounds of `b`, keeping every intermediate object: entry `i` is the object after `i`
rounds. -/
def scanB (b : σ → Bld Op n σ) : (k : ℕ) → σ → Bld Op n (Fin (k + 1) → σ)
  | 0 => fun s gs => (gs, fun _ => s)
  | k + 1 => fun s gs =>
    let p := b s gs
    let q := scanB b k p.2 p.1
    (q.1, Fin.cons s q.2)

/-- `k` rounds of `b`, which reads a fixed context and replaces the state; the result is the
final state. -/
def iterCtxB (b : σ₁ × σ₂ → Bld Op n σ₂) (k : ℕ) (s : σ₁ × σ₂) : Bld Op n σ₂ := fun gs =>
  let q := iterB (pairB (pureB Prod.fst) b) k s gs
  (q.1, q.2.2)

/-- `k` rounds of `b` with a fixed context, keeping every intermediate state: entry `i` is the
state after `i` rounds. -/
def scanCtxB (b : σ₁ × σ₂ → Bld Op n σ₂) (k : ℕ) (s : σ₁ × σ₂) :
    Bld Op n (Fin (k + 1) → σ₂) := fun gs =>
  let q := scanB (pairB (pureB Prod.fst) b) k s gs
  (q.1, fun i => (q.2 i).2)

/-- One round of `b a` for each element `a` of a list, in order; each round reads a fixed
context and replaces the state, and the result is the final state. -/
def foldCtxB (b : β → σ₁ × σ₂ → Bld Op n σ₂) (l : List β) (s : σ₁ × σ₂) : Bld Op n σ₂ :=
  fun gs =>
    let q := foldB (fun a => pairB (pureB Prod.fst) (b a)) l s gs
    (q.1, q.2.2)

/-- `tabB`, pointful form with costs depending on the index: if every `b i` extends every gate
list extending `gs₀` by exactly `c i` gates and returns an object carrying `F i`, then `tabB b`
extends `gs₀` by exactly `∑ i, c i` gates and its family of results carries `(F i)ᵢ`. -/
theorem tabB_sum_spec {R₂ : Rep Op α n σ₂ τ₂} :
    ∀ {r : ℕ} {b : Fin r → Bld Op n σ₂} {c : Fin r → ℕ} {F : Fin r → (Fin n → α) → τ₂}
      {gs₀ : List (Gate Op n)},
      (∀ i gs, gs₀ <+: gs → gs <+: (b i gs).1 ∧ (b i gs).1.length = gs.length + c i ∧
        R₂.rep (b i gs).1 (b i gs).2 (F i)) →
      gs₀ <+: (tabB b gs₀).1 ∧ (tabB b gs₀).1.length = gs₀.length + ∑ i, c i ∧
        (Rep.pi (Fin r) R₂).rep (tabB b gs₀).1 (tabB b gs₀).2 (fun x i => F i x)
  | 0, _, _, _, _, _ => ⟨List.prefix_refl _, by simp [tabB], fun i => i.elim0⟩
  | r + 1, b, c, F, gs₀, h => by
    obtain ⟨hp₁, hl₁, hr₁⟩ := h 0 gs₀ (List.prefix_refl _)
    obtain ⟨hp₂, hl₂, hr₂⟩ := tabB_sum_spec (b := fun i => b i.succ) (c := fun i => c i.succ)
      (F := fun i => F i.succ) (gs₀ := (b 0 gs₀).1) fun i gs hgs => h i.succ gs (hp₁.trans hgs)
    refine ⟨hp₁.trans hp₂, hl₂.trans (by rw [hl₁, Fin.sum_univ_succ]; ring), fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact R₂.mono hp₂ hr₁
    · exact hr₂ j

/-- `tabB`, pointful form: if every `b i` extends every gate list extending `gs₀` by exactly `c`
gates and returns an object carrying `F i`, then `tabB b` extends `gs₀` by exactly `r c` gates
and its family of results carries `(F i)ᵢ`. -/
theorem tabB_spec {R₂ : Rep Op α n σ₂ τ₂} {c r : ℕ} {b : Fin r → Bld Op n σ₂}
    {F : Fin r → (Fin n → α) → τ₂} {gs₀ : List (Gate Op n)}
    (h : ∀ i gs, gs₀ <+: gs → gs <+: (b i gs).1 ∧ (b i gs).1.length = gs.length + c ∧
      R₂.rep (b i gs).1 (b i gs).2 (F i)) :
    gs₀ <+: (tabB b gs₀).1 ∧ (tabB b gs₀).1.length = gs₀.length + r * c ∧
      (Rep.pi (Fin r) R₂).rep (tabB b gs₀).1 (tabB b gs₀).2 (fun x i => F i x) := by
  obtain ⟨hp, hl, hr⟩ := tabB_sum_spec (c := fun _ => c) h
  exact ⟨hp, by simpa using hl, hr⟩

/-- Rounds that keep a context: `k` rounds of `t ↦ (t.1, F t.1 t.2)` from `(a, s)` keep `a` and
apply `F a` `k` times to `s`. -/
theorem iterate_ctx (F : τ₁ → τ₂ → τ₂) (a : τ₁) (s : τ₂) (k : ℕ) :
    (fun t : τ₁ × τ₂ => (t.1, F t.1 t.2))^[k] (a, s) = (a, (F a)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

/-- Rounds over a list that keep a context `a` apply `F e a` for the elements `e` in order. -/
theorem foldl_ctx (F : β → τ₁ → τ₂ → τ₂) (a : τ₁) (s : τ₂) (l : List β) :
    l.foldl (fun t e => (t.1, F e t.1 t.2)) (a, s) = (a, l.foldl (fun t e => F e a t) s) := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih => exact ih (F e a s)

namespace Impl

variable {R : Rep Op α n σ τ} {R₁ : Rep Op α n σ₁ τ₁} {R₂ : Rep Op α n σ₂ τ₂}
  {R₃ : Rep Op α n σ₃ τ₃}

/-- Rewriting the gate count. -/
theorem cost {b : σ₁ → Bld Op n σ₂} {c c' : ℕ} {F : τ₁ → τ₂} (h : Impl R₁ R₂ b c F)
    (hc : c = c') : Impl R₁ R₂ b c' F :=
  hc ▸ h

/-- Rewriting the implemented function pointwise. -/
theorem congr {b : σ₁ → Bld Op n σ₂} {c : ℕ} {F G : τ₁ → τ₂} (h : Impl R₁ R₂ b c F)
    (hF : ∀ t, F t = G t) : Impl R₁ R₂ b c G :=
  funext hF ▸ h

/-- **Sequential composition**: costs add and functions compose. -/
theorem comp {b₁ : σ₁ → Bld Op n σ₂} {b₂ : σ₂ → Bld Op n σ₃} {c₁ c₂ : ℕ} {F₁ : τ₁ → τ₂}
    {F₂ : τ₂ → τ₃} (h₁ : Impl R₁ R₂ b₁ c₁ F₁) (h₂ : Impl R₂ R₃ b₂ c₂ F₂) :
    Impl R₁ R₃ (seqB b₁ b₂) (c₁ + c₂) (fun t => F₂ (F₁ t)) := by
  intro gs s T hs
  obtain ⟨hp₁, hl₁, hr₁⟩ := h₁ hs
  obtain ⟨hp₂, hl₂, hr₂⟩ := h₂ hr₁
  exact ⟨hp₁.trans hp₂, hl₂.trans (by rw [hl₁, Nat.add_assoc]), hr₂⟩

/-- **Two builders on the same object**, paired: costs add. -/
theorem pair {b₁ : σ → Bld Op n σ₁} {b₂ : σ → Bld Op n σ₂} {c₁ c₂ : ℕ} {F₁ : τ → τ₁}
    {F₂ : τ → τ₂} (h₁ : Impl R R₁ b₁ c₁ F₁) (h₂ : Impl R R₂ b₂ c₂ F₂) :
    Impl R (R₁.prod R₂) (pairB b₁ b₂) (c₁ + c₂) (fun t => (F₁ t, F₂ t)) := by
  intro gs s T hs
  obtain ⟨hp₁, hl₁, hr₁⟩ := h₁ hs
  obtain ⟨hp₂, hl₂, hr₂⟩ := h₂ (R.mono hp₁ hs)
  exact ⟨hp₁.trans hp₂, hl₂.trans (by rw [hl₁, Nat.add_assoc]), R₁.mono hp₂ hr₁, hr₂⟩

/-- **Rearranging operands is free.** -/
theorem free {g : σ₁ → σ₂} {F : τ₁ → τ₂}
    (h : ∀ ⦃gs s T⦄, R₁.rep gs s T → R₂.rep gs (g s) (fun x => F (T x))) :
    Impl R₁ R₂ (pureB g) 0 F :=
  fun _ _ _ hs => ⟨List.prefix_refl _, rfl, h hs⟩

/-- The object itself, free. -/
theorem self : Impl R R (pureB fun s => s) 0 (fun t => t) :=
  free fun _ _ _ hs => hs

/-- The first component, free. -/
theorem fst : Impl (R₁.prod R₂) R₁ (pureB Prod.fst) 0 Prod.fst :=
  free fun _ _ _ hs => hs.1

/-- The second component, free. -/
theorem snd : Impl (R₁.prod R₂) R₂ (pureB Prod.snd) 0 Prod.snd :=
  free fun _ _ _ hs => hs.2

/-- Keep the object and add a computed value. -/
theorem extend {b : σ → Bld Op n σ₁} {c : ℕ} {F : τ → τ₁} (h : Impl R R₁ b c F) :
    Impl R (R.prod R₁) (pairB (pureB fun s => s) b) c (fun t => (t, F t)) :=
  (self.pair h).cost (Nat.zero_add c)

/-- Rearranging the operands before a builder. -/
theorem pre {b : σ₁ → Bld Op n σ₂} {c : ℕ} {F : τ₁ → τ₂} (h : Impl R₁ R₂ b c F)
    {g : σ → σ₁} {G : τ → τ₁}
    (hg : ∀ ⦃gs s T⦄, R.rep gs s T → R₁.rep gs (g s) (fun x => G (T x))) :
    Impl R R₂ (fun s => b (g s)) c (fun t => F (G t)) :=
  fun _ _ _ hs => h (hg hs)

/-- Rearranging the operands after a builder. -/
theorem post {b : σ₁ → Bld Op n σ₂} {c : ℕ} {F : τ₁ → τ₂} (h : Impl R₁ R₂ b c F)
    {g : σ₂ → σ₃} {G : τ₂ → τ₃}
    (hg : ∀ ⦃gs s T⦄, R₂.rep gs s T → R₃.rep gs (g s) (fun x => G (T x))) :
    Impl R₁ R₃ (fun s gs => ((b s gs).1, g (b s gs).2)) c (fun t => G (F t)) :=
  fun _ _ _ hs => ⟨(h hs).1, (h hs).2.1, hg (h hs).2.2⟩

/-- **One builder per index**: `r` times the cost. -/
theorem tab {r : ℕ} {b : Fin r → σ → Bld Op n σ₂} {c : ℕ} {F : Fin r → τ → τ₂}
    (h : ∀ i, Impl R R₂ (b i) c (F i)) :
    Impl R (Rep.pi (Fin r) R₂) (fun s => tabB fun i => b i s) (r * c) (fun t i => F i t) :=
  fun _ _ _ hs => tabB_spec fun i _ hgs => h i (R.mono hgs hs)

/-- **One builder per index**, costs depending on the index: the costs add. -/
theorem tabSum {r : ℕ} {b : Fin r → σ → Bld Op n σ₂} {c : Fin r → ℕ} {F : Fin r → τ → τ₂}
    (h : ∀ i, Impl R R₂ (b i) (c i) (F i)) :
    Impl R (Rep.pi (Fin r) R₂) (fun s => tabB fun i => b i s) (∑ i, c i) (fun t i => F i t) :=
  fun _ _ _ hs => tabB_sum_spec fun i _ hgs => h i (R.mono hgs hs)

/-- **A gadget at every index.** -/
theorem map {b : σ₁ → Bld Op n σ₂} {c : ℕ} {F : τ₁ → τ₂} (h : Impl R₁ R₂ b c F) (r : ℕ) :
    Impl (Rep.pi (Fin r) R₁) (Rep.pi (Fin r) R₂) (fun s => tabB fun i => b (s i)) (r * c)
      (fun t i => F (t i)) :=
  tab fun i => h.pre (R := Rep.pi (Fin r) R₁) (g := fun s => s i) (G := fun t => t i)
    fun _ _ _ hs => hs i

/-- **A two-argument gadget at every index.** -/
theorem map₂ {b : σ₁ × σ₂ → Bld Op n σ₃} {c : ℕ} {F : τ₁ × τ₂ → τ₃}
    (h : Impl (R₁.prod R₂) R₃ b c F) (r : ℕ) :
    Impl ((Rep.pi (Fin r) R₁).prod (Rep.pi (Fin r) R₂)) (Rep.pi (Fin r) R₃)
      (fun s => tabB fun i => b (s.1 i, s.2 i)) (r * c) (fun t i => F (t.1 i, t.2 i)) :=
  tab fun i => h.pre (R := (Rep.pi (Fin r) R₁).prod (Rep.pi (Fin r) R₂))
    (g := fun s => (s.1 i, s.2 i)) (G := fun t => (t.1 i, t.2 i)) fun _ _ _ hs => ⟨hs.1 i, hs.2 i⟩

/-- **Rounds of an algorithm** (`lem:augment`, Step 2, "`k` rounds"): `k` rounds cost `k` times
one round. -/
theorem iterate {b : σ → Bld Op n σ} {c : ℕ} {F : τ → τ} (h : Impl R R b c F) :
    ∀ k : ℕ, Impl R R (iterB b k) (k * c) F^[k]
  | 0 => (self (R := R)).cost (Nat.zero_mul c).symm
  | k + 1 => (h.comp (iterate h k)).cost (by ring)

/-- One round per element of a list (the rounds need only be implemented for the elements of
the list). -/
theorem fold {b : β → σ → Bld Op n σ} {c : ℕ} {F : β → τ → τ} :
    ∀ {l : List β}, (∀ a ∈ l, Impl R R (b a) c (F a)) →
      Impl R R (foldB b l) (l.length * c) (fun t => l.foldl (fun t a => F a t) t)
  | [], _ => (self (R := R)).cost (by simp)
  | a :: _, h => ((h a (List.mem_cons_self ..)).comp
      (fold fun e he => h e (List.mem_cons_of_mem a he))).cost
        (by simp only [List.length_cons]; ring)

/-- **All intermediate rounds**: entry `i` carries `F^[i]`. -/
theorem scan {b : σ → Bld Op n σ} {c : ℕ} {F : τ → τ} (h : Impl R R b c F) :
    ∀ k : ℕ, Impl R (Rep.pi (Fin (k + 1)) R) (scanB b k) (k * c) (fun t i => F^[i] t)
  | 0 => by
    intro gs s T hs
    refine ⟨List.prefix_refl _, by simp [scanB], fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    exact hs
  | k + 1 => by
    intro gs s T hs
    obtain ⟨hp₁, hl₁, hr₁⟩ := h hs
    obtain ⟨hp₂, hl₂, hr₂⟩ := scan h k hr₁
    refine ⟨hp₁.trans hp₂, hl₂.trans (by rw [hl₁]; ring), fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact R.mono (hp₁.trans hp₂) hs
    · exact hr₂ j

/-- **Rounds with a fixed context**: a round reads the context and replaces the state; `k`
rounds cost `k` times one round and apply `F a` `k` times, `a` the context. -/
theorem iterateCtx {b : σ₁ × σ₂ → Bld Op n σ₂} {c : ℕ} {F : τ₁ → τ₂ → τ₂}
    (h : Impl (R₁.prod R₂) R₂ b c (fun t => F t.1 t.2)) (k : ℕ) :
    Impl (R₁.prod R₂) R₂ (iterCtxB b k) (k * c) (fun t => (F t.1)^[k] t.2) :=
  ((((fst (R₂ := R₂)).pair h).cost (Nat.zero_add c)).iterate k |>.post (g := Prod.snd)
    (G := Prod.snd) fun _ _ _ hs => hs.2).congr fun t =>
    congrArg Prod.snd (iterate_ctx F t.1 t.2 k)

/-- **All intermediate rounds with a fixed context**: entry `i` carries `(F a)^[i]` of the
initial state, `a` the context. -/
theorem scanCtx {b : σ₁ × σ₂ → Bld Op n σ₂} {c : ℕ} {F : τ₁ → τ₂ → τ₂}
    (h : Impl (R₁.prod R₂) R₂ b c (fun t => F t.1 t.2)) (k : ℕ) :
    Impl (R₁.prod R₂) (Rep.pi (Fin (k + 1)) R₂) (scanCtxB b k) (k * c)
      (fun t i => (F t.1)^[i] t.2) :=
  ((((fst (R₂ := R₂)).pair h).cost (Nat.zero_add c)).scan k |>.post
    (R₃ := Rep.pi (Fin (k + 1)) R₂) (g := fun s i => (s i).2) (G := fun t i => (t i).2)
    fun _ _ _ hs i => (hs i).2).congr
    fun t => funext fun i => congrArg Prod.snd (iterate_ctx F t.1 t.2 i)

/-- **One round per element of a list, with a fixed context**: the round for `e` reads the
context `a` and applies `F e a` to the state (the rounds need only be implemented for the
elements of the list). -/
theorem foldCtx {b : β → σ₁ × σ₂ → Bld Op n σ₂} {c : ℕ} {F : β → τ₁ → τ₂ → τ₂} {l : List β}
    (h : ∀ e ∈ l, Impl (R₁.prod R₂) R₂ (b e) c (fun t => F e t.1 t.2)) :
    Impl (R₁.prod R₂) R₂ (foldCtxB b l) (l.length * c)
      (fun t => l.foldl (fun s e => F e t.1 s) t.2) :=
  ((fold fun e he => ((fst (R₂ := R₂)).pair (h e he)).cost (Nat.zero_add c)).post
    (g := Prod.snd) (G := Prod.snd) fun _ _ _ hs => hs.2).congr fun t =>
    congrArg Prod.snd (foldl_ctx F t.1 t.2 l)

end Impl

/-! ### Conversions between lists and families -/

/-- A family of operands carrying a family of values, read as lists. -/
theorem denL_ofFn {I : Interp Op α} {r : ℕ} {gs : List (Gate Op n)} {v : Fin r → Arg n}
    {V : (Fin n → α) → Fin r → α} (h : (Rep.pi (Fin r) (Rep.arg I)).rep gs v V) :
    DenL I gs (List.ofFn v) (fun x => List.ofFn (V x)) := by
  have := DenL.map (I := I) (gs := gs) (g := v) (G := fun i x => V x i) (List.finRange r)
    fun i _ => h i
  simpa only [List.ofFn_eq_map] using this

/-- A family of operands, read as a list: free. -/
theorem ofFn_impl (I : Interp Op α) (r : ℕ) :
    Impl (Rep.pi (Fin r) (Rep.arg I)) (Rep.list I r) (pureB (n := n) List.ofFn) 0 List.ofFn :=
  Impl.free fun _ _ _ hs => ⟨List.length_ofFn, denL_ofFn hs⟩

/-- A list of operands, read as a family (missing entries read the constant): free. -/
theorem getD_impl (I : Interp Op α) (L : ℕ) :
    Impl (Rep.list I L) (Rep.pi (Fin L) (Rep.arg I))
      (pureB (n := n) fun as i => as.getD i .const) 0 (fun A i => A.getD i I.zero) :=
  Impl.free fun _ _ _ hs i => hs.2.getD i

/-! ### Running a circuit inside a circuit -/

/-- Run the circuit `C` on the operands `v`: append its gates, input `i` of `C` reading `v i`,
and return its output operands. -/
def runB {k : ℕ} (C : Circuit Op k) (v : Fin k → Arg n) : Bld Op n (List (Arg n)) :=
  inline (fun o a b => emit o a b) v .const C

/-- **Running a circuit** (`lem:observer`, Steps 1 and 3, "evaluate the rank circuit on ...")
costs its size, and the outputs carry the outputs of `C` evaluated at the carried values. -/
theorem runB_impl (I : Interp Op α) {k : ℕ} (C : Circuit Op k) :
    Impl (Rep.pi (Fin k) (Rep.arg I)) (Rep.list I C.outs.length) (runB (n := n) C) C.size
      (C.eval I) := by
  intro gs v V hv
  obtain ⟨hp, h₂⟩ := inline_spec (R := fun gs a f => Den I gs a f) (J := fun _ => I)
    (φ := fun i x => V x i) (gad := fun o a b => emit o a b) (inp := v) (c := .const)
    (gs₀ := gs) (fun _ _ _ _ hp h => h.mono hp) (den_const gs) hv
    (fun o _ _ _ _ _ _ h₁ h₂ => ⟨isPrefix_emit _ _ _ _, den_emit o h₁ h₂⟩) C
  refine ⟨hp, ?_, by simp [runB, inline], (DenL.of_forall₂ h₂).congr fun x => ?_⟩
  · rw [runB, length_inline (fun _ => 1) (fun o a b gs => length_emit o a b gs)]
    simp [Circuit.size]
  · simp [Circuit.eval, List.map_map, Function.comp_def]

/-! ### Back to circuits -/

/-- The circuit that a builder makes from the input operands. -/
def circuitOf (b : (Fin n → Arg n) → Bld Op n (List (Arg n))) : Circuit Op n :=
  ⟨(b (fun i => .input i) []).1, (b (fun i => .input i) []).2⟩

/-- **An implementation from the inputs is a circuit**: of size `c`, with `L` outputs, computing
`F`. -/
theorem circuitOf_spec {I : Interp Op α} {b : (Fin n → Arg n) → Bld Op n (List (Arg n))}
    {L c : ℕ} {F : (Fin n → α) → List α}
    (h : Impl (Rep.pi (Fin n) (Rep.arg I)) (Rep.list I L) b c F) :
    (circuitOf b).size = c ∧ (circuitOf b).outs.length = L ∧
      ∀ x, (circuitOf b).eval I x = F x := by
  obtain ⟨-, hl, hL, hd⟩ := h (gs := []) (s := fun i => .input i) (T := fun x => x)
    fun i => den_input [] i
  exact ⟨by simpa [Circuit.size, circuitOf] using hl, hL, fun x => hd.eval x⟩

/-- `C₂` run on the outputs of `C₁`. -/
def seqCircuit {k : ℕ} (C₁ : Circuit Op n) (C₂ : Circuit Op k) : Circuit Op n :=
  circuitOf (seqB (runB C₁) fun as => runB C₂ fun i => as.getD i .const)

/-- **Sequential composition of circuits**: sizes add, and output `j` is `C₂` evaluated at the
outputs of `C₁` (a missing output reads the constant). -/
theorem seqCircuit_spec (I : Interp Op α) {k : ℕ} (C₁ : Circuit Op n) (C₂ : Circuit Op k) :
    (seqCircuit C₁ C₂).size = C₁.size + C₂.size ∧
      ∀ x, (seqCircuit C₁ C₂).eval I x = C₂.eval I fun i => (C₁.eval I x).getD i I.zero := by
  have h := (runB_impl (n := n) I C₁).comp ((runB_impl I C₂).pre (R := Rep.list I C₁.outs.length)
    (g := fun as (i : Fin k) => as.getD i .const) (G := fun A (i : Fin k) => A.getD i I.zero)
    fun _ _ _ hs i => hs.2.getD i)
  exact ⟨(circuitOf_spec h).1, (circuitOf_spec h).2.2⟩

end SignedTropical.BoolAlg
