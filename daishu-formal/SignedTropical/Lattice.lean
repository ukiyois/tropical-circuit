import SignedTropical.GapSum
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Monotone observables: the Sugeno form and `Lat = Mon`

`signed_assignment.tex`, Proposition `prop:sugeno`, Definition `def:lattice`, Theorem
`thm:lattice`.

A lattice circuit has `min` and `max` gates and no constants: no operand is the constant
source and no operand refers to a wire not yet built (`Circuit.IsLattice`).  Read over
`Bool`, where `min` is `∧` and `max` is `∨`, the same circuits are the monotone Boolean
circuits without constants.

* **Threshold identity** (`thr_eval`): for a lattice circuit and every threshold `t`,
  thresholding the outputs at `t` gives the outputs of the same circuit over `Bool` on the
  thresholded inputs.  This is the homomorphism lemma for `x ↦ [t ≤ x]`, which commutes
  with `min` and `max`.
* **Sugeno value** (`sugeno`): `Λ_g(D) = max_{A : g(A)} min_{e ∈ A} D_e`, with the
  convention that the maximum over an empty family is `0` (the convention of `ℝ`'s
  `iSup`).
* **Proposition `prop:sugeno`** (`gapSum_eq_sugeno`): for monotone `g` with `g(∅) = 0`
  and `F(S) = g(E \ S)`, `C_F(D) = Λ_g(D)` on `D ≥ 0`.
* **Theorem `thm:lattice`** (`thm_lattice`): for monotone `g` with `g(∅) = 0` and
  `g(E) = 1`, a lattice circuit computes `Λ_g` on `ℝ_{≥0}^E` exactly when, read over
  `Bool`, it computes `g`; hence `Lat(Λ_g) = Mon(g)` and `LatDepth(Λ_g) = MonDepth(g)`.
  The forward direction holds on all of `ℝ^E` (`eval_eq_sugeno`), which Corollary F uses.
-/

open Finset

namespace SignedTropical

variable {n m : ℕ}

/-! ### Lattice circuits -/

/-- An operand that is an input or an existing wire: neither the constant nor a reference
to a wire that does not exist yet. -/
def Arg.Proper (k : ℕ) : Arg n → Prop
  | .input _ => True
  | .const => False
  | .wire j => j < k

/-- Every gate reads only inputs and earlier wires. -/
def ProperGates (gs : List (Gate LatOp n)) : Prop :=
  ∀ k (h : k < gs.length), gs[k].a.Proper k ∧ gs[k].b.Proper k

/-- A *lattice circuit* (`def:lattice`): `min` and `max` gates, no constants, and no
reference to a wire not yet built. -/
def Circuit.IsLattice (C : Circuit LatOp n) : Prop :=
  ProperGates C.gates ∧ ∀ o ∈ C.outs, o.Proper C.gates.length

theorem properGates_concat {gs : List (Gate LatOp n)} {g : Gate LatOp n} :
    ProperGates (gs ++ [g]) ↔ ProperGates gs ∧ g.a.Proper gs.length ∧ g.b.Proper gs.length := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      simpa [List.getElem_append_left hk] using this
    · have := h gs.length (by simp)
      simpa using this
  · rintro ⟨h, ha, hb⟩ k hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · simpa [List.getElem_append_left hk] using h k hk
    · simpa using ⟨ha, hb⟩

/-- A proper operand does not read the constant. -/
theorem Arg.read_proper {α : Type} [LinearOrder α] {z z' : α} {x : Fin n → α} {ws : List α}
    {a : Arg n} (ha : a.Proper ws.length) :
    a.read (latInterp α z) x ws = a.read (latInterp α z') x ws := by
  cases a with
  | input i => rfl
  | const => exact absurd ha id
  | wire j =>
    simp only [Arg.read]
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha]

/-- The wires of a lattice circuit do not depend on the value given to the constant. -/
theorem wires_latInterp {α : Type} [LinearOrder α] (z z' : α) (x : Fin n → α) :
    ∀ {gs : List (Gate LatOp n)}, ProperGates gs →
      wires (latInterp α z) x gs = wires (latInterp α z') x gs := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro; rfl
  | append_singleton gs g ih =>
    intro h
    obtain ⟨hgs, ha, hb⟩ := properGates_concat.1 h
    rw [wires_concat, wires_concat, ih hgs]
    simp only [Gate.eval]
    rw [Arg.read_proper (z := z) (z' := z') (a := g.a) (by simpa using ha),
      Arg.read_proper (z := z) (z' := z') (a := g.b) (by simpa using hb)]
    rfl

theorem Circuit.eval_latInterp {α : Type} [LinearOrder α] {C : Circuit LatOp n}
    (hC : C.IsLattice) (z z' : α) (x : Fin n → α) :
    C.eval (latInterp α z) x = C.eval (latInterp α z') x := by
  simp only [Circuit.eval, wires_latInterp z z' x hC.1]
  exact List.map_congr_left fun o ho => Arg.read_proper (by simpa using hC.2 o ho)

/-! ### The threshold identity -/

/-- Thresholding at `t`. -/
def thr {α : Type} [LinearOrder α] (t x : α) : Bool := decide (t ≤ x)

theorem min_bool (a b : Bool) : min a b = (a && b) := by cases a <;> cases b <;> rfl
theorem max_bool (a b : Bool) : max a b = (a || b) := by cases a <;> cases b <;> rfl

theorem thr_monotone {α : Type} [LinearOrder α] (t : α) : Monotone (thr t) := by
  intro a b hab
  simp only [thr]
  by_cases h : t ≤ a
  · simp [h, h.trans hab]
  · simp [h]

/-- **Threshold identity.**  For a lattice circuit and every threshold `t`, thresholding
the outputs gives the same circuit read over `Bool` on the thresholded inputs. -/
theorem thr_eval {α : Type} [LinearOrder α] {C : Circuit LatOp n} (hC : C.IsLattice) (z t : α)
    (x : Fin n → α) :
    (C.eval (latInterp α z) x).map (thr t) = C.eval (latInterp Bool false) (thr t ∘ x) := by
  rw [C.eval_latInterp hC false (thr t z),
    Circuit.eval_map (thr t) (I := latInterp α z) (J := latInterp Bool (thr t z)) x rfl]
  intro o a b
  cases o
  · exact (thr_monotone t).map_min
  · exact (thr_monotone t).map_max

/-! ### The Sugeno value -/

/-- `Λ_g(D) = max_{A : g(A)} min_{e ∈ A} D_e` (`eq:sugeno`); the maximum over an empty
family is `0`. -/
noncomputable def sugeno (g : Finset (Fin m) → Bool) (D : Fin m → ℝ) : ℝ :=
  ⨆ A : {A : Finset (Fin m) // g A = true}, ⨅ e : A.1, D e

/-- `g` is monotone: supersets of a set with `g = 1` have `g = 1`. -/
def MonotoneObs (g : Finset (Fin m) → Bool) : Prop := ∀ S T, S ⊆ T → g S = true → g T = true

section Sugeno

variable {g : Finset (Fin m) → Bool}

/-- The minimum over a set with `g = 1` is attained. -/
theorem exists_eq_iInf (hg0 : g ∅ = false) (A : {A : Finset (Fin m) // g A = true})
    (D : Fin m → ℝ) : ∃ e ∈ A.1, D e = ⨅ e : A.1, D e := by
  have hne : A.1.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := A.2
    rw [h, hg0] at this
    exact Bool.false_ne_true this
  obtain ⟨e₀, he₀⟩ := hne
  have : Nonempty A.1 := ⟨⟨e₀, he₀⟩⟩
  obtain ⟨⟨e, he⟩, h⟩ := exists_eq_ciInf_of_finite (f := fun e : A.1 => D e)
  exact ⟨e, he, h⟩

/-- The maximum over a nonempty family is attained. -/
theorem exists_eq_sugeno (hg1 : g univ = true) (D : Fin m → ℝ) :
    ∃ A : {A : Finset (Fin m) // g A = true}, (⨅ e : A.1, D e) = sugeno g D := by
  have : Nonempty {A : Finset (Fin m) // g A = true} := ⟨⟨univ, hg1⟩⟩
  exact exists_eq_ciSup_of_finite

theorem le_iInf_iff (hg0 : g ∅ = false) (A : {A : Finset (Fin m) // g A = true})
    (D : Fin m → ℝ) (t : ℝ) : t ≤ ⨅ e : A.1, D e ↔ ∀ e ∈ A.1, t ≤ D e := by
  obtain ⟨e₀, he₀, h₀⟩ := exists_eq_iInf hg0 A D
  have : Nonempty A.1 := ⟨⟨e₀, he₀⟩⟩
  rw [le_ciInf_iff (Finite.bddBelow_range _)]
  exact ⟨fun h e he => h ⟨e, he⟩, fun h e => h e.1 e.2⟩

/-- **Threshold reading of the Sugeno value.**  For monotone `g` with `g(∅) = 0` and
`g(E) = 1`: `t ≤ Λ_g(D)` iff `g({e : t ≤ D_e}) = 1`. -/
theorem le_sugeno_iff (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true)
    (D : Fin m → ℝ) (t : ℝ) : t ≤ sugeno g D ↔ g (univ.filter fun e => t ≤ D e) = true := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := exists_eq_sugeno hg1 D
    rw [← hA, le_iInf_iff hg0] at h
    exact hg _ _ (fun e he => by simp [h e he]) A.2
  · intro h
    have hle := (le_iInf_iff hg0 ⟨_, h⟩ D t).2 (fun e he => by simpa using he)
    exact hle.trans (le_ciSup (f := fun A : {A : Finset (Fin m) // g A = true} =>
      ⨅ e : A.1, D e) (Finite.bddAbove_range _) ⟨_, h⟩)

/-- The strict form: `s < Λ_g(D)` iff `g({e : s < D_e}) = 1`. -/
theorem lt_sugeno_iff (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true)
    (D : Fin m → ℝ) (s : ℝ) : s < sugeno g D ↔ g (univ.filter fun e => s < D e) = true := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := exists_eq_sugeno hg1 D
    obtain ⟨e₀, he₀, h₀⟩ := exists_eq_iInf hg0 A D
    refine hg _ _ (fun e he => ?_) A.2
    have : (⨅ e : A.1, D e) ≤ D e :=
      ciInf_le (Finite.bddBelow_range _) (⟨e, he⟩ : A.1)
    simp only [mem_filter, mem_univ, true_and]
    linarith
  · intro h
    obtain ⟨e₀, he₀, h₀⟩ := exists_eq_iInf hg0 ⟨_, h⟩ D
    have hlt : s < D e₀ := by simpa using he₀
    rw [h₀] at hlt
    exact hlt.trans_le (le_ciSup (f := fun A : {A : Finset (Fin m) // g A = true} =>
      ⨅ e : A.1, D e) (Finite.bddAbove_range _) ⟨_, h⟩)

/-- The Sugeno value is `0` or an entry of `D`. -/
theorem sugeno_mem (hg0 : g ∅ = false) (D : Fin m → ℝ) :
    sugeno g D = 0 ∨ ∃ e, sugeno g D = D e := by
  by_cases hne : Nonempty {A : Finset (Fin m) // g A = true}
  · obtain ⟨A, hA⟩ := exists_eq_ciSup_of_finite (f := fun A : {A : Finset (Fin m) // g A = true}
      => ⨅ e : A.1, D e)
    obtain ⟨e, -, he⟩ := exists_eq_iInf hg0 A D
    exact Or.inr ⟨e, by rw [sugeno, ← hA, he]⟩
  · rw [not_nonempty_iff] at hne
    exact Or.inl (Real.iSup_of_isEmpty _)

/-- **Proposition `prop:sugeno` (Sugeno form).**  Let `g` be monotone with `g(∅) = 0` and
`F(S) = g(E \ S)`.  Then `C_F(D) = Λ_g(D)` for every `D ≥ 0`. -/
theorem gapSum_eq_sugeno (hg : MonotoneObs g) (hg0 : g ∅ = false) {D : Fin m → ℝ}
    (hD : ∀ e, 0 ≤ D e) :
    gapSum (fun S => if g (univ \ S) then 1 else 0) D = sugeno g D := by
  by_cases hg1 : g univ = true
  · have hterm : ∀ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k)
        * (if g (univ \ threshSet D k) then 1 else 0)
        = (sortedVal D (k + 1) - sortedVal D k)
          * (if sortedVal D k < sugeno g D then 1 else 0) := by
      intro k _
      rw [compl_threshSet]
      by_cases h : sortedVal D k < sugeno g D
      · rw [if_pos ((lt_sugeno_iff hg hg0 hg1 D _).1 h), if_pos h]
      · rw [if_neg (fun h' => h ((lt_sugeno_iff hg hg0 hg1 D _).2 h')), if_neg h]
    rw [gapSum, sum_congr rfl hterm]
    rcases sugeno_mem hg0 D with h | ⟨e, he⟩
    · rw [h, ← sortedVal_zero D]
      exact sum_gap_lt hD (Nat.zero_le m)
    · obtain ⟨j, -, hjm, hj⟩ := exists_sortedVal_eq D e
      rw [he, ← hj]
      exact sum_gap_lt hD hjm
  · have hgf : ∀ S, g S = false := fun S => by
      by_contra h
      exact hg1 (hg S univ (subset_univ S) (by simpa using h))
    have hempty : IsEmpty {A : Finset (Fin m) // g A = true} :=
      ⟨fun A => by have := A.2; rw [hgf] at this; exact Bool.false_ne_true this⟩
    simp [gapSum, hgf, sugeno, Real.iSup_of_isEmpty]

end Sugeno

/-! ### Theorem `thm:lattice` -/

/-- A lattice circuit computes `Λ_g` on `ℝ_{≥0}^E`. -/
def LatComputes (C : Circuit LatOp m) (h : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ D : Fin m → ℝ, (∀ e, 0 ≤ D e) → C.eval (latInterp ℝ 0) D = [h D]

/-- A lattice circuit, read over `Bool`, computes `g` from the indicator vector. -/
def MonComputes (C : Circuit LatOp m) (g : Finset (Fin m) → Bool) : Prop :=
  ∀ S, C.eval (latInterp Bool false) (indicator S) = [g S]

/-- The depth of a circuit: the length of a longest path from a source to an output,
computed by reading every gate as `1 + max`. -/
def Circuit.depth {Op : Type} (C : Circuit Op n) : ℕ :=
  (C.eval ⟨0, fun _ a b => max a b + 1⟩ (fun _ => 0)).foldr max 0

/-- `Lat(h)`: the least size of a lattice circuit computing `h` on `ℝ_{≥0}^E`. -/
noncomputable def latSize (h : (Fin m → ℝ) → ℝ) : ℕ :=
  sInf {s | ∃ C : Circuit LatOp m, C.IsLattice ∧ LatComputes C h ∧ C.size = s}

/-- `LatDepth(h)`. -/
noncomputable def latDepth (h : (Fin m → ℝ) → ℝ) : ℕ :=
  sInf {d | ∃ C : Circuit LatOp m, C.IsLattice ∧ LatComputes C h ∧ C.depth = d}

/-- `Mon(g)`: the least size of a Boolean circuit over `∧, ∨` without constants
computing `g`. -/
noncomputable def monSize (g : Finset (Fin m) → Bool) : ℕ :=
  sInf {s | ∃ C : Circuit LatOp m, C.IsLattice ∧ MonComputes C g ∧ C.size = s}

/-- `MonDepth(g)`. -/
noncomputable def monDepth (g : Finset (Fin m) → Bool) : ℕ :=
  sInf {d | ∃ C : Circuit LatOp m, C.IsLattice ∧ MonComputes C g ∧ C.depth = d}

section Lattice

variable {g : Finset (Fin m) → Bool}

theorem thr_comp_eq_indicator (D : Fin m → ℝ) (t : ℝ) :
    thr t ∘ D = indicator (univ.filter fun e => t ≤ D e) := by
  funext e
  simp [thr, indicator]

/-- **Forward direction of `thm:lattice`, on all of `ℝ^E`.**  If a lattice circuit
computes `g` over `Bool`, then over `ℝ` it computes `Λ_g` at every `D`. -/
theorem eval_eq_sugeno (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true)
    {C : Circuit LatOp m} (hC : C.IsLattice) (hmon : MonComputes C g) (z : ℝ)
    (D : Fin m → ℝ) : C.eval (latInterp ℝ z) D = [sugeno g D] := by
  have hlen : (C.eval (latInterp ℝ z) D).length = 1 := by
    have := congrArg List.length (hmon ∅); simpa [Circuit.eval] using this
  obtain ⟨v, hv⟩ : ∃ v, C.eval (latInterp ℝ z) D = [v] := List.length_eq_one_iff.1 hlen
  have key : ∀ t, t ≤ v ↔ t ≤ sugeno g D := by
    intro t
    have h := thr_eval hC z t D
    rw [hv, thr_comp_eq_indicator, hmon] at h
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [le_sugeno_iff hg hg0 hg1, ← h]
    simp [thr]
  rw [hv, le_antisymm ((key v).1 le_rfl) ((key _).2 le_rfl)]

/-- The Sugeno value at an indicator vector is the observable. -/
theorem sugeno_indicator (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true)
    (S : Finset (Fin m)) : sugeno g (fun e => if e ∈ S then 1 else 0)
      = if g S then 1 else 0 := by
  have hS : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (univ.filter fun e => t ≤ (if e ∈ S then (1 : ℝ) else 0)) = S := by
    intro t ht0 ht1
    ext e
    by_cases he : e ∈ S <;> simp [he, ht1, not_le.2 ht0]
  by_cases hgS : g S = true
  · rw [if_pos hgS]
    refine le_antisymm (not_lt.1 fun h => ?_) ?_
    · have := (lt_sugeno_iff hg hg0 hg1 _ 1).1 h
      rw [show (univ.filter fun e => (1 : ℝ) < if e ∈ S then 1 else 0) = ∅ by
        ext e; by_cases he : e ∈ S <;> simp [he]] at this
      rw [hg0] at this; exact absurd this (by simp)
    · rw [le_sugeno_iff hg hg0 hg1, hS 1 one_pos le_rfl]; exact hgS
  · rw [if_neg hgS]
    refine le_antisymm (not_lt.1 fun h => ?_) ?_
    · have ht := (le_sugeno_iff hg hg0 hg1 _ _).1 (min_le_left
        (sugeno g fun e => if e ∈ S then (1 : ℝ) else 0) 1)
      rw [hS _ (lt_min h one_pos) (min_le_right _ _)] at ht
      exact hgS ht
    · rw [le_sugeno_iff hg hg0 hg1]
      convert hg1
      ext e; by_cases he : e ∈ S <;> simp [he]

/-- The embedding `Bool → ℝ`, `false ↦ 0`, `true ↦ 1`. -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

theorem boolReal_monotone : Monotone boolReal := by
  intro a b hab
  cases a <;> cases b <;> simp [boolReal]
  exact absurd hab (by decide)

theorem boolReal_injective : Function.Injective boolReal := by
  intro a b h; cases a <;> cases b <;> simp_all [boolReal]

/-- **Theorem `thm:lattice`, circuit by circuit.**  For monotone `g` with `g(∅) = 0` and
`g(E) = 1`, a lattice circuit computes `Λ_g` on `ℝ_{≥0}^E` iff, read over `Bool`, it
computes `g`. -/
theorem latComputes_iff (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true)
    {C : Circuit LatOp m} (hC : C.IsLattice) : LatComputes C (sugeno g) ↔ MonComputes C g := by
  constructor
  · intro hlat S
    have h := C.eval_map boolReal (I := latInterp Bool false) (J := latInterp ℝ 0)
      (indicator S) rfl (fun o a b => by
        cases o
        · exact boolReal_monotone.map_min
        · exact boolReal_monotone.map_max)
    have hx : boolReal ∘ indicator S = fun e => if e ∈ S then 1 else 0 := by
      funext e; by_cases he : e ∈ S <;> simp [boolReal, indicator, he]
    rw [hx, hlat _ (fun e => by by_cases he : e ∈ S <;> simp [he]), sugeno_indicator hg hg0 hg1]
      at h
    have hl : (C.eval (latInterp Bool false) (indicator S)).length = 1 := by
      have := congrArg List.length h; simpa using this.symm
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hl
    rw [hb] at h ⊢
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    congr 1
    exact boolReal_injective (by rw [← h]; rfl)
  · intro hmon D _
    exact eval_eq_sugeno hg hg0 hg1 hC hmon 0 D

/-- **Theorem `thm:lattice` (exact equivalence in the monotone case).**  For monotone `g`
with `g(∅) = 0` and `g(E) = 1`: `Lat(Λ_g) = Mon(g)` and `LatDepth(Λ_g) = MonDepth(g)`. -/
theorem thm_lattice (hg : MonotoneObs g) (hg0 : g ∅ = false) (hg1 : g univ = true) :
    latSize (sugeno g) = monSize g ∧ latDepth (sugeno g) = monDepth g := by
  have key : ∀ C : Circuit LatOp m, C.IsLattice ∧ LatComputes C (sugeno g)
      ↔ C.IsLattice ∧ MonComputes C g := fun C =>
    ⟨fun h => ⟨h.1, (latComputes_iff hg hg0 hg1 h.1).1 h.2⟩,
      fun h => ⟨h.1, (latComputes_iff hg hg0 hg1 h.1).2 h.2⟩⟩
  constructor
  · simp only [latSize, monSize, ← and_assoc, key]
  · simp only [latDepth, monDepth, ← and_assoc, key]

end Lattice

end SignedTropical
