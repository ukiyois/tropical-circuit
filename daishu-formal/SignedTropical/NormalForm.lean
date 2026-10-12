import SignedTropical.TheoremA

/-!
# The `±` normal form

`signed_assignment.tex`, Proposition `prop:normal-form`.  Let `σ` be `max` or `min`.  A
circuit of size `s` over `σ`, `+`, `-` and the constant `0` is rewritten as `A - B`, where `A`
and `B` are circuits over `σ`, `+` and the constant `0` with `|A| + |B| ≤ 8 s`.

Gate sets.  `SignedOp` has the gates `σ`, `+`, `-` and `PlusOp` the gates `σ`, `+`; in both
the gate `sel` is read as `σ` (`Sel`), in a linearly ordered additive commutative group `R`
with constant source `0` (`signedInterp σ R`, `plusInterp σ R`).  Phase 1's signed tropical
gates `STOp` are `SignedOp` at `σ = max` up to renaming the operations (`relabel`, `ofSTOp`,
`toSTOp`, `eval_relabel`), and a circuit over `σ`, `+` is a circuit over Phase 1's
`(min, +, max)` gates `TropOp` (`toTropOp`).

The construction carries every wire `g` as a pair `(g⁺, g⁻)` with `g = g⁺ - g⁻`: an input
`x_i` as `(x_i, 0)`, the constant as `(0, 0)`, and
`a + b ↦ (a⁺ + b⁺, a⁻ + b⁻)`, `a - b ↦ (a⁺ + b⁻, a⁻ + b⁺)`,
`σ(a, b) ↦ (σ(a⁺ + b⁻, b⁺ + a⁻), a⁻ + b⁻)`, the last because `σ` commutes with subtracting
`a⁻ + b⁻` from both arguments (`Sel.op_sub_sub`).  This is inlining (`inline_spec`) with a
gadget of two or four gates per gate (`pairGad`).  The halves of every pair are operands of
one gate list, read by all later gadgets, so `A` and `B` are one gate list of at most `4 s`
gates with two lists of outputs (`posCircuit`, `negCircuit`, `normal_form_shared`), and as
two circuits `|A| + |B| ≤ 8 s` (`normal_form`).  The construction depends neither on `σ` nor
on `R`.

The bases are interchangeable: replacing every `σ` gate by `a + b - σ̄(a, b)`, three gates,
where `σ̄` is the other choice, gives a circuit over `σ̄`, `+`, `-` of size at most `3 s` with
the same outputs (`swapCircuit`, `interchange`).

For Phase 1's circuits: `normal_form_stOp` (`σ = max`); `stOp_to_min` and `min_to_stOp`
(interchange); `normal_form_stOp_min`, the route of `eq:normal-form` (to the `min` basis,
then normalized, `|A| + |B| ≤ 24 s`); and `theoremA_normal_form`, `h_M = A - B` with `A`
and `B` over `max`, `+`.
-/

namespace SignedTropical.NormalForm

variable {n : ℕ}

/-! ### Gate sets -/

/-- The choice `σ ∈ {max, min}`. -/
inductive Sel
  | max
  | min
  deriving DecidableEq, Repr

namespace Sel

/-- `σ` read in a linear order. -/
def op {R : Type} [LinearOrder R] : Sel → R → R → R
  | .max => Max.max
  | .min => Min.min

/-- The other choice, `σ̄`. -/
def swap : Sel → Sel
  | .max => .min
  | .min => .max

end Sel

/-- Gates over `σ`, `+` and `-`; the gate `sel` is read as `σ`. -/
inductive SignedOp
  | sel
  | add
  | sub
  deriving DecidableEq, Repr

/-- Gates over `σ` and `+`; the gate `sel` is read as `σ`. -/
inductive PlusOp
  | sel
  | add
  deriving DecidableEq, Repr

/-- Gates over `σ`, `+`, `-` read in `R`, with constant source `0`. -/
def signedInterp (σ : Sel) (R : Type) [AddCommGroup R] [LinearOrder R] :
    Interp SignedOp R where
  zero := 0
  op
    | .sel, a, b => σ.op a b
    | .add, a, b => a + b
    | .sub, a, b => a - b

/-- Gates over `σ` and `+` read in `R`, with constant source `0`. -/
def plusInterp (σ : Sel) (R : Type) [AddCommGroup R] [LinearOrder R] : Interp PlusOp R where
  zero := 0
  op
    | .sel, a, b => σ.op a b
    | .add, a, b => a + b

/-! ### Renaming operations, counting gates -/

section Relabel

variable {Op Op' α : Type}

/-- Rename the operations of a circuit; operands and outputs are unchanged. -/
def relabel (f : Op → Op') (C : Circuit Op n) : Circuit Op' n :=
  ⟨C.gates.map fun g => ⟨f g.op, g.a, g.b⟩, C.outs⟩

@[simp] theorem size_relabel (f : Op → Op') (C : Circuit Op n) :
    (relabel f C).size = C.size := by
  simp [relabel, Circuit.size]

@[simp] theorem outs_relabel (f : Op → Op') (C : Circuit Op n) : (relabel f C).outs = C.outs :=
  rfl

/-- A renamed circuit read with `J` has the outputs of the original read with `I`, when `J`
reads `f o` as `I` reads `o`. -/
theorem eval_relabel (f : Op → Op') {I : Interp Op α} {J : Interp Op' α}
    (hz : J.zero = I.zero) (hop : ∀ o, J.op (f o) = I.op o) (C : Circuit Op n)
    (x : Fin n → α) : (relabel f C).eval J x = C.eval I x := by
  have hread : ∀ ws : List α, Arg.read (n := n) J x ws = Arg.read I x ws := fun ws =>
    funext fun a => by cases a <;> simp [Arg.read, hz]
  have hw : ∀ gs : List (Gate Op n),
      wires J x (gs.map fun g => ⟨f g.op, g.a, g.b⟩) = wires I x gs := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [List.map_append, List.map_singleton, wires_concat, wires_concat, ih]
      simp [Gate.eval, hread, hop]
  simp only [Circuit.eval, relabel, hw, hread]

/-- A gate list whose gates cost at most `c` each costs at most `c` times its length. -/
theorem sum_cost_le {cost : Op → ℕ} {c : ℕ} (h : ∀ o, cost o ≤ c) (gs : List (Gate Op n)) :
    (gs.map fun g => cost g.op).sum ≤ c * gs.length := by
  rw [mul_comm]
  simpa using List.sum_le_card_nsmul (gs.map fun g => cost g.op) c (by simp [h])

end Relabel

/-- Phase 1's signed tropical gates as gates over `σ`, `+`, `-`. -/
def ofSTOp : STOp → SignedOp
  | .max => .sel
  | .add => .add
  | .sub => .sub

/-- Gates over `σ`, `+`, `-` as Phase 1's signed tropical gates. -/
def toSTOp : SignedOp → STOp
  | .sel => .max
  | .add => .add
  | .sub => .sub

section Bridge

variable {R : Type} [AddCommGroup R] [LinearOrder R]

theorem eval_relabel_ofSTOp (C : Circuit STOp n) (x : Fin n → R) :
    (relabel ofSTOp C).eval (signedInterp .max R) x = C.eval (stInterp R) x :=
  eval_relabel ofSTOp rfl (fun o => by cases o <;> rfl) C x

theorem eval_relabel_toSTOp (C : Circuit SignedOp n) (x : Fin n → R) :
    (relabel toSTOp C).eval (stInterp R) x = C.eval (signedInterp .max R) x :=
  eval_relabel toSTOp rfl (fun o => by cases o <;> rfl) C x

end Bridge

/-- Gates over `σ`, `+` as Phase 1's `(min, +, max)` gates. -/
def toTropOp : Sel → PlusOp → TropOp
  | .max, .sel => .max
  | .min, .sel => .min
  | _, .add => .add

/-- Over `ℝ`, a circuit over `σ`, `+`, renamed into Phase 1's `(min, +, max)` gates, has the
same outputs; it has the same size (`size_relabel`) and its gates are `σ` and `+`. -/
theorem eval_relabel_toTropOp (σ : Sel) (A : Circuit PlusOp n) (x : Fin n → ℝ) :
    (relabel (toTropOp σ) A).eval tropInterp x = A.eval (plusInterp σ ℝ) x :=
  eval_relabel (toTropOp σ) (I := plusInterp σ ℝ) rfl (fun o => by cases σ <;> cases o <;> rfl)
    A x

/-! ### The pairs `(g⁺, g⁻)` -/

/-- Two additions, `(a + b, c + d)`. -/
def add2 (a b c d : Arg n) : Bld PlusOp n (Arg n × Arg n) := fun gs =>
  let p := emit .add a b gs
  let q := emit .add c d p.1
  (q.1, (p.2, q.2))

/-- The gadget of one gate on the pairs `a = (a⁺, a⁻)` and `b = (b⁺, b⁻)`:
`a + b ↦ (a⁺ + b⁺, a⁻ + b⁻)`, `a - b ↦ (a⁺ + b⁻, a⁻ + b⁺)` and
`σ(a, b) ↦ (σ(a⁺ + b⁻, b⁺ + a⁻), a⁻ + b⁻)`. -/
def pairGad : SignedOp → Arg n × Arg n → Arg n × Arg n → Bld PlusOp n (Arg n × Arg n)
  | .add, a, b => add2 a.1 b.1 a.2 b.2
  | .sub, a, b => add2 a.1 b.2 a.2 b.1
  | .sel, a, b => fun gs =>
    let p := add2 a.1 b.2 b.1 a.2 gs
    let q := emit .sel p.2.1 p.2.2 p.1
    let r := emit .add a.2 b.2 q.1
    (r.1, (q.2, r.2))

/-- Gates per gadget. -/
def pairCost : SignedOp → ℕ
  | .sel => 4
  | .add => 2
  | .sub => 2

theorem length_pairGad (o : SignedOp) (a b : Arg n × Arg n) (gs : List (Gate PlusOp n)) :
    (pairGad o a b gs).1.length = gs.length + pairCost o := by
  cases o <;> simp [pairGad, pairCost, add2, length_emit]

/-- The gadgets of all gates of `C`, inlined into one gate list, and the output pairs. -/
def pairs (C : Circuit SignedOp n) : List (Gate PlusOp n) × List (Arg n × Arg n) :=
  inline pairGad (fun i => (.input i, .const)) (.const, .const) C []

/-- `A`: the shared gate list, with the first halves of the output pairs as outputs. -/
def posCircuit (C : Circuit SignedOp n) : Circuit PlusOp n :=
  ⟨(pairs C).1, (pairs C).2.map Prod.fst⟩

/-- `B`: the shared gate list, with the second halves of the output pairs as outputs. -/
def negCircuit (C : Circuit SignedOp n) : Circuit PlusOp n :=
  ⟨(pairs C).1, (pairs C).2.map Prod.snd⟩

theorem gates_negCircuit (C : Circuit SignedOp n) :
    (negCircuit C).gates = (posCircuit C).gates := rfl

theorem length_outs_posCircuit (C : Circuit SignedOp n) :
    (posCircuit C).outs.length = C.outs.length := by
  simp [posCircuit, pairs, inline]

theorem length_outs_negCircuit (C : Circuit SignedOp n) :
    (negCircuit C).outs.length = C.outs.length := by
  simp [negCircuit, pairs, inline]

/-- The shared gate list has `4` gates per `σ` gate and `2` per `+` or `-` gate. -/
theorem size_posCircuit (C : Circuit SignedOp n) :
    (posCircuit C).size = (C.gates.map fun g => pairCost g.op).sum := by
  simp [posCircuit, pairs, Circuit.size, length_inline pairCost length_pairGad]

theorem size_posCircuit_le (C : Circuit SignedOp n) : (posCircuit C).size ≤ 4 * C.size :=
  (size_posCircuit C).trans_le (sum_cost_le (fun o => by cases o <;> decide) C.gates)

section PairSpec

variable {R : Type} [AddCommGroup R] [LinearOrder R]

/-- The pair `p = (p⁺, p⁻)` carries `f` in the gate list `gs`: read with `σ`, `p⁺` and `p⁻`
carry `f⁺` and `f⁻` with `f = f⁺ - f⁻`. -/
def PairDen (σ : Sel) (gs : List (Gate PlusOp n)) (p : Arg n × Arg n)
    (f : (Fin n → R) → R) : Prop :=
  ∃ f₁ f₂, Den (plusInterp σ R) gs p.1 f₁ ∧ Den (plusInterp σ R) gs p.2 f₂ ∧
    ∀ x, f x = f₁ x - f₂ x

theorem PairDen.mono {σ : Sel} {gs gs' : List (Gate PlusOp n)} {p : Arg n × Arg n}
    {f : (Fin n → R) → R} (h : PairDen σ gs p f) (hp : gs <+: gs') : PairDen σ gs' p f :=
  let ⟨f₁, f₂, h₁, h₂, hf⟩ := h
  ⟨f₁, f₂, h₁.mono hp, h₂.mono hp, hf⟩

theorem add2_spec {σ : Sel} {gs : List (Gate PlusOp n)} {a b c d : Arg n}
    {fa fb fc fd : (Fin n → R) → R} (ha : Den (plusInterp σ R) gs a fa)
    (hb : Den (plusInterp σ R) gs b fb) (hc : Den (plusInterp σ R) gs c fc)
    (hd : Den (plusInterp σ R) gs d fd) :
    gs <+: (add2 a b c d gs).1 ∧
      Den (plusInterp σ R) (add2 a b c d gs).1 (add2 a b c d gs).2.1 (fun x => fa x + fb x) ∧
      Den (plusInterp σ R) (add2 a b c d gs).1 (add2 a b c d gs).2.2 (fun x => fc x + fd x) :=
  have p₁ := isPrefix_emit PlusOp.add a b gs
  have p₂ := isPrefix_emit PlusOp.add c d (emit PlusOp.add a b gs).1
  ⟨p₁.trans p₂, (den_emit PlusOp.add ha hb).mono p₂,
    den_emit PlusOp.add (hc.mono p₁) (hd.mono p₁)⟩

/-- Output pairs carrying the values `fs` give `A` and `B` with `fs = A - B`. -/
theorem eval_of_forall₂ {σ : Sel} {gs : List (Gate PlusOp n)} :
    ∀ {ps : List (Arg n × Arg n)} {fs : List ((Fin n → R) → R)},
      List.Forall₂ (PairDen σ gs) ps fs → ∀ x,
        fs.map (· x) = List.zipWith (· - ·)
          ((Circuit.mk gs (ps.map Prod.fst)).eval (plusInterp σ R) x)
          ((Circuit.mk gs (ps.map Prod.snd)).eval (plusInterp σ R) x)
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons ⟨_, _, h₁, h₂, hf⟩ h, x => by
    have ih := eval_of_forall₂ h x
    simp only [Circuit.eval] at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, h₁.2 x, h₂.2 x, hf x, ih]

variable [IsOrderedAddMonoid R]

/-- `σ` commutes with subtracting a constant from both arguments. -/
theorem Sel.op_sub_sub (σ : Sel) (a b c : R) : σ.op (a - c) (b - c) = σ.op a b - c := by
  cases σ
  exacts [max_sub_sub_right a b c, min_sub_sub_right a b c]

theorem pairGad_spec {σ : Sel} {gs : List (Gate PlusOp n)} {a b : Arg n × Arg n}
    {f g : (Fin n → R) → R} (ha : PairDen σ gs a f) (hb : PairDen σ gs b g) (o : SignedOp) :
    gs <+: (pairGad o a b gs).1 ∧ PairDen σ (pairGad o a b gs).1 (pairGad o a b gs).2
      (fun x => (signedInterp σ R).op o (f x) (g x)) := by
  obtain ⟨f₁, f₂, ha₁, ha₂, hf⟩ := ha
  obtain ⟨g₁, g₂, hb₁, hb₂, hg⟩ := hb
  cases o with
  | add =>
    obtain ⟨hp, h₁, h₂⟩ := add2_spec ha₁ hb₁ ha₂ hb₂
    refine ⟨hp, _, _, h₁, h₂, fun x => ?_⟩
    simp only [signedInterp, hf, hg]
    abel
  | sub =>
    obtain ⟨hp, h₁, h₂⟩ := add2_spec ha₁ hb₂ ha₂ hb₁
    refine ⟨hp, _, _, h₁, h₂, fun x => ?_⟩
    simp only [signedInterp, hf, hg]
    abel
  | sel =>
    obtain ⟨hp, h₁, h₂⟩ := add2_spec ha₁ hb₂ hb₁ ha₂
    set p := add2 a.1 b.2 b.1 a.2 gs
    have hq := isPrefix_emit PlusOp.sel p.2.1 p.2.2 p.1
    have hr := isPrefix_emit PlusOp.add a.2 b.2 (emit PlusOp.sel p.2.1 p.2.2 p.1).1
    refine ⟨(hp.trans hq).trans hr, _, _, (den_emit PlusOp.sel h₁ h₂).mono hr,
      den_emit PlusOp.add (ha₂.mono (hp.trans hq)) (hb₂.mono (hp.trans hq)), fun x => ?_⟩
    simp only [signedInterp, plusInterp, hf, hg]
    rw [← σ.op_sub_sub]
    congr 1 <;> abel

/-- Every output pair carries the corresponding output of `C`. -/
theorem pairs_spec (σ : Sel) (C : Circuit SignedOp n) :
    List.Forall₂ (PairDen σ (pairs C).1) (pairs C).2
      (C.outs.map fun o x => o.read (signedInterp σ R) x (wires (signedInterp σ R) x C.gates)) :=
  (inline_spec (R := PairDen σ) (J := fun _ => signedInterp σ R) (φ := fun i x => x i)
    (gad := pairGad) (inp := fun i => (.input i, .const)) (c := (.const, .const))
    (fun _ _ _ _ hp h => h.mono hp)
    ⟨_, _, den_const [], den_const [], fun _ => (sub_zero _).symm⟩
    (fun i => ⟨_, _, den_input [] i, den_const [], fun _ => (sub_zero _).symm⟩)
    (fun o _ _ _ _ _ _ h₁ h₂ => pairGad_spec h₁ h₂ o) C).2

/-- **The `±` decomposition.**  In a linearly ordered additive commutative group `R`, at
every input `x ∈ R^n`, the outputs of `C` read with `σ` are the differences of the outputs of
`posCircuit C` and `negCircuit C` read with `σ`. -/
theorem eval_eq_sub (σ : Sel) (C : Circuit SignedOp n) (x : Fin n → R) :
    C.eval (signedInterp σ R) x = List.zipWith (· - ·)
      ((posCircuit C).eval (plusInterp σ R) x) ((negCircuit C).eval (plusInterp σ R) x) := by
  have h := eval_of_forall₂ (pairs_spec σ C) x
  rw [List.map_map] at h
  exact h

/-- **Proposition `prop:normal-form`, shared form.**  Let `σ` be `max` or `min` and `R` a
linearly ordered additive commutative group.  For every circuit `C` over `σ`, `+`, `-` and
the constant `0` with `N` outputs there are circuits `A` and `B` over `σ`, `+` and the
constant `0` with the same gates, at most `4 |C|` of them, and `N` outputs each, such that
`C(x) = A(x) - B(x)` componentwise at every input `x ∈ R^n`.  Taking all wires of `C` as its
outputs, one circuit of size at most `4 |C|` computes the pair `(g⁺, g⁻)` of every gate
`g`. -/
theorem normal_form_shared (σ : Sel) (C : Circuit SignedOp n) :
    ∃ A B : Circuit PlusOp n, A.gates = B.gates ∧ A.size ≤ 4 * C.size ∧
      A.outs.length = C.outs.length ∧ B.outs.length = C.outs.length ∧
      ∀ x : Fin n → R, C.eval (signedInterp σ R) x =
        List.zipWith (· - ·) (A.eval (plusInterp σ R) x) (B.eval (plusInterp σ R) x) :=
  ⟨posCircuit C, negCircuit C, rfl, size_posCircuit_le C, length_outs_posCircuit C,
    length_outs_negCircuit C, eval_eq_sub σ C⟩

/-- **Proposition `prop:normal-form`.**  Let `σ` be `max` or `min` and `R` a linearly
ordered additive commutative group.  Every circuit `C` over `σ`, `+`, `-` and the constant
`0` with `N` outputs is `A - B`, componentwise at every input `x ∈ R^n`, where `A` and `B`
are circuits over `σ`, `+` and the constant `0` with `N` outputs each and
`|A| + |B| ≤ 8 |C|`. -/
theorem normal_form (σ : Sel) (C : Circuit SignedOp n) :
    ∃ A B : Circuit PlusOp n, A.size + B.size ≤ 8 * C.size ∧
      A.outs.length = C.outs.length ∧ B.outs.length = C.outs.length ∧
      ∀ x : Fin n → R, C.eval (signedInterp σ R) x =
        List.zipWith (· - ·) (A.eval (plusInterp σ R) x) (B.eval (plusInterp σ R) x) := by
  obtain ⟨A, B, hg, hs, h⟩ := normal_form_shared (R := R) σ C
  refine ⟨A, B, ?_, h⟩
  have : B.size = A.size := by simp [Circuit.size, hg]
  omega

/-- **Proposition `prop:normal-form` for Phase 1's signed tropical circuits** (`σ = max`).
Let `R` be a linearly ordered additive commutative group.  Every circuit `C` over `max`,
`+`, `-` and the constant `0` with `N` outputs is `A - B`, componentwise at every input
`x ∈ R^n`, where `A` and `B` are circuits over `max`, `+` and the constant `0` with `N`
outputs each and `|A| + |B| ≤ 8 |C|`. -/
theorem normal_form_stOp (C : Circuit STOp n) :
    ∃ A B : Circuit PlusOp n, A.size + B.size ≤ 8 * C.size ∧
      A.outs.length = C.outs.length ∧ B.outs.length = C.outs.length ∧
      ∀ x : Fin n → R, C.eval (stInterp R) x =
        List.zipWith (· - ·) (A.eval (plusInterp .max R) x) (B.eval (plusInterp .max R) x) := by
  obtain ⟨A, B, h⟩ := normal_form (R := R) .max (relabel ofSTOp C)
  refine ⟨A, B, ?_⟩
  simpa only [size_relabel, outs_relabel, eval_relabel_ofSTOp] using h

end PairSpec

/-! ### Interchanging `max` and `min` -/

/-- The gadget of one gate: `σ(a, b) ↦ a + b - σ̄(a, b)`, three gates; `+` and `-` are
kept. -/
def swapGad : SignedOp → Arg n → Arg n → Bld SignedOp n (Arg n)
  | .sel, a, b => fun gs =>
    let p := emit .add a b gs
    let q := emit .sel a b p.1
    emit .sub p.2 q.2 q.1
  | .add, a, b => emit .add a b
  | .sub, a, b => emit .sub a b

/-- Gates per gadget. -/
def swapCost : SignedOp → ℕ
  | .sel => 3
  | .add => 1
  | .sub => 1

theorem length_swapGad (o : SignedOp) (a b : Arg n) (gs : List (Gate SignedOp n)) :
    (swapGad o a b gs).1.length = gs.length + swapCost o := by
  cases o <;> simp [swapGad, swapCost, length_emit]

/-- `C` with every `σ` gate replaced by `a + b - σ̄(a, b)`. -/
def swapCircuit (C : Circuit SignedOp n) : Circuit SignedOp n :=
  let p := inline swapGad (fun i => .input i) .const C []
  ⟨p.1, p.2⟩

/-- `swapCircuit C` has `3` gates per `σ` gate and `1` per `+` or `-` gate. -/
theorem size_swapCircuit (C : Circuit SignedOp n) :
    (swapCircuit C).size = (C.gates.map fun g => swapCost g.op).sum := by
  simp [swapCircuit, Circuit.size, length_inline swapCost length_swapGad]

theorem size_swapCircuit_le (C : Circuit SignedOp n) : (swapCircuit C).size ≤ 3 * C.size :=
  (size_swapCircuit C).trans_le (sum_cost_le (fun o => by cases o <;> decide) C.gates)

section SwapSpec

variable {R : Type} [AddCommGroup R] [LinearOrder R]

/-- `σ(a, b) = a + b - σ̄(a, b)`. -/
theorem Sel.add_sub_swap (σ : Sel) (a b : R) : a + b - σ.swap.op a b = σ.op a b := by
  cases σ
  exacts [sub_eq_iff_eq_add'.2 (min_add_max a b).symm,
    sub_eq_iff_eq_add.2 (min_add_max a b).symm]

theorem swapGad_spec {σ : Sel} {gs : List (Gate SignedOp n)} {a b : Arg n}
    {f g : (Fin n → R) → R} (ha : Den (signedInterp σ.swap R) gs a f)
    (hb : Den (signedInterp σ.swap R) gs b g) (o : SignedOp) :
    gs <+: (swapGad o a b gs).1 ∧ Den (signedInterp σ.swap R) (swapGad o a b gs).1
      (swapGad o a b gs).2 (fun x => (signedInterp σ R).op o (f x) (g x)) := by
  cases o with
  | add => exact ⟨isPrefix_emit _ _ _ _, den_emit SignedOp.add ha hb⟩
  | sub => exact ⟨isPrefix_emit _ _ _ _, den_emit SignedOp.sub ha hb⟩
  | sel =>
    have hp := isPrefix_emit SignedOp.add a b gs
    have hq := isPrefix_emit SignedOp.sel a b (emit SignedOp.add a b gs).1
    refine ⟨(hp.trans hq).trans (isPrefix_emit _ _ _ _), (den_emit SignedOp.sub
      ((den_emit SignedOp.add ha hb).mono hq)
      (den_emit SignedOp.sel (ha.mono hp) (hb.mono hp))).congr fun x => ?_⟩
    exact σ.add_sub_swap (f x) (g x)

/-- `swapCircuit C` read with `σ̄` has the outputs of `C` read with `σ`. -/
theorem eval_swapCircuit (σ : Sel) (C : Circuit SignedOp n) (x : Fin n → R) :
    (swapCircuit C).eval (signedInterp σ.swap R) x = C.eval (signedInterp σ R) x := by
  obtain ⟨-, h⟩ := inline_spec (R := Den (signedInterp σ.swap R))
    (J := fun _ => signedInterp σ R) (φ := fun i x => x i) (gad := swapGad)
    (inp := fun i => .input i) (c := .const) (fun _ _ _ _ hp h => h.mono hp) (den_const [])
    (fun i => den_input [] i) (fun o _ _ _ _ _ _ h₁ h₂ => swapGad_spec h₁ h₂ o) C
  exact ((DenL.of_forall₂ h).congr (G := fun x => C.eval (signedInterp σ R) x)
    fun x => by simp only [List.map_map]; rfl).eval x

/-- **Proposition `prop:normal-form`, interchange of the bases.**  Let `σ` be `max` or `min`,
`σ̄` the other one, and `R` an additive commutative group with a linear order.  Every circuit
over `σ`, `+`, `-` and the constant `0` of size `s` has, at every input `x ∈ R^n`, the same
outputs as a circuit over `σ̄`, `+`, `-` and the constant `0` of size at most `3 s`. -/
theorem interchange (σ : Sel) (C : Circuit SignedOp n) :
    ∃ C' : Circuit SignedOp n, C'.size ≤ 3 * C.size ∧
      ∀ x : Fin n → R, C'.eval (signedInterp σ.swap R) x = C.eval (signedInterp σ R) x :=
  ⟨swapCircuit C, size_swapCircuit_le C, eval_swapCircuit σ C⟩

/-- **Interchange for Phase 1's signed tropical circuits**, from `max` to `min`: in an
additive commutative group `R` with a linear order, every circuit over `max`, `+`, `-` of
size `s` has, at every input `x ∈ R^n`, the same outputs as a circuit over `min`, `+`, `-`
of size at most `3 s`. -/
theorem stOp_to_min (C : Circuit STOp n) :
    ∃ C' : Circuit SignedOp n, C'.size ≤ 3 * C.size ∧
      ∀ x : Fin n → R, C'.eval (signedInterp .min R) x = C.eval (stInterp R) x :=
  ⟨swapCircuit (relabel ofSTOp C), (size_swapCircuit_le _).trans_eq (by simp), fun x =>
    (eval_swapCircuit .max _ x).trans (eval_relabel_ofSTOp C x)⟩

/-- **Interchange for Phase 1's signed tropical circuits**, from `min` to `max`: in an
additive commutative group `R` with a linear order, every circuit over `min`, `+`, `-` of
size `s` has, at every input `x ∈ R^n`, the same outputs as a circuit over `max`, `+`, `-`
of size at most `3 s`. -/
theorem min_to_stOp (C : Circuit SignedOp n) :
    ∃ C' : Circuit STOp n, C'.size ≤ 3 * C.size ∧
      ∀ x : Fin n → R, C'.eval (stInterp R) x = C.eval (signedInterp .min R) x :=
  ⟨relabel toSTOp (swapCircuit C), (size_relabel _ _).trans_le (size_swapCircuit_le C),
    fun x => (eval_relabel_toSTOp _ x).trans (eval_swapCircuit .min C x)⟩

variable [IsOrderedAddMonoid R]

/-- **The route of `eq:normal-form`.**  Let `R` be a linearly ordered additive commutative
group.  Every circuit `C` over `max`, `+`, `-` and the constant `0` with `N` outputs is
`A - B`, componentwise at every input `x ∈ R^n`, where `A` and `B` are circuits over `min`,
`+` and the constant `0` with `N` outputs each and `|A| + |B| ≤ 24 |C|`: the interchange to
the `min` basis, then the normal form. -/
theorem normal_form_stOp_min (C : Circuit STOp n) :
    ∃ A B : Circuit PlusOp n, A.size + B.size ≤ 24 * C.size ∧
      A.outs.length = C.outs.length ∧ B.outs.length = C.outs.length ∧
      ∀ x : Fin n → R, C.eval (stInterp R) x =
        List.zipWith (· - ·) (A.eval (plusInterp .min R) x) (B.eval (plusInterp .min R) x) := by
  set C' := swapCircuit (relabel ofSTOp C)
  have hs : C'.size ≤ 3 * C.size := (size_swapCircuit_le _).trans_eq (by simp)
  have hN : C'.outs.length = C.outs.length := by simp [C', swapCircuit, inline, relabel]
  obtain ⟨A, B, hAB, hA, hB, h⟩ := normal_form (R := R) .min C'
  refine ⟨A, B, by omega, hA.trans hN, hB.trans hN, fun x => ?_⟩
  rw [← h x, ← eval_relabel_ofSTOp C x]
  exact (eval_swapCircuit .max _ x).symm

end SwapSpec

/-! ### Theorem A in normal form -/

/-- **Theorem A in normal form.**  Let `M` be a matroid on `Fin m` with ground set `univ` and
rank `k`, and let a Boolean circuit `B` of size `s` output `r(S)` in binary from the indicator
vector of `S`.  Then `h_M = P - Q` at every `w ∈ ℝ^m`, where `P` and `Q` are circuits over
`max`, `+` and the constant `0` with one output each and
`|P| + |Q| ≤ 8 (3 m s + m L + 9 m² + 4 m + 4 L + 1)`, `L = ⌈log₂(k + 1)⌉`. -/
theorem theoremA_normal_form {m : ℕ} (M : Matroid (Fin m)) (hE : M.E = Set.univ)
    (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ P Q : Circuit PlusOp m,
      P.size + Q.size ≤ 8 * (3 * m * B.size + m * Nat.size (rank M) + 9 * m ^ 2 + 4 * m
          + 4 * Nat.size (rank M) + 1) ∧
        ∀ w : Fin m → ℝ, ∃ p q : ℝ, P.eval (plusInterp .max ℝ) w = [p] ∧
          Q.eval (plusInterp .max ℝ) w = [q] ∧ maxBasisWeight M w = p - q := by
  obtain ⟨C, hs, hC⟩ := theoremA M hE B hB
  obtain ⟨P, Q, hPQ, hP, hQ, h⟩ := normal_form_stOp (R := ℝ) C
  refine ⟨P, Q, hPQ.trans (Nat.mul_le_mul_left 8 hs), fun w => ?_⟩
  have h1 : C.outs.length = 1 := by simpa [Circuit.eval] using congrArg List.length (hC w)
  have hone : ∀ D : Circuit PlusOp m, D.outs.length = 1 →
      ∃ v, D.eval (plusInterp .max ℝ) w = [v] :=
    fun D hD => List.length_eq_one_iff.1 (by simp [Circuit.eval, hD])
  obtain ⟨p, hp⟩ := hone P (hP.trans h1)
  obtain ⟨q, hq⟩ := hone Q (hQ.trans h1)
  have := (hC w).symm.trans (h w)
  rw [hp, hq] at this
  exact ⟨p, q, hp, hq, by simpa using this⟩

end SignedTropical.NormalForm
