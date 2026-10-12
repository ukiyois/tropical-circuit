import SignedTropical.Compiler
import SignedTropical.Matroid
import Mathlib.Data.Nat.Size

/-!
# Theorem A: greedy compiled

`docs/research-direction-2026-10-11.md`, Section 3.2, Theorem A.  Let `M` be a matroid on
`E = Fin m` with rank function `r` and `k = r(E)`.  If a Boolean circuit of size `s`
outputs `r(S)` in binary from the indicator vector of `S`, then
`h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^E` by a signed tropical circuit of size
at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`, where `L = ⌈log₂(k + 1)⌉` (`Nat.size k`).

The circuit (`theoremACircuit`):

1. `μ = min_e w_e` by `m - 1` minimum gadgets of three gates (`minListB`);
2. `D_e = w_e - μ ≥ 0`, `m` gates;
3. the integer-observable circuit (`cor:integer-observable`) on `D` for
   `F(S) = r(E \ S)`, whose Boolean circuit is the given one with its inputs negated
   (`negInputs`, `m` more gates) and its outputs truncated to the `L` low bits
   (`truncOuts`; the higher bits are `0` because `r ≤ k < 2^L`);
4. `μ k` by doubling, at most `2 L` gates (`mulConstB`);
5. one addition.

Correctness: `h_M(w) = μ k + h_M(w - μ·1)` (`maxBasisWeight_add_const`) and
`h_M(D) = C_F(D)` on `D ≥ 0` (`maxBasisWeight_eq_gapSum`).  The research document states
the bound `O(ms + m log k + m² + m log² m)`; the term `m log² m` is absent here because the
sorting network costs `O(m²)` (`Sorting.lean`).
-/

open Finset

namespace SignedTropical

variable {n m : ℕ}

/-- A rank of a matroid on `Fin m` is below `2 ^ ⌈log₂(m+1)⌉`. -/
theorem rk_lt_two_pow (M : Matroid (Fin m)) (S : Finset (Fin m)) : rk M S < 2 ^ Nat.size m :=
  ((rk_le_card M S).trans ((card_le_univ S).trans_eq (Fintype.card_fin m))).trans_lt
    (Nat.lt_size_self m)

/-! ### Boolean preprocessing -/

/-- `B` read on the complement of its argument: `m` negation gates, then `B`. -/
def negInputs (B : Circuit BoolOp m) : Circuit BoolOp m :=
  let p := mapB (fun i : Fin m => emit BoolOp.not (.input i) .const) (List.finRange m) []
  let q := inline (fun o a b => emit o a b) (fun i => p.2.getD i .const) .const B p.1
  ⟨q.1, q.2⟩

theorem negInputs_spec (B : Circuit BoolOp m) :
    (negInputs B).size = m + B.size ∧
      ∀ β, (negInputs B).eval boolInterp β = B.eval boolInterp fun i => !β i := by
  obtain ⟨-, hlen, hden⟩ := mapB_spec (I := boolInterp) (c := 1) (gs₀ := [])
    (b := fun i : Fin m => emit BoolOp.not (.input i) .const) (F := fun i x => !x i)
    (fun i gs _ => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
      den_emit BoolOp.not (den_input gs i) (den_const gs)⟩) (List.finRange m) []
    (List.prefix_refl _)
  set p := mapB (fun i : Fin m => emit BoolOp.not (.input i) .const) (List.finRange m) []
  have hinp : ∀ i : Fin m, Den boolInterp p.1 (p.2.getD i .const) (fun x => !x i) := fun i =>
    (hden.getD i).congr fun x => by rw [List.getD_eq_getElem _ _ (by simp)]; simp
  obtain ⟨-, h⟩ := inline_spec (R := Den boolInterp) (J := fun _ => boolInterp)
    (φ := fun i x => !x i) (gad := fun o a b => emit o a b)
    (inp := fun i => p.2.getD i .const) (c := .const)
    (fun _ _ _ _ hp h => h.mono hp) (den_const _) hinp
    (fun o _ _ _ _ gs _ h₁ h₂ => ⟨isPrefix_emit _ _ _ _, den_emit o h₁ h₂⟩) B
  refine ⟨?_, fun β => ?_⟩
  · simp only [negInputs, Circuit.size]
    rw [length_inline (fun _ => 1) (fun o a b gs => length_emit o a b gs) B p.1, hlen]
    simp
  · exact ((DenL.of_forall₂ h).congr (G := fun x => B.eval boolInterp fun i => !x i)
      fun x => by simp only [List.map_map]; rfl).eval β

/-- Keep the first `L` outputs. -/
def truncOuts (B : Circuit BoolOp m) (L : ℕ) : Circuit BoolOp m := ⟨B.gates, B.outs.take L⟩

theorem truncOuts_eval (B : Circuit BoolOp m) (L : ℕ) (β : Fin m → Bool) :
    (truncOuts B L).eval boolInterp β = (B.eval boolInterp β).take L := by
  simp [truncOuts, Circuit.eval, List.map_take]

/-! ### Signed tropical pieces -/

/-- `min a b = a - max(a - b, 0)`, three gates. -/
def minB (a b : Arg n) : Bld STOp n (Arg n) := fun gs =>
  let p₁ := emit .sub a b gs
  let p₂ := emit .max p₁.2 .const p₁.1
  emit .sub a p₂.2 p₂.1

theorem minB_spec {gs : List (Gate STOp n)} {a b : Arg n} {f g : (Fin n → ℝ) → ℝ}
    (ha : Den (stInterp ℝ) gs a f) (hb : Den (stInterp ℝ) gs b g) :
    gs <+: (minB a b gs).1 ∧ (minB a b gs).1.length = gs.length + 3 ∧
      Den (stInterp ℝ) (minB a b gs).1 (minB a b gs).2 (fun x => min (f x) (g x)) := by
  have p₁ : gs <+: (emit STOp.sub a b gs).1 := isPrefix_emit _ _ _ _
  have h₁ := den_emit STOp.sub ha hb
  have h₂ := den_emit STOp.max h₁ (den_const _)
  have p₂ : (emit STOp.sub a b gs).1 <+:
      (emit STOp.max (emit STOp.sub a b gs).2 .const (emit STOp.sub a b gs).1).1 :=
    isPrefix_emit _ _ _ _
  have h₃ := den_emit STOp.sub (ha.mono (p₁.trans p₂)) h₂
  refine ⟨(p₁.trans p₂).trans (isPrefix_emit _ _ _ _), by simp [minB, length_emit],
    h₃.congr fun x => ?_⟩
  simp only [stInterp]
  rcases le_total (f x) (g x) with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

/-- The minimum of a list, `0` for the empty list. -/
noncomputable def minV : List ℝ → ℝ
  | [] => 0
  | [a] => a
  | a :: b :: l => min a (minV (b :: l))

theorem minV_le : ∀ {l : List ℝ}, ∀ y ∈ l, minV l ≤ y
  | [a], y, hy => by simp_all [minV]
  | a :: b :: l, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (minV_le y hy)

theorem minV_mem : ∀ {l : List ℝ}, l ≠ [] → minV l ∈ l
  | [a], _ => by simp [minV]
  | a :: b :: l, _ => by
    rcases min_choice a (minV (b :: l)) with h | h
    · simp [minV, h]
    · rw [minV, h]; exact List.mem_cons_of_mem _ (minV_mem (List.cons_ne_nil _ _))

/-- The minimum of a list of operands by a chain of minimum gadgets. -/
def minListB : List (Arg n) → Bld STOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | [a] => fun gs => (gs, a)
  | a :: b :: l => fun gs =>
    let p := minListB (b :: l) gs
    minB a p.2 p.1

theorem minListB_spec :
    ∀ {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs l F →
      gs <+: (minListB l gs).1 ∧ (minListB l gs).1.length = gs.length + 3 * (l.length - 1) ∧
        Den (stInterp ℝ) (minListB l gs).1 (minListB l gs).2 (fun x => minV (F x))
  | [], F, gs, h => ⟨List.prefix_refl _, by simp [minListB], (den_const gs).congr fun x => by
      rw [show F x = [] by rw [← h.2 x]; rfl]; rfl⟩
  | [a], F, gs, h => by
    obtain ⟨ha, hnil, hF⟩ := h.uncons
    refine ⟨List.prefix_refl _, by simp [minListB], ha.congr fun x => ?_⟩
    rw [hF x, show (F x).tail = [] from (hnil.2 x).symm]; rfl
  | a :: b :: l, F, gs, h => by
    obtain ⟨ha, hbl, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hden⟩ := minListB_spec hbl
    obtain ⟨hq, hlen', hmin⟩ := minB_spec (ha.mono hp) hden
    refine ⟨hp.trans hq, ?_, hmin.congr fun x => ?_⟩
    · simp only [minListB, hlen', hlen, List.length_cons]; omega
    · obtain ⟨_, _, hF'⟩ := hbl.uncons
      rw [hF x, hF' x]
      rfl

/-- `k · a` by doubling, with the recursion depth bounded by `fuel`. -/
def mulConstAux (a : Arg n) : ℕ → ℕ → Bld STOp n (Arg n)
  | 0, _ => fun gs => (gs, .const)
  | fuel + 1, k => fun gs =>
    if k = 0 then (gs, .const) else
      let p := mulConstAux a fuel (k / 2) gs
      let q := emit .add p.2 p.2 p.1
      if k % 2 = 1 then emit .add q.2 a q.1 else q

/-- `k · a` by doubling: at most `2 ⌈log₂(k+1)⌉` gates. -/
def mulConstB (a : Arg n) (k : ℕ) : Bld STOp n (Arg n) := mulConstAux a k k

/-- `⌈log₂(k+1)⌉ = ⌈log₂(⌊k/2⌋+1)⌉ + 1` for `k ≥ 1`. -/
theorem size_div_two_add_one {k : ℕ} (hk : 0 < k) : Nat.size (k / 2) + 1 = Nat.size k := by
  apply le_antisymm
  · rw [Nat.add_one_le_iff, Nat.lt_size]
    rcases Nat.eq_zero_or_pos (Nat.size (k / 2)) with h | h
    · rw [h, pow_zero]; omega
    · obtain ⟨t, ht⟩ : ∃ t, Nat.size (k / 2) = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
      have := Nat.lt_size.1 (show t < Nat.size (k / 2) by omega)
      rw [ht, pow_succ]
      omega
  · rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self (k / 2)
    omega

theorem mulConstAux_spec {a : Arg n} {f : (Fin n → ℝ) → ℝ} :
    ∀ (fuel k : ℕ) {gs : List (Gate STOp n)}, k < 2 ^ fuel → Den (stInterp ℝ) gs a f →
      gs <+: (mulConstAux a fuel k gs).1 ∧
        (mulConstAux a fuel k gs).1.length ≤ gs.length + 2 * Nat.size k ∧
        Den (stInterp ℝ) (mulConstAux a fuel k gs).1 (mulConstAux a fuel k gs).2
          (fun x => k * f x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k gs hk _
    obtain rfl : k = 0 := by simpa using hk
    exact ⟨List.prefix_refl _, by simp [mulConstAux],
      (den_const gs).congr fun x => by simp [stInterp]⟩
  | succ fuel ih =>
    intro k gs hk ha
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨List.prefix_refl _, by simp [mulConstAux],
        (den_const gs).congr fun x => by simp [stInterp]⟩
    · have hk2 : k / 2 < 2 ^ fuel := by rw [pow_succ] at hk; omega
      obtain ⟨hp, hlen, hden⟩ := ih (k / 2) hk2 ha
      have hq := den_emit STOp.add hden hden
      have hsz := size_div_two_add_one (Nat.pos_of_ne_zero hk0)
      have hpq := isPrefix_emit STOp.add (mulConstAux a fuel (k / 2) gs).2
        (mulConstAux a fuel (k / 2) gs).2 (mulConstAux a fuel (k / 2) gs).1
      simp only [mulConstAux, if_neg hk0]
      by_cases hodd : k % 2 = 1
      · rw [if_pos hodd]
        have hr := den_emit STOp.add hq (ha.mono (hp.trans hpq))
        refine ⟨(hp.trans hpq).trans (isPrefix_emit _ _ _ _), ?_, hr.congr fun x => ?_⟩
        · simp only [length_emit]; omega
        · simp only [stInterp]
          have : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + 1 := by
            have := Nat.div_add_mod k 2; rw [hodd] at this; exact_mod_cast this.symm
          rw [this]; ring
      · rw [if_neg hodd]
        refine ⟨hp.trans hpq, ?_, hq.congr fun x => ?_⟩
        · simp only [length_emit]; omega
        · simp only [stInterp]
          have : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) := by
            have := Nat.div_add_mod k 2
            rw [show k % 2 = 0 by omega, add_zero] at this; exact_mod_cast this.symm
          rw [this]; ring

theorem mulConstB_spec {a : Arg n} {f : (Fin n → ℝ) → ℝ} (k : ℕ) {gs : List (Gate STOp n)}
    (ha : Den (stInterp ℝ) gs a f) :
    gs <+: (mulConstB a k gs).1 ∧ (mulConstB a k gs).1.length ≤ gs.length + 2 * Nat.size k ∧
      Den (stInterp ℝ) (mulConstB a k gs).1 (mulConstB a k gs).2 (fun x => k * f x) :=
  mulConstAux_spec k k (Nat.lt_two_pow_self) ha

/-! ### The circuit of Theorem A -/

/-- The circuit of Theorem A, for a Boolean circuit `B` that outputs the rank in binary and
the rank `k = r(E)`. -/
def theoremACircuit (B : Circuit BoolOp m) (k : ℕ) : Circuit STOp m :=
  let B' := truncOuts (negInputs B) (Nat.size k)
  let p₀ := minListB (List.ofFn fun e => .input e) []
  let p₁ := mapB (fun e : Fin m => emit STOp.sub (.input e) p₀.2) (List.finRange m) p₀.1
  let p₂ := intObsB B' p₁.2 p₁.1
  let p₃ := mulConstB p₀.2 k p₂.1
  let p₄ := emit STOp.add p₂.2 p₃.2 p₃.1
  ⟨p₄.1, [p₄.2]⟩

/-- What the circuit of Theorem A computes, at every `w`, and its size. -/
theorem theoremACircuit_spec (B : Circuit BoolOp m) (k : ℕ) :
    (theoremACircuit B k).size
        ≤ 3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 4 * m + 4 * Nat.size k + 1 ∧
      ∀ w : Fin m → ℝ, (theoremACircuit B k).eval (stInterp ℝ) w
        = [hornerV (compVal (truncOuts (negInputs B) (Nat.size k))
            (fun e => w e - minV (List.ofFn w))) + k * minV (List.ofFn w)] := by
  set B' := truncOuts (negInputs B) (Nat.size k)
  obtain ⟨hp₀, hlen₀, hden₀⟩ := minListB_spec (denL_ofFn_input (stInterp ℝ) [])
  set p₀ := minListB (List.ofFn fun e : Fin m => Arg.input e) []
  obtain ⟨hp₁, hlen₁, hden₁⟩ := mapB_spec (I := stInterp ℝ) (c := 1) (gs₀ := p₀.1)
    (b := fun e : Fin m => emit STOp.sub (.input e) p₀.2)
    (F := fun e x => x e - minV (List.ofFn x))
    (fun e gs h => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
      den_emit STOp.sub (den_input gs e) (hden₀.mono h)⟩) (List.finRange m) p₀.1
    (List.prefix_refl _)
  set p₁ := mapB (fun e : Fin m => emit STOp.sub (.input e) p₀.2) (List.finRange m) p₀.1
  have hd : DenL (stInterp ℝ) p₁.1 p₁.2
      (fun x => List.ofFn fun e => x e - minV (List.ofFn x)) :=
    hden₁.congr fun x => List.ofFn_eq_map.symm
  obtain ⟨hp₂, hlen₂, hden₂⟩ := intObsB_spec (B := B') hd
  set p₂ := intObsB B' p₁.2 p₁.1
  obtain ⟨hp₃, hlen₃, hden₃⟩ := mulConstB_spec k (hden₀.mono (hp₁.trans hp₂))
  set p₃ := mulConstB p₀.2 k p₂.1
  have hden₄ := den_emit STOp.add (hden₂.mono hp₃) hden₃
  refine ⟨?_, fun w => ?_⟩
  · have hcost := compileCost_le B'
    have hB'size : B'.size = m + B.size := (negInputs_spec B).1
    have hB'outs : B'.outs.length ≤ Nat.size k := by
      simp [B', truncOuts]
    show (emit STOp.add p₂.2 p₃.2 p₃.1).1.length ≤ _
    rw [length_emit]
    simp only [List.length_ofFn, List.length_nil, zero_add, List.length_finRange,
      one_mul] at hlen₀ hlen₁
    rw [hB'size] at hcost
    have h1 : 3 * (m - 1) ≤ 3 * m := by omega
    have h2 : m * B'.outs.length ≤ m * Nat.size k := Nat.mul_le_mul_left m hB'outs
    have h3 : 3 * m * (m + B.size) = 3 * m * B.size + 3 * m ^ 2 := by ring
    omega
  · exact congrArg (fun v => [v]) ((hden₄.2 w).trans (by simp [stInterp]))

/-- **The circuit of Theorem A computes `h_M`**, at every `w ∈ ℝ^m`. -/
theorem theoremACircuit_correct (M : Matroid (Fin m)) (hE : M.E = Set.univ)
    (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (w : Fin m → ℝ) :
    (theoremACircuit B (rank M)).eval (stInterp ℝ) w = [maxBasisWeight M w] := by
  rw [(theoremACircuit_spec B (rank M)).2]
  set μ := minV (List.ofFn w)
  have hD : ∀ e, 0 ≤ w e - μ := fun e =>
    sub_nonneg.2 (minV_le _ (List.mem_ofFn.2 ⟨e, rfl⟩))
  -- the truncated, complemented circuit computes `r(E \ S)` in binary
  have hrk : ∀ S, bitsVal (B.eval boolInterp (indicator S)) = rk M S := fun S => by
    have := hB S; rw [← coe_rk] at this; exact_mod_cast this
  have hB' : ∀ S, bitsVal ((truncOuts (negInputs B) (Nat.size (rank M))).eval boolInterp
      (indicator S)) = rk M (univ \ S) := by
    intro S
    rw [truncOuts_eval, (negInputs_spec B).2,
      show (fun i => !indicator S i) = indicator (univ \ S) by
        funext i; simp [indicator]]
    rw [bitsVal_take_of_lt, hrk]
    rw [hrk]
    exact (rk_le_rank M _).trans_lt (Nat.lt_size_self _)
  rw [hornerV_compVal hB' hD, ← maxBasisWeight_eq_gapSum hE hD]
  have := maxBasisWeight_add_const M (fun e => w e - μ) μ
  simp only [sub_add_cancel] at this
  rw [show (fun e => w e) = w from rfl] at this
  rw [this, mul_comm]

/-- **Theorem A (greedy compiled).**  Let `M` be a matroid on `Fin m` with ground set
`univ`, rank function `r` and rank `k = r(E)`.  If a Boolean circuit `B` of size `s`
outputs `r(S)` in binary (least significant bit first) from the indicator vector of `S`,
then `h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of
size at most `3 m s + m L + 9 m² + 4 m + 4 L + 1`, `L = ⌈log₂(k + 1)⌉`. -/
theorem theoremA (M : Matroid (Fin m)) (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3 * m * B.size + m * Nat.size (rank M) + 9 * m ^ 2 + 4 * m
          + 4 * Nat.size (rank M) + 1 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight M w] :=
  ⟨theoremACircuit B (rank M), (theoremACircuit_spec B (rank M)).1,
    theoremACircuit_correct M hE B hB⟩

end SignedTropical
