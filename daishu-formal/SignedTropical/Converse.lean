import SignedTropical.TheoremA

/-!
# Theorem B: the converse simulation

`docs/research-direction-2026-10-11.md`, Section 3.2, Theorem B; the same argument is the
left inequality of Theorem `thm:equivalence` of `signed_assignment.tex`.

A signed tropical circuit of size `S` that computes `h_M` on `{0,1}^E` yields a Boolean
circuit of size at most `15 S² + 40 S` that outputs `r(T)` in binary from the indicator
vector of `T`.

Proof route.

1. `h_M(1_T) = r(T)` (`maxBasisWeight_indicator`).
2. On inputs in `{0, 1}` the circuit, read over `ℤ`, has the same values as over `ℝ`
   (homomorphism lemma for `ℤ → ℝ`), and wire `j` carries an integer of absolute value at
   most `2^{j+1}`, so every wire is at most `2^S` (`abs_wires_le`).
3. With `W = S + 2` bits, two's complement arithmetic (`BitVec W`, `bvInterp`) agrees with
   the integers on all wires (`wires_bv`): `+` and `-` are ring operations modulo `2^W`,
   and `max` is read through the signed comparison, which is exact on values of absolute
   value at most `2^S < 2^{W-1}`.
4. Each signed gate is simulated on `W`-bit vectors by a Boolean gadget: a ripple-carry
   adder (`11W` gates), a subtractor `x + ¬y + 1` (`12W + 1` gates), and the signed maximum
   (`15W + 10` gates), whose comparison bit is Lean's `BitVec.slt_eq_not_carry`.  The
   gadgets are proved against `BitVec` addition through `BitVec.getLsbD_add_add_bool` and
   `BitVec.carry_succ`.
5. Inlining with these gadgets (`inline_spec`) gives a Boolean circuit whose outputs are
   the bits of the output of the signed circuit, which is `r(T) ∈ [0, 2^S]`.

The paper's Boolean model has `∧, ∨, ¬`; this one also reads the constant source `false`
(`boolInterp`).  When `m ≥ 1`, `false = x₀ ∧ ¬x₀` costs two gates.
-/

open Finset BitVec

namespace SignedTropical

variable {n m : ℕ}

/-! ### Integer values on `{0, 1}` inputs -/

theorem abs_op_le (o : STOp) (a b : ℤ) :
    |(stInterp ℤ).op o a b| ≤ 2 * max |a| |b| := by
  cases o <;> simp only [stInterp]
  · exact (abs_max_le_max_abs_abs).trans (by linarith [le_max_left |a| |b|, abs_nonneg a])
  · exact (abs_add_le a b).trans (by linarith [le_max_left |a| |b|, le_max_right |a| |b|])
  · exact (abs_sub a b).trans (by linarith [le_max_left |a| |b|, le_max_right |a| |b|])

/-- On inputs of absolute value at most `1`, wire `j` carries at most `2^{j+1}`. -/
theorem abs_wires_getElem_le {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ 1) :
    ∀ (gs : List (Gate STOp n)) (j : ℕ) (h : j < (wires (stInterp ℤ) x gs).length),
      |(wires (stInterp ℤ) x gs)[j]| ≤ 2 ^ (j + 1) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro j h; simp at h
  | append_singleton gs g ih =>
    intro j h
    have hread : ∀ a : Arg n, |a.read (stInterp ℤ) x (wires (stInterp ℤ) x gs)|
        ≤ 2 ^ gs.length := by
      intro a
      cases a with
      | input i => exact (hx i).trans (one_le_pow₀ (by norm_num))
      | const => simp [Arg.read, stInterp]
      | wire j' =>
        simp only [Arg.read]
        by_cases hj' : j' < (wires (stInterp ℤ) x gs).length
        · rw [List.getD_eq_getElem _ _ hj']
          refine (ih j' hj').trans (pow_le_pow_right₀ (by norm_num) ?_)
          simp at hj'; omega
        · rw [List.getD_eq_default _ _ (by omega)]
          simp [stInterp]
    simp only [wires_concat, List.length_append, length_wires, List.length_singleton] at h ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [List.getElem_append_left (by simpa using h)]
      exact ih j (by simpa using h)
    · rw [List.getElem_append_right (by simp)]
      simp only [length_wires, Nat.sub_self, List.getElem_singleton, Gate.eval]
      refine (abs_op_le _ _ _).trans ?_
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right (max_le (hread g.a) (hread g.b)) (by norm_num)

/-- On inputs of absolute value at most `1`, every wire carries at most `2^S`. -/
theorem abs_wires_le {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ 1) (gs : List (Gate STOp n)) :
    ∀ v ∈ wires (stInterp ℤ) x gs, |v| ≤ 2 ^ gs.length := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hv
  refine (abs_wires_getElem_le hx gs j hj).trans (pow_le_pow_right₀ (by norm_num) ?_)
  simp at hj; omega

/-- An output reads an input, the constant or a wire, so it is bounded too. -/
theorem abs_read_le {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ 1) (gs : List (Gate STOp n))
    (a : Arg n) : |a.read (stInterp ℤ) x (wires (stInterp ℤ) x gs)| ≤ 2 ^ gs.length := by
  cases a with
  | input i => exact (hx i).trans (one_le_pow₀ (by norm_num))
  | const => simp [Arg.read, stInterp]
  | wire j =>
    simp only [Arg.read]
    by_cases hj : j < (wires (stInterp ℤ) x gs).length
    · rw [List.getD_eq_getElem _ _ hj]
      exact abs_wires_le hx gs _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [stInterp]

/-- The integer reading maps to the real reading. -/
theorem eval_intCast (C : Circuit STOp n) (x : Fin n → ℤ) :
    C.eval (stInterp ℝ) (fun i => (x i : ℝ)) = (C.eval (stInterp ℤ) x).map (Int.cast) :=
  C.eval_map (Int.cast : ℤ → ℝ) x (by simp [stInterp]) fun o a b => by
    cases o <;> simp [stInterp]

/-! ### Two's complement -/

/-- Signed tropical gates read in `W`-bit two's complement. -/
def bvInterp (W : ℕ) : Interp STOp (BitVec W) where
  zero := 0
  op
    | .max, a, b => if a.slt b then b else a
    | .add, a, b => a + b
    | .sub, a, b => a - b

theorem toInt_ofInt_of_abs_le {W S : ℕ} {a : ℤ} (h : |a| ≤ 2 ^ S) (hW : S + 2 ≤ W) :
    (BitVec.ofInt W a).toInt = a := by
  rw [BitVec.toInt_ofInt]
  obtain ⟨V, rfl⟩ : ∃ V, W = V + 1 := ⟨W - 1, by omega⟩
  have hhalf : (2 : ℤ) ^ (V + 1) / 2 = 2 ^ V := by
    rw [pow_succ]; exact Int.mul_ediv_cancel _ (by norm_num)
  have hSV : (2 : ℤ) ^ S < 2 ^ V := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hup : (2 : ℤ) ^ (V + 1) / 2 ≤ (2 ^ (V + 1) + 1) / 2 :=
    Int.ediv_le_ediv (by norm_num) (by linarith)
  apply Int.bmod_eq_of_le
  · push_cast
    rw [hhalf]
    linarith [neg_abs_le a]
  · push_cast
    rw [hhalf] at hup
    linarith [le_abs_self a]

/-- On bounded integers, `ofInt` commutes with the gates. -/
theorem ofInt_op {W S : ℕ} (hW : S + 2 ≤ W) (o : STOp) {a b : ℤ} (ha : |a| ≤ 2 ^ S)
    (hb : |b| ≤ 2 ^ S) :
    BitVec.ofInt W ((stInterp ℤ).op o a b)
      = (bvInterp W).op o (BitVec.ofInt W a) (BitVec.ofInt W b) := by
  cases o with
  | max =>
    simp only [stInterp, bvInterp]
    have hslt : (BitVec.ofInt W a).slt (BitVec.ofInt W b) = decide (a < b) := by
      rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, toInt_ofInt_of_abs_le ha hW,
        toInt_ofInt_of_abs_le hb hW]
      simp
    rw [hslt]
    by_cases hab : a < b
    · rw [max_eq_right hab.le]; simp [hab]
    · rw [max_eq_left (not_lt.1 hab)]; simp [hab]
  | add => simp [stInterp, bvInterp, BitVec.ofInt_add]
  | sub =>
    simp only [stInterp, bvInterp]
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.toInt_sub, BitVec.toInt_ofInt]

/-- **Two's complement simulation.**  With `W ≥ S + 2` bits, the `BitVec` reading of a
circuit with `S` gates agrees with the integer reading on inputs in `[-1, 1]`. -/
theorem wires_bv {W : ℕ} {x : Fin n → ℤ} (hx : ∀ i, |x i| ≤ 1) (gs : List (Gate STOp n))
    (hW : gs.length + 2 ≤ W) :
    wires (bvInterp W) (fun i => BitVec.ofInt W (x i)) gs
      = (wires (stInterp ℤ) x gs).map (BitVec.ofInt W) :=
  wires_map_of (BitVec.ofInt W) (I := stInterp ℤ) (J := bvInterp W) (x := x)
    (fun v => |v| ≤ 2 ^ gs.length) (by simp [stInterp, bvInterp]) (by simp [stInterp])
    (fun i => (hx i).trans (one_le_pow₀ (by norm_num)))
    (fun o _ _ ha hb => ofInt_op hW o ha hb) gs (abs_wires_le hx gs)

/-! ### Bits -/

/-- The `W` bits of a bit vector, least significant first. -/
def bitsOf {W : ℕ} (v : BitVec W) : List Bool := (List.range W).map v.getLsbD

@[simp] theorem length_bitsOf {W : ℕ} (v : BitVec W) : (bitsOf v).length = W := by
  simp [bitsOf]

theorem bitsVal_testBit (N : ℕ) :
    ∀ W : ℕ, bitsVal ((List.range W).map N.testBit) = N % 2 ^ W := by
  intro W
  induction W generalizing N with
  | zero => simp [Nat.mod_one]
  | succ W ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, bitsVal_cons]
    have : (N.testBit ∘ Nat.succ) = (N / 2).testBit := by
      funext i; simp [Function.comp, Nat.testBit_div_two]
    rw [this, ih, pow_succ', Nat.mod_mul, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h]

theorem bitsVal_bitsOf {W : ℕ} (v : BitVec W) : bitsVal (bitsOf v) = v.toNat := by
  rw [bitsOf, show v.getLsbD = v.toNat.testBit from funext fun i => (BitVec.testBit_toNat v).symm,
    bitsVal_testBit, Nat.mod_eq_of_lt v.isLt]

theorem bitsOf_not {W : ℕ} (v : BitVec W) : bitsOf (~~~v) = (bitsOf v).map (!·) := by
  simp only [bitsOf, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  simp [List.mem_range.1 hi]

theorem getD_bitsOf {W : ℕ} (v : BitVec W) (i : ℕ) : (bitsOf v).getD i false = v.getLsbD i := by
  by_cases hi : i < W
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp [bitsOf]
  · rw [List.getD_eq_default _ _ (by simp; omega), BitVec.getLsbD_of_ge v i (by omega)]

/-- The ripple-carry adder on bit lists. -/
def rcaV : List Bool → List Bool → Bool → List Bool × Bool
  | x :: xs, y :: ys, c =>
    let r := rcaV xs ys (Bool.atLeastTwo x y c)
    ((x ^^ (y ^^ c)) :: r.1, r.2)
  | _, _, c => ([], c)

theorem rcaV_range' {W : ℕ} (X Y : BitVec W) (c : Bool) :
    ∀ k i, i + k = W →
      rcaV ((List.range' i k).map X.getLsbD) ((List.range' i k).map Y.getLsbD) (carry i X Y c)
        = ((List.range' i k).map (X + Y + setWidth W (ofBool c)).getLsbD, carry W X Y c) := by
  intro k
  induction k with
  | zero => intro i hi; simp [rcaV, show i = W by omega]
  | succ k ih =>
    intro i hi
    simp only [List.range'_succ, List.map_cons, rcaV]
    rw [← carry_succ, ih (i + 1) (by omega), getLsbD_add_add_bool (by omega)]

/-- **The ripple-carry adder adds.** -/
theorem rcaV_bitsOf {W : ℕ} (X Y : BitVec W) (c : Bool) :
    rcaV (bitsOf X) (bitsOf Y) c = (bitsOf (X + Y + setWidth W (ofBool c)), carry W X Y c) := by
  simpa [bitsOf, List.range_eq_range'] using rcaV_range' X Y c W 0 (by omega)

theorem sub_eq_add_not_add {W : ℕ} (X Y : BitVec W) :
    X - Y = X + ~~~Y + setWidth W (ofBool true) := by
  have h1 : setWidth W (ofBool true) = 1#W := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h1, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]

/-! ### Boolean gadgets -/

/-- Exclusive or at four gates. -/
def xorB (a b : Arg n) : Bld BoolOp n (Arg n) := fun gs =>
  let p₁ := emit BoolOp.or a b gs
  let p₂ := emit BoolOp.and a b p₁.1
  let p₃ := emit BoolOp.not p₂.2 .const p₂.1
  emit BoolOp.and p₁.2 p₃.2 p₃.1

theorem xorB_spec {gs : List (Gate BoolOp n)} {a b : Arg n} {f g : (Fin n → Bool) → Bool}
    (ha : Den boolInterp gs a f) (hb : Den boolInterp gs b g) :
    gs <+: (xorB a b gs).1 ∧ (xorB a b gs).1.length = gs.length + 4 ∧
      Den boolInterp (xorB a b gs).1 (xorB a b gs).2 (fun x => f x ^^ g x) := by
  have p₁ : gs <+: (emit BoolOp.or a b gs).1 := isPrefix_emit _ _ _ _
  have h₁ := den_emit BoolOp.or ha hb
  have h₂ := den_emit BoolOp.and (ha.mono p₁) (hb.mono p₁)
  have p₂ : (emit BoolOp.or a b gs).1 <+: (emit BoolOp.and a b (emit BoolOp.or a b gs).1).1 :=
    isPrefix_emit _ _ _ _
  have h₃ := den_emit BoolOp.not h₂ (den_const _)
  have h₄ := den_emit BoolOp.and ((h₁.mono p₂).mono (isPrefix_emit _ _ _ _)) h₃
  refine ⟨((p₁.trans p₂).trans (isPrefix_emit _ _ _ _)).trans (isPrefix_emit _ _ _ _),
    by simp [xorB, length_emit], h₄.congr fun x => ?_⟩
  simp only [boolInterp]
  cases f x <;> cases g x <;> rfl

/-- A full adder at nine gates: the sum bit and the carry. -/
def faB (a b c : Arg n) : Bld BoolOp n (Arg n × Arg n) := fun gs =>
  let p₁ := emit BoolOp.and a b gs
  let p₂ := xorB a b p₁.1
  let p₃ := xorB p₂.2 c p₂.1
  let p₄ := emit BoolOp.and p₂.2 c p₃.1
  let p₅ := emit BoolOp.or p₁.2 p₄.2 p₄.1
  (p₅.1, (p₃.2, p₅.2))

theorem faB_spec {gs : List (Gate BoolOp n)} {a b c : Arg n} {f g h : (Fin n → Bool) → Bool}
    (ha : Den boolInterp gs a f) (hb : Den boolInterp gs b g) (hc : Den boolInterp gs c h) :
    gs <+: (faB a b c gs).1 ∧ (faB a b c gs).1.length = gs.length + 11 ∧
      Den boolInterp (faB a b c gs).1 (faB a b c gs).2.1 (fun x => f x ^^ (g x ^^ h x)) ∧
      Den boolInterp (faB a b c gs).1 (faB a b c gs).2.2
        (fun x => Bool.atLeastTwo (f x) (g x) (h x)) := by
  have p₁ : gs <+: (emit BoolOp.and a b gs).1 := isPrefix_emit _ _ _ _
  have h₁ := den_emit BoolOp.and ha hb
  obtain ⟨p₂, l₂, h₂⟩ := xorB_spec (ha.mono p₁) (hb.mono p₁)
  obtain ⟨p₃, l₃, h₃⟩ := xorB_spec h₂ ((hc.mono p₁).mono p₂)
  have h₄ := den_emit BoolOp.and (h₂.mono p₃) (((hc.mono p₁).mono p₂).mono p₃)
  have p₄ := isPrefix_emit BoolOp.and (xorB a b (emit BoolOp.and a b gs).1).2 c
    (xorB (xorB a b (emit BoolOp.and a b gs).1).2 c (xorB a b (emit BoolOp.and a b gs).1).1).1
  have h₅ := den_emit BoolOp.or (((h₁.mono p₂).mono p₃).mono p₄) h₄
  refine ⟨(((p₁.trans p₂).trans p₃).trans p₄).trans (isPrefix_emit _ _ _ _), ?_,
    ((h₃.mono p₄).mono (isPrefix_emit _ _ _ _)).congr fun x => ?_, h₅.congr fun x => ?_⟩
  · simp only [faB, length_emit, l₃, l₂]
  · cases f x <;> cases g x <;> cases h x <;> rfl
  · simp only [boolInterp]; cases f x <;> cases g x <;> cases h x <;> rfl

/-- The ripple-carry adder on operand lists. -/
def rcaB : List (Arg n) → List (Arg n) → Arg n → Bld BoolOp n (List (Arg n) × Arg n)
  | a :: as, b :: bs, c => fun gs =>
    let p := faB a b c gs
    let q := rcaB as bs p.2.2 p.1
    (q.1, (p.2.1 :: q.2.1, q.2.2))
  | _, _, c => fun gs => (gs, ([], c))

theorem rcaB_spec :
    ∀ {as bs : List (Arg n)} {c : Arg n} {A B : (Fin n → Bool) → List Bool}
      {h : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
      DenL boolInterp gs as A → DenL boolInterp gs bs B → Den boolInterp gs c h →
      gs <+: (rcaB as bs c gs).1 ∧
        (rcaB as bs c gs).1.length = gs.length + 11 * min as.length bs.length ∧
        DenL boolInterp (rcaB as bs c gs).1 (rcaB as bs c gs).2.1
          (fun x => (rcaV (A x) (B x) (h x)).1) ∧
        Den boolInterp (rcaB as bs c gs).1 (rcaB as bs c gs).2.2
          (fun x => (rcaV (A x) (B x) (h x)).2)
  | [], bs, c, A, B, h, gs, ha, _, hc => by
    have hA : ∀ x, A x = [] := fun x => by rw [← ha.2 x]; rfl
    refine ⟨List.prefix_refl _, by simp [rcaB], (denL_nil gs).congr fun x => ?_,
      hc.congr fun x => ?_⟩ <;> simp [hA x, rcaV]
  | a :: as, [], c, A, B, h, gs, _, hb, hc => by
    have hB : ∀ x, B x = [] := fun x => by rw [← hb.2 x]; rfl
    refine ⟨List.prefix_refl _, by simp [rcaB], (denL_nil gs).congr fun x => ?_,
      hc.congr fun x => ?_⟩ <;> cases A x <;> simp [hB x, rcaV]
  | a :: as, b :: bs, c, A, B, h, gs, ha, hb, hc => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    obtain ⟨hb₀, hbs, hB⟩ := hb.uncons
    obtain ⟨hp, hlen, hs, hcarry⟩ := faB_spec ha₀ hb₀ hc
    obtain ⟨hq, hlen', hss, hcout⟩ := rcaB_spec (has.mono hp) (hbs.mono hp) hcarry
    refine ⟨hp.trans hq, ?_, (DenL.cons (hs.mono hq) hss).congr fun x => ?_,
      hcout.congr fun x => ?_⟩
    · simp only [rcaB, hlen', hlen, List.length_cons]; rw [Nat.add_min_add_right]; ring
    · conv_rhs => rw [hA x, hB x]
      rfl
    · conv_rhs => rw [hA x, hB x]
      rfl

/-- Negate every operand of a list, one gate each. -/
def notsB : List (Arg n) → Bld BoolOp n (List (Arg n))
  | [] => fun gs => (gs, [])
  | a :: as => fun gs =>
    let p := emit BoolOp.not a .const gs
    let q := notsB as p.1
    (q.1, p.2 :: q.2)

theorem notsB_spec :
    ∀ {as : List (Arg n)} {A : (Fin n → Bool) → List Bool} {gs : List (Gate BoolOp n)},
      DenL boolInterp gs as A →
      gs <+: (notsB as gs).1 ∧ (notsB as gs).1.length = gs.length + as.length ∧
        DenL boolInterp (notsB as gs).1 (notsB as gs).2 (fun x => (A x).map (!·))
  | [], A, gs, ha => ⟨List.prefix_refl _, by simp [notsB], (denL_nil gs).congr fun x => by
      rw [show A x = [] by rw [← ha.2 x]; rfl]; rfl⟩
  | a :: as, A, gs, ha => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    have h₁ := den_emit BoolOp.not ha₀ (den_const gs)
    obtain ⟨hq, hlen, hden⟩ := notsB_spec (has.mono (isPrefix_emit BoolOp.not a .const gs))
    refine ⟨(isPrefix_emit _ _ _ _).trans hq, by simp [notsB, hlen, length_emit]; ring,
      (DenL.cons (h₁.mono hq) hden).congr fun x => ?_⟩
    conv_rhs => rw [hA x]
    rfl

/-- Bitwise selection `(s ∧ yᵢ) ∨ (t ∧ xᵢ)`, three gates per bit. -/
def selB (s t : Arg n) : List (Arg n) → List (Arg n) → Bld BoolOp n (List (Arg n))
  | x :: xs, y :: ys => fun gs =>
    let p₁ := emit BoolOp.and s y gs
    let p₂ := emit BoolOp.and t x p₁.1
    let p₃ := emit BoolOp.or p₁.2 p₂.2 p₂.1
    let q := selB s t xs ys p₃.1
    (q.1, p₃.2 :: q.2)
  | _, _ => fun gs => (gs, [])

theorem selB_spec {s t : Arg n} {σ τ : (Fin n → Bool) → Bool} :
    ∀ {xs ys : List (Arg n)} {X Y : (Fin n → Bool) → List Bool} {gs : List (Gate BoolOp n)},
      Den boolInterp gs s σ → Den boolInterp gs t τ →
      DenL boolInterp gs xs X → DenL boolInterp gs ys Y →
      gs <+: (selB s t xs ys gs).1 ∧
        (selB s t xs ys gs).1.length = gs.length + 3 * min xs.length ys.length ∧
        DenL boolInterp (selB s t xs ys gs).1 (selB s t xs ys gs).2
          (fun x => List.zipWith (fun a b => (σ x && b) || (τ x && a)) (X x) (Y x))
  | [], ys, X, Y, gs, _, _, hx, _ => ⟨List.prefix_refl _, by simp [selB],
      (denL_nil gs).congr fun x => by rw [show X x = [] by rw [← hx.2 x]; rfl]; rfl⟩
  | a :: xs, [], X, Y, gs, _, _, _, hy => ⟨List.prefix_refl _, by simp [selB],
      (denL_nil gs).congr fun x => by rw [show Y x = [] by rw [← hy.2 x]; rfl]; simp⟩
  | a :: xs, b :: ys, X, Y, gs, hs, ht, hx, hy => by
    obtain ⟨ha, hxs, hX⟩ := hx.uncons
    obtain ⟨hb, hys, hY⟩ := hy.uncons
    have p₁ := isPrefix_emit BoolOp.and s b gs
    have h₁ := den_emit BoolOp.and hs hb
    have p₂ := isPrefix_emit BoolOp.and t a (emit BoolOp.and s b gs).1
    have h₂ := den_emit BoolOp.and (ht.mono p₁) (ha.mono p₁)
    have p₃ := isPrefix_emit BoolOp.or (emit BoolOp.and s b gs).2
      (emit BoolOp.and t a (emit BoolOp.and s b gs).1).2
      (emit BoolOp.and t a (emit BoolOp.and s b gs).1).1
    have h₃ := den_emit BoolOp.or (h₁.mono p₂) h₂
    have hpp := (p₁.trans p₂).trans p₃
    obtain ⟨hq, hlen, hden⟩ := selB_spec (hs.mono hpp) (ht.mono hpp) (hxs.mono hpp)
      (hys.mono hpp)
    refine ⟨hpp.trans hq, ?_, (DenL.cons (h₃.mono hq) hden).congr fun x => ?_⟩
    · simp only [selB, hlen, length_emit, List.length_cons]; rw [Nat.add_min_add_right]; ring
    · conv_rhs => rw [hX x, hY x]
      rfl

/-- Pad or cut a list of operands to exactly `W` entries. -/
def fit (W : ℕ) (xs : List (Arg n)) : List (Arg n) :=
  (xs ++ List.replicate W (Arg.const : Arg n)).take W

@[simp] theorem length_fit (W : ℕ) (xs : List (Arg n)) : (fit W xs).length = W := by
  simp [fit]

theorem fit_of_length {W : ℕ} {xs : List (Arg n)} (h : xs.length = W) : fit W xs = xs := by
  simp [fit, ← h]

/-- The gadget for one signed gate on `W`-bit two's complement operands. -/
def bvGad (W : ℕ) (o : STOp) (xs ys : List (Arg n)) : Bld BoolOp n (List (Arg n)) :=
  fun gs =>
  let xs := fit W xs
  let ys := fit W ys
  match o with
  | .add =>
    let p := rcaB xs ys .const gs
    (p.1, p.2.1)
  | .sub =>
    let p₁ := notsB ys gs
    let p₂ := emit BoolOp.not .const .const p₁.1
    let p₃ := rcaB xs p₁.2 p₂.2 p₂.1
    (p₃.1, p₃.2.1)
  | .max =>
    let p₁ := notsB ys gs
    let p₂ := emit BoolOp.not .const .const p₁.1
    let p₃ := rcaB xs p₁.2 p₂.2 p₂.1
    let p₄ := xorB (xs.getD (W - 1) .const) (ys.getD (W - 1) .const) p₃.1
    let p₅ := xorB p₄.2 p₃.2.2 p₄.1
    let p₆ := emit BoolOp.not p₅.2 .const p₅.1
    selB p₆.2 p₅.2 xs ys p₆.1

/-- Gates of the gadget. -/
def bvCost (W : ℕ) : STOp → ℕ
  | .add => 11 * W
  | .sub => 12 * W + 1
  | .max => 15 * W + 10

theorem rcaB_length {as bs : List (Arg n)} {c : Arg n} {gs : List (Gate BoolOp n)} :
    (rcaB as bs c gs).1.length = gs.length + 11 * min as.length bs.length := by
  induction as generalizing bs c gs with
  | nil => simp [rcaB]
  | cons a as ih =>
    cases bs with
    | nil => simp [rcaB]
    | cons b bs =>
      simp only [rcaB, ih, List.length_cons, Nat.add_min_add_right]
      have : (faB a b c gs).1.length = gs.length + 11 := by
        simp [faB, xorB, length_emit]
      rw [this]; ring

theorem notsB_length {as : List (Arg n)} {gs : List (Gate BoolOp n)} :
    (notsB as gs).1.length = gs.length + as.length := by
  induction as generalizing gs with
  | nil => simp [notsB]
  | cons a as ih => simp [notsB, ih, length_emit]; ring

theorem notsB_length₂ {as : List (Arg n)} {gs : List (Gate BoolOp n)} :
    (notsB as gs).2.length = as.length := by
  induction as generalizing gs with
  | nil => simp [notsB]
  | cons a as ih => simp [notsB, ih]

theorem selB_length {s t : Arg n} {xs ys : List (Arg n)} {gs : List (Gate BoolOp n)} :
    (selB s t xs ys gs).1.length = gs.length + 3 * min xs.length ys.length := by
  induction xs generalizing ys gs with
  | nil => simp [selB]
  | cons a xs ih =>
    cases ys with
    | nil => simp [selB]
    | cons b ys => simp [selB, ih, length_emit, Nat.add_min_add_right]; ring

theorem length_bvGad (W : ℕ) (o : STOp) (xs ys : List (Arg n)) (gs : List (Gate BoolOp n)) :
    (bvGad W o xs ys gs).1.length = gs.length + bvCost W o := by
  cases o <;>
    simp [bvGad, bvCost, rcaB_length, notsB_length, notsB_length₂, selB_length, xorB,
      length_emit] <;> ring

/-- The representation of a `W`-bit value by `W` operands. -/
def BitRep (W : ℕ) (gs : List (Gate BoolOp n)) (r : List (Arg n))
    (F : (Fin n → Bool) → BitVec W) : Prop :=
  DenL boolInterp gs r (fun x => bitsOf (F x))

theorem BitRep.fit {W : ℕ} {gs : List (Gate BoolOp n)} {r : List (Arg n)}
    {F : (Fin n → Bool) → BitVec W} (h : BitRep W gs r F) : fit W r = r := by
  apply fit_of_length
  rw [← h.length_eq (fun _ => false), length_bitsOf]

theorem msb_slt (X Y : BitVec W) :
    ((X.getLsbD (W - 1) ^^ Y.getLsbD (W - 1)) ^^ carry W X (~~~Y) true) = !X.slt Y := by
  rw [slt_eq_not_carry, msb_eq_getLsbD_last, msb_eq_getLsbD_last]
  cases X.getLsbD (W - 1) <;> cases Y.getLsbD (W - 1) <;> cases carry W X (~~~Y) true <;> rfl

/-- The output of the signed-maximum gadget. -/
theorem sel_eq (X Y : BitVec W) :
    List.zipWith (fun a b =>
      (!((X.getLsbD (W - 1) ^^ Y.getLsbD (W - 1)) ^^
          (rcaV (bitsOf X) ((bitsOf Y).map (!·)) true).2) && b) ||
        (((X.getLsbD (W - 1) ^^ Y.getLsbD (W - 1)) ^^
          (rcaV (bitsOf X) ((bitsOf Y).map (!·)) true).2) && a))
      (bitsOf X) (bitsOf Y) = bitsOf (if X.slt Y then Y else X) := by
  have hs : ((X.getLsbD (W - 1) ^^ Y.getLsbD (W - 1)) ^^
      (rcaV (bitsOf X) ((bitsOf Y).map (!·)) true).2) = !X.slt Y := by
    rw [← bitsOf_not, rcaV_bitsOf]
    exact msb_slt X Y
  rw [hs, Bool.not_not]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  by_cases h : X.slt Y <;> simp [h, bitsOf]

/-- **The gadgets implement two's complement arithmetic.** -/
theorem bvGad_spec {W : ℕ} {xs ys : List (Arg n)} {X Y : (Fin n → Bool) → BitVec W}
    {gs : List (Gate BoolOp n)} (hx : BitRep W gs xs X) (hy : BitRep W gs ys Y) (o : STOp) :
    gs <+: (bvGad W o xs ys gs).1 ∧
      BitRep W (bvGad W o xs ys gs).1 (bvGad W o xs ys gs).2
        (fun x => (bvInterp W).op o (X x) (Y x)) := by
  have hxs := hx.fit
  have hys := hy.fit
  cases o with
  | add =>
    obtain ⟨hp, -, hs, -⟩ := rcaB_spec hx hy (den_const (I := boolInterp) gs)
    simp only [bvGad, hxs, hys]
    refine ⟨hp, hs.congr fun x => ?_⟩
    simp only [bvInterp, boolInterp]
    rw [rcaV_bitsOf]
    simp
  | sub =>
    obtain ⟨hp₁, -, hn⟩ := notsB_spec hy
    have h₂ := den_emit BoolOp.not (den_const (I := boolInterp) (notsB ys gs).1) (den_const _)
    have p₂ := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const (notsB ys gs).1
    obtain ⟨hp₃, -, hs, -⟩ := rcaB_spec ((hx.mono hp₁).mono p₂) (hn.mono p₂) h₂
    simp only [bvGad, hxs, hys]
    refine ⟨(hp₁.trans p₂).trans hp₃, hs.congr fun x => ?_⟩
    simp only [bvInterp, boolInterp, Bool.not_false]
    rw [← bitsOf_not, rcaV_bitsOf, sub_eq_add_not_add]
  | max =>
    obtain ⟨hp₁, -, hn⟩ := notsB_spec hy
    have h₂ := den_emit BoolOp.not (den_const (I := boolInterp) (notsB ys gs).1) (den_const _)
    have p₂ := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const (notsB ys gs).1
    obtain ⟨hp₃, -, -, hc⟩ := rcaB_spec ((hx.mono hp₁).mono p₂) (hn.mono p₂) h₂
    set p₃ := rcaB xs (notsB ys gs).2 (emit BoolOp.not .const .const (notsB ys gs).1).2
      (emit BoolOp.not .const .const (notsB ys gs).1).1
    have hpp := (hp₁.trans p₂).trans hp₃
    have hmx := ((hx.mono hpp).getD (W - 1))
    have hmy := ((hy.mono hpp).getD (W - 1))
    obtain ⟨hp₄, -, he⟩ := xorB_spec hmx hmy
    obtain ⟨hp₅, -, hs⟩ := xorB_spec he (hc.mono hp₄)
    have h₆ := den_emit BoolOp.not hs (den_const _)
    have p₆ := isPrefix_emit BoolOp.not (xorB (xorB (xs.getD (W - 1) .const)
      (ys.getD (W - 1) .const) p₃.1).2 p₃.2.2 (xorB (xs.getD (W - 1) .const)
      (ys.getD (W - 1) .const) p₃.1).1).2 .const (xorB (xorB (xs.getD (W - 1) .const)
      (ys.getD (W - 1) .const) p₃.1).2 p₃.2.2 (xorB (xs.getD (W - 1) .const)
      (ys.getD (W - 1) .const) p₃.1).1).1
    have hall := ((hpp.trans hp₄).trans hp₅).trans p₆
    obtain ⟨hp₇, -, hsel⟩ := selB_spec h₆ (hs.mono p₆) (hx.mono hall) (hy.mono hall)
    simp only [bvGad, hxs, hys]
    refine ⟨hall.trans hp₇, hsel.congr fun x => ?_⟩
    simp only [bvInterp, boolInterp, Bool.not_false]
    rw [getD_bitsOf, getD_bitsOf]
    exact sel_eq (X x) (Y x)

/-! ### The simulating Boolean circuit -/

/-- The Boolean circuit simulating `C` on `W`-bit two's complement values; its outputs are
the bits of the outputs of `C`. -/
def simulate (W : ℕ) (C : Circuit STOp m) : Circuit BoolOp m :=
  let p := inline (bvGad W) (fun i => .input i :: List.replicate (W - 1) .const)
    (List.replicate W .const) C []
  ⟨p.1, p.2.flatten⟩

theorem simulate_size (W : ℕ) (C : Circuit STOp m) :
    (simulate W C).size ≤ C.size * (15 * W + 10) := by
  simp only [simulate, Circuit.size]
  rw [length_inline (bvCost W) (length_bvGad W) C [], List.length_nil, zero_add]
  have : ∀ o, bvCost W o ≤ 15 * W + 10 := fun o => by cases o <;> simp [bvCost] <;> omega
  calc (C.gates.map fun g => bvCost W g.op).sum
      ≤ (C.gates.map fun _ => 15 * W + 10).sum := List.sum_le_sum fun g _ => this g.op
    _ = C.gates.length * (15 * W + 10) := by simp

theorem bitsOf_zero (W : ℕ) : bitsOf (0 : BitVec W) = List.replicate W false := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [bitsOf]

theorem bitsOf_ofBool {W : ℕ} (hW : 1 ≤ W) (b : Bool) :
    bitsOf (BitVec.ofNat W b.toNat) = b :: List.replicate (W - 1) false := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [bitsOf, List.getElem_map, List.getElem_range, BitVec.getLsbD_ofNat]
  rcases i with _ | i
  · cases b <;> simp; omega
  · simp only [List.getElem_cons_succ, List.getElem_replicate]
    cases b <;> simp [Nat.testBit_succ]

/-- Reading the concatenated representations of several outputs. -/
theorem flatten_read {W : ℕ} {gs : List (Gate BoolOp m)} (x : Fin m → Bool) :
    ∀ {reps : List (List (Arg m))} {Fs : List ((Fin m → Bool) → BitVec W)},
      List.Forall₂ (fun r F => BitRep W gs r F) reps Fs →
      reps.flatten.map (Arg.read boolInterp x (wires boolInterp x gs))
        = (Fs.map (· x)).flatMap bitsOf
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hs => by
    rw [List.flatten_cons, List.map_append, h.2 x, flatten_read x hs]
    rfl

/-- **The simulation is correct**: on every input, the outputs of `simulate W C` are the
bits of the outputs of `C` read in `W`-bit two's complement. -/
theorem simulate_eval {W : ℕ} (hW : 1 ≤ W) (C : Circuit STOp m) (x : Fin m → Bool) :
    (simulate W C).eval boolInterp x
      = (C.eval (bvInterp W) (fun i => BitVec.ofNat W (x i).toNat)).flatMap bitsOf := by
  obtain ⟨-, h⟩ := inline_spec (R := BitRep W) (J := fun _ => bvInterp W)
    (φ := fun i x => BitVec.ofNat W (x i).toNat) (gad := bvGad W)
    (inp := fun i => .input i :: List.replicate (W - 1) .const)
    (c := List.replicate W .const) (gs₀ := [])
    (fun _ _ _ _ hp h => DenL.mono h hp)
    (⟨by simp [Arg.Valid], fun x => by
      show _ = bitsOf (0 : BitVec W)
      rw [bitsOf_zero]; simp [Arg.read, boolInterp]⟩)
    (fun i => ⟨by simp [Arg.Valid], fun x => by simp [bitsOf_ofBool hW, Arg.read, boolInterp]⟩)
    (fun o _ _ _ _ gs _ h₁ h₂ => bvGad_spec h₁ h₂ o) C
  simp only [simulate, Circuit.eval]
  rw [flatten_read x h, List.map_map]
  rfl

/-- **Theorem B (the converse).**  Let `M` be a matroid on `Fin m` with ground set `univ`.
If a signed tropical circuit `C` of size `S` computes `h_M` on `{0,1}^m`, that is at the
indicator vector of every set `T`, then a Boolean circuit of size at most `15 S² + 40 S`
outputs `r(T)` in binary from the indicator vector of `T`. -/
theorem theoremB (M : Matroid (Fin m)) (hE : M.E = Set.univ) (C : Circuit STOp m)
    (hC : ∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
      = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]) :
    ∃ B : Circuit BoolOp m, B.size ≤ 15 * C.size ^ 2 + 40 * C.size ∧
      ∀ T : Finset (Fin m),
        (bitsVal (B.eval boolInterp (indicator T)) : ℕ∞) = M.eRk (T : Set (Fin m)) := by
  set S := C.size
  set W := S + 2
  refine ⟨simulate W C, (simulate_size W C).trans (le_of_eq (by simp only [W, S]; ring)),
    fun T => ?_⟩
  -- integer inputs
  set xz : Fin m → ℤ := fun i => if i ∈ T then 1 else 0
  have hxz : ∀ i, |xz i| ≤ 1 := fun i => by by_cases hi : i ∈ T <;> simp [xz, hi]
  -- the real and integer readings
  have hreal := hC T
  rw [show (fun e => if e ∈ T then (1 : ℝ) else 0) = fun e => ((xz e : ℤ) : ℝ) by
    funext e; by_cases he : e ∈ T <;> simp [xz, he], eval_intCast] at hreal
  rw [show (fun e => ((xz e : ℤ) : ℝ)) = fun e => if e ∈ T then 1 else 0 by
    funext e; by_cases he : e ∈ T <;> simp [xz, he], maxBasisWeight_indicator hE] at hreal
  have hlen : (C.eval (stInterp ℤ) xz).length = 1 := by
    have := congrArg List.length hreal; simpa using this
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.1 hlen
  rw [hr] at hreal
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hreal
  have hrz : r = rk M T := by exact_mod_cast hreal
  -- the bound on the output
  have hCo : C.outs.length = 1 := by simpa [Circuit.eval] using hlen
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.1 hCo
  have hrbound : r ≤ 2 ^ S := by
    have : C.eval (stInterp ℤ) xz = [o.read (stInterp ℤ) xz (wires (stInterp ℤ) xz C.gates)] := by
      simp [Circuit.eval, ho]
    rw [hr] at this
    simp only [List.cons.injEq, and_true] at this
    rw [this]
    exact le_of_abs_le (abs_read_le hxz C.gates o)
  -- the two's complement reading
  have hbv : C.eval (bvInterp W) (fun i => BitVec.ofNat W (indicator T i).toNat)
      = [BitVec.ofInt W r] := by
    have hin : (fun i => BitVec.ofNat W (indicator T i).toNat)
        = fun i => BitVec.ofInt W (xz i) := by
      funext i; by_cases hi : i ∈ T <;> simp [indicator, xz, hi]
    rw [hin]
    have hw := wires_bv (W := W) hxz C.gates (by simp [W, S, Circuit.size])
    simp only [Circuit.eval, hw]
    rw [show C.outs.map (Arg.read (bvInterp W) (fun i => BitVec.ofInt W (xz i))
        ((wires (stInterp ℤ) xz C.gates).map (BitVec.ofInt W)))
        = (C.eval (stInterp ℤ) xz).map (BitVec.ofInt W) by
      simp only [Circuit.eval, List.map_map]
      exact List.map_congr_left fun a _ => Arg.read_map (BitVec.ofInt W) xz (by
        simp [stInterp, bvInterp]) _ a, hr]
    rfl
  rw [simulate_eval (by omega), hbv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    bitsVal_bitsOf, ← coe_rk]
  congr 1
  have hr0 : 0 ≤ r := by rw [hrz]; positivity
  have hrW : r < 2 ^ W := by
    have : (2 : ℤ) ^ S < 2 ^ W := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hr0 (by exact_mod_cast hrW), hrz]
  simp

/-- Theorem B for a circuit that computes `h_M` at every `w ∈ ℝ^m`. -/
theorem theoremB_of_forall (M : Matroid (Fin m)) (hE : M.E = Set.univ) (C : Circuit STOp m)
    (hC : ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight M w]) :
    ∃ B : Circuit BoolOp m, B.size ≤ 15 * C.size ^ 2 + 40 * C.size ∧
      ∀ T : Finset (Fin m),
        (bitsVal (B.eval boolInterp (indicator T)) : ℕ∞) = M.eRk (T : Set (Fin m)) :=
  theoremB M hE C fun _ => hC _

end SignedTropical
