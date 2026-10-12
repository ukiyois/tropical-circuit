import SignedTropical.BoolAlg.Bits
import SignedTropical.Counting

/-!
# Binary numbers

A natural number is carried in binary, least significant bit first, as `bitsVal` reads it
(`Models.lean`): `numR w` represents `N` by `w` operands whose bits have value `N`, so every value
it carries is below `2 ^ w` (`numR_lt`).  For two arguments of widths `w₁`, `w₂` put
`W = max w₁ w₂`; the shorter one is padded with the constant `false`.  Gate counts are exact
(`Impl` of `BoolAlg/Impl.lean`).

| gadget | value | width | gates |
| :-- | :-- | :-- | :-- |
| `numConstB c w` | `c mod 2^w` | `w` | `1` |
| `numAddB` | `a + b` | `W + 1` | `11 W` |
| `numSubB` | `a - b`, truncated at `0` | `w₁` | `12 W + w₁ + 1` |
| `numLeB` | `[a ≤ b]` | bit | `5 W + 1` |
| `numLtB` | `[a < b]` | bit | `5 W + 2` |
| `numEqB` | `[a = b]` | bit | `5 W + 1` |
| `numMuxB` | `if s then a else b` | `W` | `3 W + 1` |
| `numMaskB` | `if s then a else 0` | `w` | `w` |
| `numMinB` | `min a b` | `W` | `8 W + 2` |

With a constant `c` as second argument, on `W = max w ⌈log₂(c+1)⌉` bits, one more gate is
spent on the constant: `numLeConstB` (`[a ≤ c]`), `numGeConstB` (`[c ≤ a]`), `numEqConstB`
(`[a = c]`), `numSubConstB` (`a - c`, on `w` bits), `numMinConstB` (`min a c`).  Reading bits as
a number (`numOfBits_impl`, `numOfBit_impl`), widening (`numWiden_impl`), truncation
(`numTrunc_impl`, the value modulo `2^W`) and fitting to any width (`numFit_impl`, the value
modulo `2^W`) cost no gate.
-/

namespace SignedTropical.BoolAlg

open Finset

variable {n : ℕ} {σ τ : Type}

/-! ### Values of bit lists -/

/-- The value of a concatenation. -/
theorem bitsVal_append (l₁ l₂ : List Bool) :
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂ := by
  induction l₁ with
  | nil => simp
  | cons b l ih => simp only [List.cons_append, bitsVal_cons, ih, List.length_cons]; ring

/-- Keeping the low `k` bits: the value modulo `2 ^ k`. -/
theorem bitsVal_take (k : ℕ) (l : List Bool) : bitsVal (l.take k) = bitsVal l % 2 ^ k := by
  have hlt : bitsVal (l.take k) < 2 ^ k :=
    (bitsVal_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) (by simp))
  rw [bitsVal_eq_take_add k l, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The complement of `l` has value `2 ^ |l| - 1 - bitsVal l`. -/
theorem bitsVal_map_not (l : List Bool) :
    bitsVal (l.map (!·)) + bitsVal l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp [pow_succ] <;> omega

/-- Every bit in conjunction with `c`: the value if `c`, and `0` otherwise. -/
theorem bitsVal_map_and (c : Bool) (l : List Bool) :
    bitsVal (l.map (· && c)) = if c then bitsVal l else 0 := by
  induction l with
  | nil => simp
  | cons b l ih => cases c <;> simp_all

/-- Bitwise selection between two lists of one length selects the value. -/
theorem bitsVal_zipWith_sel (s : Bool) :
    ∀ l₁ l₂ : List Bool, l₁.length = l₂.length →
      bitsVal (List.zipWith (fun a b => (s && b) || (!s && a)) l₁ l₂)
        = if s then bitsVal l₂ else bitsVal l₁
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    have ih := bitsVal_zipWith_sel s l₁ l₂ (by simpa using h)
    cases s <;> simp_all
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

/-- Bit lists of one length are determined by their values. -/
theorem eq_of_bitsVal_eq : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length →
    bitsVal l₁ = bitsVal l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, h, hv => by
    simp only [bitsVal_cons] at hv
    have hab : a = b := by cases a <;> cases b <;> simp at hv ⊢ <;> omega
    subst hab
    rw [eq_of_bitsVal_eq (l₁ := l₁) (l₂ := l₂) (by simpa using h) (by omega)]
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)

/-- Two lists of one length differ iff some bit of their exclusive or is set. -/
theorem any_zipWith_xor : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length →
    (List.zipWith (· ^^ ·) l₁ l₂).any id = !decide (l₁ = l₂)
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    rw [List.zipWith_cons_cons, List.any_cons, any_zipWith_xor (by simpa using h)]
    cases a <;> cases b <;> simp
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

/-- The ripple-carry adder returns as many sum bits as the shorter list has bits. -/
theorem length_rcaV : ∀ (xs ys : List Bool) (c : Bool),
    (rcaV xs ys c).1.length = min xs.length ys.length
  | _ :: xs, _ :: ys, _ => by
    simp only [rcaV, List.length_cons, length_rcaV xs ys, Nat.add_min_add_right]
  | [], _, _ => by simp [rcaV]
  | _ :: _, [], _ => by simp [rcaV]

/-- **The ripple-carry adder adds**: its sum bits and carry are `x + y + c`. -/
theorem bitsVal_rcaV : ∀ (xs ys : List Bool) (c : Bool), xs.length = ys.length →
    bitsVal (rcaV xs ys c).1 + 2 ^ xs.length * (rcaV xs ys c).2.toNat
      = bitsVal xs + bitsVal ys + c.toNat
  | [], [], c, _ => by simp [rcaV]
  | x :: xs, y :: ys, c, h => by
    have ih := bitsVal_rcaV xs ys (Bool.atLeastTwo x y c) (by simpa using h)
    have key : (x ^^ (y ^^ c)).toNat + 2 * (Bool.atLeastTwo x y c).toNat
        = x.toNat + y.toNat + c.toNat := by
      cases x <;> cases y <;> cases c <;> rfl
    simp only [rcaV, bitsVal_cons, List.length_cons, pow_succ]
    linarith
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)

/-- The carry of `x + y + 1` on `W` bits, with `y` the complement of `b`: set iff `b ≤ x`, and
then the sum is `x - b`. -/
theorem rcaV_not_carry {xs bs : List Bool} (h : xs.length = bs.length) :
    (rcaV xs (bs.map (!·)) true).2 = decide (bitsVal bs ≤ bitsVal xs) ∧
      (bitsVal bs ≤ bitsVal xs →
        bitsVal (rcaV xs (bs.map (!·)) true).1 = bitsVal xs - bitsVal bs) := by
  have hv := bitsVal_rcaV xs (bs.map (!·)) true (by simpa using h)
  have hn := bitsVal_map_not bs
  have hS := bitsVal_lt (rcaV xs (bs.map (!·)) true).1
  have hX := bitsVal_lt xs
  rw [length_rcaV, List.length_map, ← h, min_self] at hS
  rw [← h] at hn
  cases hc : (rcaV xs (bs.map (!·)) true).2 <;> simp only [hc, Bool.toNat_true,
    Bool.toNat_false, mul_one, mul_zero, Bool.toNat_true] at hv <;> constructor
  · simp only [Bool.false_eq, decide_eq_false_iff_not, not_le]; omega
  · intro hle; omega
  · simp only [Bool.true_eq, decide_eq_true_eq]; omega
  · intro _; omega

/-! ### Lists of operands -/

/-- The first `k` operands carry the first `k` values. -/
theorem denL_take {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {A : (Fin n → Bool) → List Bool} (h : DenL boolInterp gs as A) (k : ℕ) :
    DenL boolInterp gs (as.take k) (fun x => (A x).take k) :=
  ⟨fun a ha => h.1 a (List.mem_of_mem_take ha), fun x => by rw [List.map_take, h.2 x]⟩

/-- The operands after the first `k` carry the values after the first `k`. -/
theorem denL_drop {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {A : (Fin n → Bool) → List Bool} (h : DenL boolInterp gs as A) (k : ℕ) :
    DenL boolInterp gs (as.drop k) (fun x => (A x).drop k) :=
  ⟨fun a ha => h.1 a (List.mem_of_mem_drop ha), fun x => by rw [List.map_drop, h.2 x]⟩

/-- Copies of the constant source carry `false`. -/
theorem denL_replicate_const (gs : List (Gate BoolOp n)) (k : ℕ) :
    DenL boolInterp gs (List.replicate k .const) (fun _ => List.replicate k false) :=
  ⟨by simp [Arg.Valid], fun x => by simp [Arg.read, boolInterp]⟩

/-- Fitting a list of at most `W` operands to `W` operands pads it with the constant. -/
theorem fit_eq_append {W : ℕ} {as : List (Arg n)} (h : as.length ≤ W) :
    fit W as = as ++ List.replicate (W - as.length) .const := by
  rw [fit, List.take_append, List.take_of_length_le h, List.take_replicate,
    min_eq_left (Nat.sub_le W as.length)]

/-- `c ∧ aᵢ` for every operand `aᵢ` of a list, one gate each. -/
def andEachB (c : Arg n) : List (Arg n) → Bld BoolOp n (List (Arg n))
  | [] => fun gs => (gs, [])
  | a :: as => fun gs =>
    let p := emit .and a c gs
    let q := andEachB c as p.1
    (q.1, p.2 :: q.2)

/-- `andEachB c`: one gate per operand, every value in conjunction with `c`. -/
theorem andEachB_spec {c : Arg n} {C : (Fin n → Bool) → Bool} :
    ∀ {as : List (Arg n)} {A : (Fin n → Bool) → List Bool} {gs : List (Gate BoolOp n)},
      DenL boolInterp gs as A → Den boolInterp gs c C →
      gs <+: (andEachB c as gs).1 ∧ (andEachB c as gs).1.length = gs.length + as.length ∧
        DenL boolInterp (andEachB c as gs).1 (andEachB c as gs).2
          (fun x => (A x).map (· && C x))
  | [], A, gs, ha, _ => ⟨List.prefix_refl _, by simp [andEachB],
      (denL_nil gs).congr fun x => by rw [show A x = [] by rw [← ha.2 x]; rfl]; rfl⟩
  | a :: as, A, gs, ha, hc => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    have p₁ := isPrefix_emit BoolOp.and a c gs
    obtain ⟨hq, hlen, hden⟩ := andEachB_spec (has.mono p₁) (hc.mono p₁)
    refine ⟨p₁.trans hq, by simp [andEachB, hlen, length_emit]; ring,
      (DenL.cons ((den_emit BoolOp.and ha₀ hc).mono hq) hden).congr fun x => ?_⟩
    conv_rhs => rw [hA x]
    rfl

/-- Bitwise exclusive or of two lists, four gates per pair. -/
def xorsB : List (Arg n) → List (Arg n) → Bld BoolOp n (List (Arg n))
  | a :: as, b :: bs => fun gs =>
    let p := xorB a b gs
    let q := xorsB as bs p.1
    (q.1, p.2 :: q.2)
  | _, _ => fun gs => (gs, [])

/-- `xorsB`: four gates per pair, the bitwise exclusive or. -/
theorem xorsB_spec :
    ∀ {as bs : List (Arg n)} {A B : (Fin n → Bool) → List Bool} {gs : List (Gate BoolOp n)},
      DenL boolInterp gs as A → DenL boolInterp gs bs B →
      gs <+: (xorsB as bs gs).1 ∧
        (xorsB as bs gs).1.length = gs.length + 4 * min as.length bs.length ∧
        DenL boolInterp (xorsB as bs gs).1 (xorsB as bs gs).2
          (fun x => List.zipWith (· ^^ ·) (A x) (B x))
  | [], bs, A, B, gs, ha, _ => ⟨List.prefix_refl _, by simp [xorsB],
      (denL_nil gs).congr fun x => by rw [show A x = [] by rw [← ha.2 x]; rfl]; rfl⟩
  | a :: as, [], A, B, gs, _, hb => ⟨List.prefix_refl _, by simp [xorsB],
      (denL_nil gs).congr fun x => by rw [show B x = [] by rw [← hb.2 x]; rfl]; simp⟩
  | a :: as, b :: bs, A, B, gs, ha, hb => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    obtain ⟨hb₀, hbs, hB⟩ := hb.uncons
    obtain ⟨p₁, l₁, h₁⟩ := xorB_spec ha₀ hb₀
    obtain ⟨hq, hlen, hden⟩ := xorsB_spec (has.mono p₁) (hbs.mono p₁)
    refine ⟨p₁.trans hq, ?_, (DenL.cons (h₁.mono hq) hden).congr fun x => ?_⟩
    · simp only [xorsB, hlen, l₁, List.length_cons, Nat.add_min_add_right]; ring
    · conv_rhs => rw [hA x, hB x]
      rfl

/-- The carry chain alone, `cᵢ₊₁ = (xᵢ ∧ yᵢ) ∨ (cᵢ ∧ (xᵢ ∨ yᵢ))`: four gates per bit. -/
def carryB : List (Arg n) → List (Arg n) → Arg n → Bld BoolOp n (Arg n)
  | a :: as, b :: bs, c => fun gs =>
    let p₁ := emit .and a b gs
    let p₂ := emit .or a b p₁.1
    let p₃ := emit .and c p₂.2 p₂.1
    let p₄ := emit .or p₁.2 p₃.2 p₃.1
    carryB as bs p₄.2 p₄.1
  | _, _, c => fun gs => (gs, c)

/-- `carryB`: four gates per pair, the carry of the ripple-carry adder. -/
theorem carryB_spec :
    ∀ {as bs : List (Arg n)} {c : Arg n} {A B : (Fin n → Bool) → List Bool}
      {C : (Fin n → Bool) → Bool} {gs : List (Gate BoolOp n)},
      DenL boolInterp gs as A → DenL boolInterp gs bs B → Den boolInterp gs c C →
      gs <+: (carryB as bs c gs).1 ∧
        (carryB as bs c gs).1.length = gs.length + 4 * min as.length bs.length ∧
        Den boolInterp (carryB as bs c gs).1 (carryB as bs c gs).2
          (fun x => (rcaV (A x) (B x) (C x)).2)
  | [], bs, c, A, B, C, gs, ha, _, hc => by
    have hA : ∀ x, A x = [] := fun x => by rw [← ha.2 x]; rfl
    exact ⟨List.prefix_refl _, by simp [carryB], hc.congr fun x => by simp [hA x, rcaV]⟩
  | a :: as, [], c, A, B, C, gs, _, hb, hc => by
    have hB : ∀ x, B x = [] := fun x => by rw [← hb.2 x]; rfl
    exact ⟨List.prefix_refl _, by simp [carryB], hc.congr fun x => by
      cases A x <;> simp [hB x, rcaV]⟩
  | a :: as, b :: bs, c, A, B, C, gs, ha, hb, hc => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    obtain ⟨hb₀, hbs, hB⟩ := hb.uncons
    have p₁ := isPrefix_emit BoolOp.and a b gs
    have h₁ := den_emit BoolOp.and ha₀ hb₀
    have p₂ := isPrefix_emit BoolOp.or a b (emit .and a b gs).1
    have h₂ := den_emit BoolOp.or (ha₀.mono p₁) (hb₀.mono p₁)
    have p₃ := isPrefix_emit BoolOp.and c (emit .or a b (emit .and a b gs).1).2
      (emit .or a b (emit .and a b gs).1).1
    have h₃ := den_emit BoolOp.and ((hc.mono p₁).mono p₂) h₂
    have p₄ := isPrefix_emit BoolOp.or (emit .and a b gs).2
      (emit .and c (emit .or a b (emit .and a b gs).1).2 (emit .or a b (emit .and a b gs).1).1).2
      (emit .and c (emit .or a b (emit .and a b gs).1).2 (emit .or a b (emit .and a b gs).1).1).1
    have h₄ := den_emit BoolOp.or ((h₁.mono p₂).mono p₃) h₃
    have hp := ((p₁.trans p₂).trans p₃).trans p₄
    obtain ⟨hq, hlen, hden⟩ := carryB_spec (has.mono hp) (hbs.mono hp) h₄
    refine ⟨hp.trans hq, ?_, hden.congr fun x => ?_⟩
    · simp only [carryB, hlen, length_emit, List.length_cons, Nat.add_min_add_right]; ring
    · conv_rhs => rw [hA x, hB x]
      simp only [rcaV, boolInterp]
      congr 1
      cases (A x).headD false <;> cases (B x).headD false <;> cases C x <;> rfl

/-! ### Numbers -/

/-- `w` operands carrying a natural number in binary, least significant bit first. -/
def numR (w : ℕ) : Rep BoolOp Bool n (List (Arg n)) ℕ :=
  ⟨fun gs as N => as.length = w ∧
      ∃ A : (Fin n → Bool) → List Bool, DenL boolInterp gs as A ∧ ∀ x, bitsVal (A x) = N x,
    fun hp ⟨hl, A, hA, hv⟩ => ⟨hl, A, hA.mono hp, hv⟩⟩

/-- The bits of a carried number: `w` of them at every input. -/
theorem numR_bits {w : ℕ} {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {N : (Fin n → Bool) → ℕ} (h : (numR w).rep gs as N) :
    ∃ A : (Fin n → Bool) → List Bool, DenL boolInterp gs as A ∧ (∀ x, (A x).length = w) ∧
      ∀ x, bitsVal (A x) = N x := by
  obtain ⟨hl, A, hA, hv⟩ := h
  exact ⟨A, hA, fun x => by rw [hA.length_eq x, hl], hv⟩

/-- A number carried on `w` bits is below `2 ^ w`. -/
theorem numR_lt {w : ℕ} {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {N : (Fin n → Bool) → ℕ} (h : (numR w).rep gs as N) (x : Fin n → Bool) : N x < 2 ^ w := by
  obtain ⟨A, -, hl, hv⟩ := numR_bits h
  rw [← hv x, ← hl x]
  exact bitsVal_lt _

/-- `L` bits, read as a number: free. -/
theorem numOfBits_impl (L : ℕ) :
    Impl (bitsR L) (numR (n := n) L) (pureB fun as => as) 0 bitsVal :=
  Impl.free fun _ _ A h => ⟨h.1, A, h.2, fun _ => rfl⟩

/-- One bit, read as a number below `2`: free. -/
theorem numOfBit_impl : Impl bitR (numR (n := n) 1) (pureB fun a => [a]) 0 Bool.toNat :=
  Impl.free fun gs _ _ h => ⟨rfl, _, DenL.cons h (denL_nil gs), fun x => by simp⟩

/-- Widening to `W ≥ w` bits by padding with `false` keeps the value. -/
theorem numR_fit {w W : ℕ} (hw : w ≤ W) {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {N : (Fin n → Bool) → ℕ} (h : (numR w).rep gs as N) : (numR W).rep gs (fit W as) N := by
  obtain ⟨hl, A, hA, hv⟩ := h
  refine ⟨length_fit W as, fun x => A x ++ List.replicate (W - w) false, ?_,
    fun x => by rw [bitsVal_append_false, hv]⟩
  rw [fit_eq_append (hl ▸ hw), hl]
  exact hA.append (denL_replicate_const gs _)

/-- Two carried numbers, both padded to the larger width `W`: bit lists of length `W`. -/
theorem numR_pad₂ {w₁ w₂ : ℕ} {gs : List (Gate BoolOp n)} {as bs : List (Arg n)}
    {N₁ N₂ : (Fin n → Bool) → ℕ} (h₁ : (numR w₁).rep gs as N₁) (h₂ : (numR w₂).rep gs bs N₂) :
    ∃ A B : (Fin n → Bool) → List Bool,
      DenL boolInterp gs (fit (max as.length bs.length) as) A ∧
      DenL boolInterp gs (fit (max as.length bs.length) bs) B ∧
      (∀ x, (A x).length = max as.length bs.length) ∧
      (∀ x, (B x).length = max as.length bs.length) ∧
      (∀ x, bitsVal (A x) = N₁ x) ∧ ∀ x, bitsVal (B x) = N₂ x := by
  obtain ⟨A, hA, hAl, hvA⟩ := numR_bits (numR_fit (W := max as.length bs.length)
    (by rw [← h₁.1]; exact le_max_left _ _) h₁)
  obtain ⟨B, hB, hBl, hvB⟩ := numR_bits (numR_fit (W := max as.length bs.length)
    (by rw [← h₂.1]; exact le_max_right _ _) h₂)
  exact ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩

/-- **Widening** to `W ≥ w` bits: free. -/
theorem numWiden_impl {w W : ℕ} (hw : w ≤ W) :
    Impl (numR w) (numR (n := n) W) (pureB (fit W)) 0 (fun N => N) :=
  Impl.free fun _ _ _ h => numR_fit hw h

/-- **Truncation** to the low `W ≤ w` bits, the value modulo `2 ^ W`: free. -/
theorem numTrunc_impl {w W : ℕ} (hW : W ≤ w) :
    Impl (numR w) (numR (n := n) W) (pureB (List.take W)) 0 (fun N => N % 2 ^ W) :=
  Impl.free fun _ _ _ ⟨hl, A, hA, hv⟩ =>
    ⟨by simp [hl, hW], _, denL_take hA W, fun x => by rw [bitsVal_take, hv]⟩

/-- **Fitting** to `W` bits, padding with `false` or cutting: the value modulo `2 ^ W`, free. -/
theorem numFit_impl {w W : ℕ} :
    Impl (numR w) (numR (n := n) W) (pureB (fit W)) 0 (fun N => N % 2 ^ W) := by
  intro gs as N h
  refine ⟨List.prefix_refl _, rfl, ?_⟩
  show (numR W).rep gs (fit W as) _
  rcases le_total w W with hw | hW
  · exact Rep.congr _ (numR_fit hw h) fun x => (Nat.mod_eq_of_lt ((numR_lt h x).trans_le
      (Nat.pow_le_pow_right two_pos hw))).symm
  · rw [fit, List.take_append_of_le_length (by rw [h.1]; exact hW)]
    exact (numTrunc_impl hW h).2.2

/-- **The constant** `c` on `w` bits, that is `c mod 2^w`: one gate, for the constant `true`. -/
def numConstB (c w : ℕ) : Bld BoolOp n (List (Arg n)) := fun gs =>
  let t := emit .not .const .const gs
  (t.1, (List.range w).map fun i => if c.testBit i then t.2 else .const)

/-- **The constant** `c` on `w` bits, `c mod 2 ^ w`: one gate. -/
theorem numConstB_impl (c w : ℕ) (R : Rep BoolOp Bool n σ τ) :
    Impl R (numR w) (fun _ => numConstB c w) 1 (fun _ => c % 2 ^ w) := by
  intro gs _ _ _
  have ht := den_emit (I := boolInterp) BoolOp.not (den_const gs) (den_const gs)
  refine ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, by simp [numConstB],
    fun _ => (List.range w).map c.testBit, ?_, fun x => bitsVal_testBit c w⟩
  refine (DenL.map (g := fun i => if c.testBit i then (emit .not .const .const gs).2 else .const)
    (G := fun i _ => c.testBit i) (List.range w) fun i _ => ?_).congr fun x => rfl
  by_cases hi : c.testBit i
  · simp only [hi, if_true]; exact ht.congr fun x => rfl
  · simp only [hi, Bool.false_eq_true, if_false]
    exact (den_const _).congr fun x => rfl

/-- **Addition**: both numbers padded to `W = max w₁ w₂` bits, a ripple-carry adder (`rcaB`,
eleven gates per bit), and the `W` sum bits followed by the carry. -/
def numAddB (p : List (Arg n) × List (Arg n)) : Bld BoolOp n (List (Arg n)) := fun gs =>
  let W := max p.1.length p.2.length
  let q := rcaB (fit W p.1) (fit W p.2) .const gs
  (q.1, q.2.1 ++ [q.2.2])

/-- **Addition** (`thm:D`, Step 2): `a + b` on `W + 1` bits, `11 W` gates. -/
theorem numAddB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (numR (n := n) (max w₁ w₂ + 1)) numAddB (11 * max w₁ w₂)
      (fun P => P.1 + P.2) := by
  intro gs p P ⟨h₁, h₂⟩
  obtain ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩ := numR_pad₂ h₁ h₂
  rw [← h₁.1, ← h₂.1]
  have h0 : Den boolInterp gs (.const : Arg n) (fun _ => false) := den_const gs
  obtain ⟨hp, hlen, hs, hc⟩ := rcaB_spec hA hB h0
  have hS : ∀ x, (rcaV (A x) (B x) false).1.length = max p.1.length p.2.length := fun x => by
    rw [length_rcaV, hAl, hBl, min_self]
  have hout := hs.append (DenL.cons hc (denL_nil _))
  refine ⟨hp, hlen.trans (by rw [length_fit, length_fit, min_self]),
    (hout.length_eq fun _ => false).symm.trans (by simp [hS]), _, hout, fun x => ?_⟩
  have h := bitsVal_rcaV (A x) (B x) false (by rw [hAl, hBl])
  rw [hAl] at h
  rw [bitsVal_append, hS, bitsVal_cons, bitsVal_nil, mul_zero, add_zero, h, hvA, hvB,
    Bool.toNat_false, add_zero]

/-- **Truncated subtraction** `a - b` (`0` when `b > a`): `a + ¬b + 1` on `W = max w₁ w₂` bits,
whose carry is `[b ≤ a]`, and the low `w₁` sum bits, each in conjunction with the carry:
`12 W + w₁ + 1` gates. -/
def numSubB (p : List (Arg n) × List (Arg n)) : Bld BoolOp n (List (Arg n)) := fun gs =>
  let W := max p.1.length p.2.length
  let q₁ := notsB (fit W p.2) gs
  let q₂ := emit .not .const .const q₁.1
  let q₃ := rcaB (fit W p.1) q₁.2 q₂.2 q₂.1
  andEachB q₃.2.2 (q₃.2.1.take p.1.length) q₃.1

/-- **Truncated subtraction** (`lem:observer`, Step 3; `thm:D`, Step 2): `a - b`, which is
`0` when `b > a`, on `w₁` bits, `12 W + w₁ + 1` gates. -/
theorem numSubB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (numR (n := n) w₁) numSubB (12 * max w₁ w₂ + w₁ + 1)
      (fun P => P.1 - P.2) := by
  intro gs p P ⟨h₁, h₂⟩
  obtain ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩ := numR_pad₂ h₁ h₂
  have hlt := numR_lt h₁
  rw [← h₁.1, ← h₂.1]
  rw [← h₁.1] at hlt
  set W := max p.1.length p.2.length with hW
  obtain ⟨p₁, l₁, hn⟩ := notsB_spec hB
  have p₂ := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const (notsB (fit W p.2) gs).1
  have h₂ : Den boolInterp (emit BoolOp.not .const .const (notsB (fit W p.2) gs).1).1
      (emit BoolOp.not .const .const (notsB (fit W p.2) gs).1).2 (fun _ => true) :=
    den_emit BoolOp.not (den_const _) (den_const _)
  obtain ⟨p₃, l₃, hs, hc⟩ := rcaB_spec ((hA.mono p₁).mono p₂) (hn.mono p₂) h₂
  obtain ⟨p₄, l₄, hd⟩ := andEachB_spec (denL_take hs p.1.length) hc
  have hSl : ∀ x, (rcaV (A x) ((B x).map (!·)) true).1.length = W := fun x => by
    rw [length_rcaV, List.length_map, hAl, hBl, min_self]
  have hwW : p.1.length ≤ W := le_max_left _ _
  refine ⟨((p₁.trans p₂).trans p₃).trans p₄, l₄.trans ?_,
    (hd.length_eq fun _ => false).symm.trans ?_, _, hd, fun x => ?_⟩
  · rw [List.length_take, ← hs.length_eq fun _ => false, hSl, min_eq_left hwW, l₃, length_emit,
      l₁, notsB_length₂, length_fit, length_fit, min_self]
    ring
  · rw [List.length_map, List.length_take, hSl, min_eq_left hwW]
  · obtain ⟨hcar, hsub⟩ := rcaV_not_carry (xs := A x) (bs := B x) (by rw [hAl, hBl])
    beta_reduce
    rw [bitsVal_map_and, hcar, bitsVal_take, hvA, hvB]
    by_cases hle : (P x).2 ≤ (P x).1
    · rw [decide_eq_true hle, if_pos rfl, ← hvA, ← hvB, hsub (by rwa [hvA, hvB]), hvA, hvB]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (hlt x))
    · rw [decide_eq_false hle, if_neg Bool.false_ne_true]
      omega

/-- **Comparison** `[a ≤ b]`: the carry of `b + ¬a + 1` on `W = max w₁ w₂` bits, `5 W + 1`
gates. -/
def numLeB (p : List (Arg n) × List (Arg n)) : Bld BoolOp n (Arg n) := fun gs =>
  let W := max p.1.length p.2.length
  let q₁ := notsB (fit W p.1) gs
  let q₂ := emit .not .const .const q₁.1
  carryB (fit W p.2) q₁.2 q₂.2 q₂.1

/-- **Comparison** (`lem:observer`, Steps 1 and 4; `thm:D`, Step 4): `[a ≤ b]`, `5 W + 1`
gates. -/
theorem numLeB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (bitR (n := n)) numLeB (5 * max w₁ w₂ + 1)
      (fun P => decide (P.1 ≤ P.2)) := by
  intro gs p P ⟨h₁, h₂⟩
  obtain ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩ := numR_pad₂ h₁ h₂
  rw [← h₁.1, ← h₂.1]
  set W := max p.1.length p.2.length with hW
  obtain ⟨p₁, l₁, hn⟩ := notsB_spec hA
  have p₂ := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const (notsB (fit W p.1) gs).1
  have h₂ : Den boolInterp (emit BoolOp.not .const .const (notsB (fit W p.1) gs).1).1
      (emit BoolOp.not .const .const (notsB (fit W p.1) gs).1).2 (fun _ => true) :=
    den_emit BoolOp.not (den_const _) (den_const _)
  obtain ⟨p₃, l₃, hc⟩ := carryB_spec ((hB.mono p₁).mono p₂) (hn.mono p₂) h₂
  refine ⟨(p₁.trans p₂).trans p₃, l₃.trans ?_, hc.congr fun x => ?_⟩
  · rw [length_emit, l₁, notsB_length₂, length_fit, length_fit, min_self]; ring
  · rw [(rcaV_not_carry (xs := B x) (bs := A x) (by rw [hAl, hBl])).1, hvA, hvB]

/-- **Strict comparison** `[a < b] = ¬[b ≤ a]`, `5 W + 2` gates. -/
def numLtB : List (Arg n) × List (Arg n) → Bld BoolOp n (Arg n) :=
  seqB (fun p => numLeB (p.2, p.1)) fun a => emit .not a .const

/-- **Strict comparison** `[a < b]`, `5 W + 2` gates. -/
theorem numLtB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (bitR (n := n)) numLtB (5 * max w₁ w₂ + 2)
      (fun P => decide (P.1 < P.2)) :=
  (((numLeB_impl w₂ w₁).pre (R := (numR w₁).prod (numR w₂))
    (g := fun p : List (Arg n) × List (Arg n) => (p.2, p.1)) (G := fun P : ℕ × ℕ => (P.2, P.1))
    fun _ _ _ hs => ⟨hs.2, hs.1⟩).comp emitNot_impl).cost (by rw [max_comm]) |>.congr
    fun P => by simp only [← decide_not, not_le]

/-- **Equality** `[a = b]`: no bit of `a ⊕ b` is set; `5 W + 1` gates. -/
def numEqB (p : List (Arg n) × List (Arg n)) : Bld BoolOp n (Arg n) := fun gs =>
  let W := max p.1.length p.2.length
  let q₁ := xorsB (fit W p.1) (fit W p.2) gs
  let q₂ := orB q₁.2 q₁.1
  emit .not q₂.2 .const q₂.1

/-- **Equality** (`lem:observer`, Step 1): `[a = b]`, `5 W + 1` gates. -/
theorem numEqB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (bitR (n := n)) numEqB (5 * max w₁ w₂ + 1)
      (fun P => decide (P.1 = P.2)) := by
  intro gs p P ⟨h₁, h₂⟩
  obtain ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩ := numR_pad₂ h₁ h₂
  rw [← h₁.1, ← h₂.1]
  obtain ⟨p₁, l₁, hx⟩ := xorsB_spec hA hB
  obtain ⟨p₂, l₂, ho⟩ := orB_spec hx
  have hn := den_emit BoolOp.not ho (den_const _)
  refine ⟨(p₁.trans p₂).trans (isPrefix_emit _ _ _ _), ?_, hn.congr fun x => ?_⟩
  · refine (length_emit _ _ _ _).trans ?_
    rw [l₂, l₁, ← hx.length_eq fun _ => false, List.length_zipWith, hAl, hBl, length_fit,
      length_fit, min_self]
    ring
  · show (!(List.zipWith (· ^^ ·) (A x) (B x)).any id) = decide ((P x).1 = (P x).2)
    rw [any_zipWith_xor (by rw [hAl, hBl]), Bool.not_not, ← hvA, ← hvB]
    exact decide_eq_decide.2 ⟨congrArg bitsVal, eq_of_bitsVal_eq (by rw [hAl, hBl])⟩

/-- **Selection** `if s then a else b`, both padded to `W = max w₁ w₂` bits: `3 W + 1`
gates (`selB` of `Converse.lean`). -/
def numMuxB (p : Arg n × List (Arg n) × List (Arg n)) : Bld BoolOp n (List (Arg n)) := fun gs =>
  let W := max p.2.1.length p.2.2.length
  let t := emit .not p.1 .const gs
  selB p.1 t.2 (fit W p.2.2) (fit W p.2.1) t.1

/-- **Selection** (`thm:D`, Step 4): `if s then a else b` on `W` bits, `3 W + 1` gates. -/
theorem numMuxB_impl (w₁ w₂ : ℕ) :
    Impl (bitR.prod ((numR w₁).prod (numR w₂))) (numR (n := n) (max w₁ w₂)) numMuxB
      (3 * max w₁ w₂ + 1) (fun P => if P.1 then P.2.1 else P.2.2) := by
  intro gs p P ⟨hs, h₁, h₂⟩
  obtain ⟨A, B, hA, hB, hAl, hBl, hvA, hvB⟩ := numR_pad₂ h₁ h₂
  rw [← h₁.1, ← h₂.1]
  have pt := isPrefix_emit BoolOp.not p.1 .const gs
  have ht : Den boolInterp (emit BoolOp.not p.1 .const gs).1 (emit BoolOp.not p.1 .const gs).2
      (fun x => !(P x).1) := den_emit BoolOp.not hs (den_const gs)
  obtain ⟨p₁, l₁, hd⟩ := selB_spec (hs.mono pt) ht (hB.mono pt) (hA.mono pt)
  refine ⟨pt.trans p₁, l₁.trans ?_, (hd.length_eq fun _ => false).symm.trans ?_, _, hd,
    fun x => ?_⟩
  · rw [length_emit, length_fit, length_fit, min_self]; ring
  · rw [List.length_zipWith, hAl, hBl, min_self]
  · rw [bitsVal_zipWith_sel _ _ _ (by rw [hAl, hBl]), hvA, hvB]

/-- **Masking** `if s then a else 0`: each bit in conjunction with `s`, `w` gates. -/
def numMaskB (p : Arg n × List (Arg n)) : Bld BoolOp n (List (Arg n)) := andEachB p.1 p.2

/-- **Masking** `if s then a else 0`, `w` gates. -/
theorem numMaskB_impl (w : ℕ) :
    Impl (bitR.prod (numR w)) (numR (n := n) w) numMaskB w
      (fun P => if P.1 then P.2 else 0) := by
  intro gs p P ⟨hs, hl, A, hA, hv⟩
  obtain ⟨p₁, l₁, hd⟩ := andEachB_spec hA hs
  refine ⟨p₁, l₁.trans (by rw [hl]), (hd.length_eq fun _ => false).symm.trans ?_, _, hd,
    fun x => ?_⟩
  · rw [List.length_map, hA.length_eq, hl]
  · rw [bitsVal_map_and, hv]

/-- **Minimum** `min a b`: a comparison and a selection, `8 W + 2` gates. -/
def numMinB : List (Arg n) × List (Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB numLeB (pureB fun p => p)) numMuxB

/-- **Minimum** `min a b` on `W` bits, `8 W + 2` gates. -/
theorem numMinB_impl (w₁ w₂ : ℕ) :
    Impl ((numR w₁).prod (numR w₂)) (numR (n := n) (max w₁ w₂)) numMinB (8 * max w₁ w₂ + 2)
      (fun P => min P.1 P.2) :=
  (((numLeB_impl w₁ w₂).pair Impl.self).comp (numMuxB_impl w₁ w₂)).cost (by ring) |>.congr
    fun P => by by_cases h : P.1 ≤ P.2 <;> simp [h, min_def]

/-! ### Constants as second arguments -/

/-- `[a ≤ c]` for a constant `c`. -/
def numLeConstB (c : ℕ) : List (Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun as => as) fun _ => numConstB c (Nat.size c)) numLeB

/-- `[c ≤ a]` for a constant `c`. -/
def numGeConstB (c : ℕ) : List (Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (fun _ => numConstB c (Nat.size c)) (pureB fun as => as)) numLeB

/-- `[a = c]` for a constant `c`. -/
def numEqConstB (c : ℕ) : List (Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun as => as) fun _ => numConstB c (Nat.size c)) numEqB

/-- `a - c` truncated at `0`, for a constant `c`. -/
def numSubConstB (c : ℕ) : List (Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB (pureB fun as => as) fun _ => numConstB c (Nat.size c)) numSubB

/-- `min a c` for a constant `c`. -/
def numMinConstB (c : ℕ) : List (Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB (pureB fun as => as) fun _ => numConstB c (Nat.size c)) numMinB

/-- A constant on `⌈log₂(c+1)⌉` bits keeps its value. -/
theorem const_mod_size (c : ℕ) : c % 2 ^ Nat.size c = c := Nat.mod_eq_of_lt (Nat.lt_size_self c)

/-- **Comparison with a constant**, `[a ≤ c]`: `5 max(w, ⌈log₂(c+1)⌉) + 2` gates. -/
theorem numLeConstB_impl (c w : ℕ) :
    Impl (numR w) (bitR (n := n)) (numLeConstB c) (5 * max w (Nat.size c) + 2)
      (fun a => decide (a ≤ c)) :=
  ((Impl.self.pair (numConstB_impl c (Nat.size c) (numR w))).comp
    (numLeB_impl w (Nat.size c))).cost (by ring) |>.congr fun a => by rw [const_mod_size]

/-- **Comparison with a constant**, `[c ≤ a]`: `5 max(w, ⌈log₂(c+1)⌉) + 2` gates. -/
theorem numGeConstB_impl (c w : ℕ) :
    Impl (numR w) (bitR (n := n)) (numGeConstB c) (5 * max (Nat.size c) w + 2)
      (fun a => decide (c ≤ a)) :=
  (((numConstB_impl c (Nat.size c) (numR w)).pair Impl.self).comp
    (numLeB_impl (Nat.size c) w)).cost (by ring) |>.congr fun a => by rw [const_mod_size]

/-- **Equality with a constant**, `[a = c]`: `5 max(w, ⌈log₂(c+1)⌉) + 2` gates. -/
theorem numEqConstB_impl (c w : ℕ) :
    Impl (numR w) (bitR (n := n)) (numEqConstB c) (5 * max w (Nat.size c) + 2)
      (fun a => decide (a = c)) :=
  ((Impl.self.pair (numConstB_impl c (Nat.size c) (numR w))).comp
    (numEqB_impl w (Nat.size c))).cost (by ring) |>.congr fun a => by rw [const_mod_size]

/-- **Subtraction of a constant**, `a - c` truncated at `0`, on the width `w` of `a`:
`12 max(w, ⌈log₂(c+1)⌉) + w + 2` gates. -/
theorem numSubConstB_impl (c w : ℕ) :
    Impl (numR w) (numR (n := n) w) (numSubConstB c) (12 * max w (Nat.size c) + w + 2)
      (fun a => a - c) :=
  ((Impl.self.pair (numConstB_impl c (Nat.size c) (numR w))).comp
    (numSubB_impl w (Nat.size c))).cost (by ring) |>.congr fun a => by rw [const_mod_size]

/-- **Minimum with a constant**, `min a c`: `8 max(w, ⌈log₂(c+1)⌉) + 3` gates. -/
theorem numMinConstB_impl (c w : ℕ) :
    Impl (numR w) (numR (n := n) (max w (Nat.size c))) (numMinConstB c)
      (8 * max w (Nat.size c) + 3) (fun a => min a c) :=
  ((Impl.self.pair (numConstB_impl c (Nat.size c) (numR w))).comp
    (numMinB_impl w (Nat.size c))).cost (by ring) |>.congr fun a => by rw [const_mod_size]

end SignedTropical.BoolAlg
