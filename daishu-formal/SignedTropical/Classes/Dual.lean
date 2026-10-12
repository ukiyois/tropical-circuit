import SignedTropical.Binary

/-!
# Duality

`greedy_intersection.tex`, Corollary `cor:classes`, item 4, for duals of matroids with a
Boolean rank circuit; with `Graphic.lean` this covers cographic matroids.

Let `M` be a matroid on `E = Fin m` with ground set `univ`, rank function `r` and rank
`k = r(E)`, and let `M✶` be its dual (Mathlib's `Matroid.dual`).

* `rk_dual`: `r✶(S) + k = r(E \ S) + |S|`, from Mathlib's `Matroid.eRk_dual_add_eRank`.
* `dualRankCircuit B k`: from a Boolean circuit `B` that outputs `r(S)` in binary, a Boolean
  circuit that outputs `r✶(S)` in binary, with `W = ⌈log₂(m+1)⌉` output bits:
  1. the constant `1 = ¬0`, one gate;
  2. the negated inputs, `m` gates, and `B` on them, `s` gates, giving `r(E \ S)`;
  3. a `W`-bit counter that starts at `2^W - (k mod 2^W)` and adds every input bit
     (`countB` of `Binary.lean`), `11 W m` gates;
  4. a `W`-bit ripple-carry addition of the `W` low bits of `r(E \ S)`, `11 W` gates.
  All arithmetic is modulo `2^W`, and `0 ≤ r✶(S) ≤ |S| ≤ m < 2^W`, so the result is exact.
  It has exactly `s + m + 1 + 11 (m + 1) W` gates (`dualRankCircuit_size`).
* `dual_rankCircuit`, `theoremA_dual`: the Boolean rank circuit of `M✶`, and Theorem A
  applied to it.
-/

open Finset

namespace SignedTropical.Classes

variable {m : ℕ}

/-! ### The rank function of the dual -/

/-- **The rank function of the dual.**  `r✶(S) + r(E) = r(E \ S) + |S|`. -/
theorem rk_dual (M : Matroid (Fin m)) (hE : M.E = Set.univ) (S : Finset (Fin m)) :
    rk M✶ S + rank M = rk M (univ \ S) + S.card := by
  have h := M.eRk_dual_add_eRank (S : Set (Fin m)) (by simp [hE])
  rw [hE, ← coe_rk, ← ENat.coe_toNat (eRank_ne_top M), ← Finset.coe_univ, ← Finset.coe_sdiff,
    ← coe_rk, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-! ### Bits of numbers and of constants -/

theorem testBit_bitsVal : ∀ (l : List Bool) (j : ℕ), (bitsVal l).testBit j = l.getD j false
  | [], j => by simp
  | b :: l, 0 => by cases b <;> simp [Nat.testBit_zero]
  | b :: l, j + 1 => by
    rw [bitsVal_cons, Nat.testBit_succ,
      show (b.toNat + 2 * bitsVal l) / 2 = bitsVal l by
        cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega]
    exact testBit_bitsVal l j

/-- Padding with `0`s and keeping `W` bits gives the `W` low bits. -/
theorem take_append_replicate (W : ℕ) (l : List Bool) :
    (l ++ List.replicate W false).take W = bitsOf (BitVec.ofNat W (bitsVal l)) := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  have hj : j < W := by simpa using h₂
  simp only [List.getElem_take, bitsOf, List.getElem_map, List.getElem_range,
    BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and, testBit_bitsVal]
  by_cases hjl : j < l.length
  · rw [List.getElem_append_left hjl, List.getD_eq_getElem _ _ hjl]
  · rw [List.getElem_append_right (by omega), List.getElem_replicate,
      List.getD_eq_default _ _ (by omega)]

/-- Padded or cut to `W` operands, a list of operands carries the `W` low bits of its
value. -/
theorem bitRep_fit {gs : List (Gate BoolOp m)} {as : List (Arg m)}
    {A : (Fin m → Bool) → List Bool} (h : DenL boolInterp gs as A) (W : ℕ) :
    BitRep W gs (fit W as) (fun x => BitVec.ofNat W (bitsVal (A x))) := by
  refine ⟨fun a ha => ?_, fun x => ?_⟩
  · rcases List.mem_append.1 (List.mem_of_mem_take ha) with ha | ha
    · exact h.1 a ha
    · rw [List.eq_of_mem_replicate ha]; trivial
  · show _ = bitsOf (BitVec.ofNat W (bitsVal (A x)))
    rw [← take_append_replicate, ← h.2 x]
    simp [fit, List.map_take, Arg.read, boolInterp]

/-- The `W` bits of the constant `c`, read from the constant source and a wire `t`
carrying `1`. -/
def constBits (t : Arg m) (W c : ℕ) : List (Arg m) :=
  (List.range W).map fun j => if c.testBit j then t else .const

theorem bitRep_constBits {gs : List (Gate BoolOp m)} {t : Arg m}
    (ht : Den boolInterp gs t fun _ => true) (W c : ℕ) :
    BitRep W gs (constBits t W c) (fun _ => BitVec.ofNat W c) := by
  refine ⟨fun a ha => ?_, fun x => ?_⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    split_ifs
    exacts [ht.1, trivial]
  · simp only [constBits, bitsOf, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply, BitVec.getLsbD_ofNat, List.mem_range.1 hj, decide_true,
      Bool.true_and]
    split_ifs with h
    · rw [ht.2 x, h]
    · simp [Arg.read, boolInterp, h]

/-! ### The rank circuit of the dual -/

/-- **The rank circuit of the dual**, for a Boolean circuit `B` that outputs `r(S)` in binary
and the rank `k = r(E)`. -/
def dualRankCircuit (B : Circuit BoolOp m) (k : ℕ) : Circuit BoolOp m :=
  let W := Nat.size m
  let p₀ := emit BoolOp.not (Arg.const : Arg m) .const []
  let p₁ := mapB (fun i : Fin m => emit BoolOp.not (.input i) .const) (List.finRange m) p₀.1
  let p₂ := inline (fun o a b => emit o a b) (fun i => p₁.2.getD i .const) .const B p₁.1
  let p₃ := countB W (fun e : Fin m => .input e) (List.finRange m)
    (constBits p₀.2 W (2 ^ W - k % 2 ^ W)) p₂.1
  let p₄ := rcaB p₃.2 (fit W p₂.2) .const p₃.1
  ⟨p₄.1, p₄.2.1⟩

theorem ofNat_add_ofNat_add_false (W a b : ℕ) :
    BitVec.ofNat W a + BitVec.ofNat W b + BitVec.setWidth W (BitVec.ofBool false)
      = BitVec.ofNat W (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

/-- The size of the dual rank circuit, and what it computes: the `W = ⌈log₂(m+1)⌉` low bits
of `2^W - (k mod 2^W) + |{e : x_e}| + B(¬x)`. -/
theorem dualRankCircuit_spec (B : Circuit BoolOp m) (k : ℕ) :
    (dualRankCircuit B k).size = B.size + m + 1 + 11 * (m + 1) * Nat.size m ∧
      ∀ x : Fin m → Bool, (dualRankCircuit B k).eval boolInterp x
        = bitsOf (BitVec.ofNat (Nat.size m) (2 ^ Nat.size m - k % 2 ^ Nat.size m
          + ((List.finRange m).filter x).length + bitsVal (B.eval boolInterp fun i => !x i))) := by
  set W := Nat.size m
  set p₀ := emit BoolOp.not (Arg.const : Arg m) .const []
  have h₀ : Den boolInterp p₀.1 p₀.2 fun _ => true :=
    (den_emit BoolOp.not (den_const []) (den_const [])).congr fun _ => rfl
  obtain ⟨hp₁, hlen₁, hden₁⟩ := mapB_spec (I := boolInterp) (c := 1) (gs₀ := p₀.1)
    (b := fun i : Fin m => emit BoolOp.not (.input i) .const) (F := fun i x => !x i)
    (fun i gs _ => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
      den_emit BoolOp.not (den_input gs i) (den_const gs)⟩) (List.finRange m) p₀.1
    (List.prefix_refl _)
  set p₁ := mapB (fun i : Fin m => emit BoolOp.not (.input i) .const) (List.finRange m) p₀.1
  have hinp : ∀ i : Fin m, Den boolInterp p₁.1 (p₁.2.getD i .const) (fun x => !x i) := fun i =>
    (hden₁.getD i).congr fun x => by rw [List.getD_eq_getElem _ _ (by simp)]; simp
  obtain ⟨hp₂, h₂⟩ := inline_spec (R := Den boolInterp) (J := fun _ => boolInterp)
    (φ := fun i x => !x i) (gad := fun o a b => emit o a b)
    (inp := fun i => p₁.2.getD i .const) (c := .const)
    (fun _ _ _ _ hp h => h.mono hp) (den_const _) hinp
    (fun o _ _ _ _ gs _ h₁ h₂ => ⟨isPrefix_emit _ _ _ _, den_emit o h₁ h₂⟩) B
  set p₂ := inline (fun o a b => emit o a b) (fun i => p₁.2.getD i .const) .const B p₁.1
  have hden₂ : DenL boolInterp p₂.1 p₂.2 (fun x => B.eval boolInterp fun i => !x i) :=
    (DenL.of_forall₂ h₂).congr fun x => by simp only [List.map_map]; rfl
  obtain ⟨hp₃, hlen₃, hden₃⟩ := countB_spec W (Fv := fun x e => x e) (List.finRange m)
    (fun e => den_input p₂.1 e) (bitRep_constBits (h₀.mono (hp₁.trans hp₂)) W
      (2 ^ W - k % 2 ^ W))
  set p₃ := countB W (fun e : Fin m => .input e) (List.finRange m)
    (constBits p₀.2 W (2 ^ W - k % 2 ^ W)) p₂.1
  obtain ⟨-, hlen₄, hden₄, -⟩ := rcaB_spec hden₃ ((bitRep_fit hden₂ W).mono hp₃)
    (den_const (I := boolInterp) p₃.1)
  refine ⟨?_, fun x => ?_⟩
  · have hW₃ : p₃.2.length = W := by rw [← hden₃.length_eq (fun _ => false), length_bitsOf]
    show (rcaB p₃.2 (fit W p₂.2) .const p₃.1).1.length = _
    rw [hlen₄, hW₃, length_fit, min_self, hlen₃, length_inline (fun _ => 1)
      (fun o a b gs => length_emit o a b gs) B p₁.1, hlen₁, show p₀.1.length = 1 from rfl]
    simp only [List.length_finRange, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
      Circuit.size]
    ring
  · exact (hden₄.2 x).trans (by
      simp only [boolInterp, rcaV_bitsOf, ofNat_add_ofNat_add_false])

theorem dualRankCircuit_size (B : Circuit BoolOp m) (k : ℕ) :
    (dualRankCircuit B k).size = B.size + m + 1 + 11 * (m + 1) * Nat.size m :=
  (dualRankCircuit_spec B k).1

/-- **The rank circuit of the dual computes the rank function of the dual.** -/
theorem dualRankCircuit_rank (M : Matroid (Fin m)) (hE : M.E = Set.univ) {B : Circuit BoolOp m}
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (S : Finset (Fin m)) :
    (bitsVal ((dualRankCircuit B (rank M)).eval boolInterp (indicator S)) : ℕ∞)
      = M✶.eRk (S : Set (Fin m)) := by
  set W := Nat.size m
  set k := rank M
  rw [(dualRankCircuit_spec B k).2, bitsVal_bitsOf, BitVec.toNat_ofNat, ← coe_rk]
  congr 1
  have hcomp : (fun i => !indicator S i) = indicator (univ \ S) := by
    funext i; simp [indicator]
  have hrk : bitsVal (B.eval boolInterp (indicator (univ \ S))) = rk M (univ \ S) := by
    have := hB (univ \ S); rw [← coe_rk] at this; exact_mod_cast this
  have hcard : ((List.finRange m).filter (indicator S)).length = S.card := by
    rw [filter_finRange_length]; congr 1; ext e; simp [indicator]
  rw [hcomp, hrk, hcard]
  have hd := rk_dual M hE S
  have hle : rk M✶ S ≤ S.card := by
    have := M✶.eRk_le_encard (S : Set (Fin m))
    rw [← coe_rk, Set.encard_coe_eq_coe_finsetCard] at this; exact_mod_cast this
  have hlt : rk M✶ S < 2 ^ W :=
    (hle.trans (by simpa using S.card_le_univ)).trans_lt (Nat.lt_size_self m)
  have key : 2 ^ W - k % 2 ^ W + S.card + rk M (univ \ S)
      = rk M✶ S + 2 ^ W * (1 + k / 2 ^ W) := by
    have h₁ := Nat.div_add_mod k (2 ^ W)
    have h₂ : k % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by positivity)
    rw [mul_add, mul_one]
    generalize 2 ^ W * (k / 2 ^ W) = R at h₁ ⊢
    generalize k % 2 ^ W = c at h₁ h₂ ⊢
    generalize 2 ^ W = P at h₁ h₂ ⊢
    omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **Duality, Boolean rank circuits.**  Let `M` be a matroid on `Fin m` with ground set
`univ`.  If a Boolean circuit of size `s` outputs `r(S)` in binary from the indicator vector
of `S`, then a Boolean circuit of size `s + m + 1 + 11 (m + 1) ⌈log₂(m+1)⌉` outputs, in
binary, the rank of `S` in the dual matroid `M✶`. -/
theorem dual_rankCircuit (M : Matroid (Fin m)) (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ B' : Circuit BoolOp m, B'.size = B.size + m + 1 + 11 * (m + 1) * Nat.size m ∧
      ∀ S : Finset (Fin m),
        (bitsVal (B'.eval boolInterp (indicator S)) : ℕ∞) = M✶.eRk (S : Set (Fin m)) :=
  ⟨dualRankCircuit B (rank M), dualRankCircuit_size B _, dualRankCircuit_rank M hE hB⟩

/-- **Duality, signed tropical circuits** (Theorem A for `M✶`).  Under the hypotheses of
`dual_rankCircuit`, `h_{M✶}(w) = max_{B ∈ Bases(M✶)} w(B)` is computed at every
`w ∈ ℝ^m` by a signed tropical circuit of size at most
`3 m s' + m L + 9 m² + 4 m + 4 L + 1`, where `s' = s + m + 1 + 11 (m + 1) ⌈log₂(m+1)⌉` and
`L = ⌈log₂(k✶+1)⌉` for the rank `k✶` of `M✶`. -/
theorem theoremA_dual (M : Matroid (Fin m)) (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3 * m * (B.size + m + 1 + 11 * (m + 1) * Nat.size m)
          + m * Nat.size (rank M✶) + 9 * m ^ 2 + 4 * m + 4 * Nat.size (rank M✶) + 1 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight M✶ w] := by
  have h := theoremA M✶ (by rw [Matroid.dual_ground, hE]) (dualRankCircuit B (rank M))
    (dualRankCircuit_rank M hE hB)
  rwa [dualRankCircuit_size] at h

end SignedTropical.Classes
