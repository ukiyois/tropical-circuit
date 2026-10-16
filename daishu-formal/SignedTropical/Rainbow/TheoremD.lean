import SignedTropical.Rainbow.TheoremDRank
import SignedTropical.Rainbow.TheoremCFinal

/-!
# Theorem D: matroid intersection

`greedy_intersection.tex`, Theorem `thm:D` and its proof (Section 5).  `M₁`, `M₂` are matroids
on `E = Fin m` with ground set `E`, and the Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂`
output the binary digits of their rank functions (the hypothesis of Theorem A).

* The values: `commonBaseWeights` and `minCommonBaseWeight` (`isLeast_minCommonBaseWeight`:
  with a common base, the least weight of a common base); `commonIndepWeights` and
  `maxCommonIndepWeight` (`isGreatest_maxCommonIndepWeight`: the greatest weight of a common
  independent set).
* `weightCircuit`: a signed tropical circuit on `E × {1, 2}` read at `Doubling.weight w`, with
  no extra gate.
* Steps 1 and 3 (`exists_minCommonBase_circuit`): with a common base and a rank circuit `B` of
  `N = M₁ ⊕ M₂✶`, Theorem C (`TheoremCFinal.theoremC_final`) on `N` (`2m` elements, `m` blocks,
  rank `m`), read at `weight w`, computes the minimum weight of a common base
  (`Doubling.opt_eq`) with at most `3328 m³ (2m)⁴ (|B| + 2m) + 2` gates.
* **Part (1)** (`theoremD_commonBase`): with the rank circuit `doubleRankCircuit` of Step 2, at
  most `3328 m³ (2m)⁴ (s₁ + s₂ + 60m + 15) + 2 ≤ 3328 · 1200 m⁷ (s₁ + s₂ + m) + 2` gates.
* Step 4 (`minCommonBaseWeight_pad`): on `E × {1, 2}` the padded matroids
  `pad Mᵢ = (Mᵢ ⊕ U_{m,m})|_{≤m}` (`Rainbow/TheoremDRank.lean`) have the common bases
  `X × {1} ∪ Y × {2}`, `X` a common independent set of `M₁` and `M₂` and `|Y| = m - |X|`, among
  them `E × {2}` (`exists_commonBase_pad`); at `-w` on the first copies and `0` on the second,
  the least weight of a common base is minus the greatest weight of a common independent set.
* The circuit of Step 4 (`negNegCircuit`, `negNegCircuit_spec`): `u = -w` (`m` gates), the circuit
  of Steps 1 to 3 for the padded matroids, and the negation of its output.
* **Part (2)** (`theoremD_commonIndep`): with the rank circuits `padRankCircuit` of the padded
  matroids (`2m` elements), at most `3328 · 2048 m⁷ (s₁ + s₂ + 268m + 51) + m + 3 ≤
  3328 · 653313 m⁷ (s₁ + s₂ + m) + 3` gates.
* **Theorem `thm:D`** (`theoremD`): both parts, under the hypotheses of the paper.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremD

open SignedTropical.BoolAlg SignedTropical.Rainbow.Doubling SignedTropical.Rainbow.Trunc
  SignedTropical.Rainbow.TheoremC

variable {m n : ℕ}

/-! ### Common bases and common independent sets -/

section Weights

variable (M₁ M₂ : Matroid (Fin m)) (w : Fin m → ℝ)

/-- The weights `w(X)` of the common bases `X` of `M₁` and `M₂`. -/
def commonBaseWeights : Set ℝ :=
  {x | ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)) ∧
    x = ∑ e ∈ X, w e}

/-- The minimum weight of a common base of `M₁` and `M₂` (`isLeast_minCommonBaseWeight`). -/
noncomputable def minCommonBaseWeight : ℝ :=
  sInf (commonBaseWeights M₁ M₂ w)

/-- The weights `w(X)` of the common independent sets `X` of `M₁` and `M₂`. -/
def commonIndepWeights : Set ℝ :=
  {x | ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧
    x = ∑ e ∈ X, w e}

/-- The maximum weight of a common independent set of `M₁` and `M₂`
(`isGreatest_maxCommonIndepWeight`). -/
noncomputable def maxCommonIndepWeight : ℝ :=
  sSup (commonIndepWeights M₁ M₂ w)

/-- There are finitely many weights of common bases. -/
theorem commonBaseWeights_finite : (commonBaseWeights M₁ M₂ w).Finite := by
  refine ((Set.finite_univ (α := Finset (Fin m))).image fun X => ∑ e ∈ X, w e).subset ?_
  rintro x ⟨X, -, -, rfl⟩
  exact ⟨X, trivial, rfl⟩

/-- There are finitely many weights of common independent sets. -/
theorem commonIndepWeights_finite : (commonIndepWeights M₁ M₂ w).Finite := by
  refine ((Set.finite_univ (α := Finset (Fin m))).image fun X => ∑ e ∈ X, w e).subset ?_
  rintro x ⟨X, -, -, rfl⟩
  exact ⟨X, trivial, rfl⟩

/-- `maxCommonIndepWeight` is the greatest weight of a common independent set (the empty set is
one). -/
theorem isGreatest_maxCommonIndepWeight :
    IsGreatest (commonIndepWeights M₁ M₂ w) (maxCommonIndepWeight M₁ M₂ w) :=
  have hne : (commonIndepWeights M₁ M₂ w).Nonempty := ⟨0, ∅, by simp, by simp, by simp⟩
  ⟨hne.csSup_mem (commonIndepWeights_finite M₁ M₂ w),
    fun _ hx => le_csSup (commonIndepWeights_finite M₁ M₂ w).bddAbove hx⟩

end Weights

variable {M₁ M₂ : Matroid (Fin m)} {C₁ C₂ : Circuit BoolOp m}

/-- With a common base, `minCommonBaseWeight` is the least weight of a common base. -/
theorem isLeast_minCommonBaseWeight
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)))
    (w : Fin m → ℝ) : IsLeast (commonBaseWeights M₁ M₂ w) (minCommonBaseWeight M₁ M₂ w) := by
  obtain ⟨X, h₁, h₂⟩ := hX
  have hne : (commonBaseWeights M₁ M₂ w).Nonempty := ⟨_, X, h₁, h₂, rfl⟩
  exact ⟨hne.csInf_mem (commonBaseWeights_finite M₁ M₂ w),
    fun _ hx => csInf_le (commonBaseWeights_finite M₁ M₂ w).bddBelow hx⟩

/-! ### Steps 1 and 3: Theorem C on `N = M₁ ⊕ M₂✶` -/

/-- A signed tropical circuit on `E × {1, 2}` read at `weight w`: the input `(e, 1)` reads `w_e`
and the input `(e, 2)` reads the constant `0`. -/
def weightCircuit (C : Circuit STOp (m + m)) : Circuit STOp m :=
  circuitOf fun v => runB C (Fin.addCases (motive := fun _ => Arg m) v fun _ => .const)

/-- `weightCircuit C` has the size of `C` and computes `C` at `weight w`. -/
theorem weightCircuit_spec (C : Circuit STOp (m + m)) :
    (weightCircuit C).size = C.size ∧
      ∀ w : Fin m → ℝ, (weightCircuit C).eval (stInterp ℝ) w = C.eval (stInterp ℝ) (weight w) := by
  have h := (runB_impl (n := m) (stInterp ℝ) C).pre (R := realsR m)
    (g := fun v => Fin.addCases (motive := fun _ => Arg m) v fun _ => .const)
    (G := fun x => weight x) fun gs s T hs i => by
      induction i using Fin.addCases with
      | left e =>
        simp only [Fin.addCases_left]
        exact (hs e).congr fun x => (weight_castAdd _ _).symm
      | right e =>
        simp only [Fin.addCases_right]
        exact (den_const gs).congr fun x => by rw [Fin.natAdd_eq_addNat, weight_addNat]; rfl
  obtain ⟨h₁, -, h₃⟩ := circuitOf_spec h
  exact ⟨h₁, h₃⟩

/-- **Theorem `thm:D`, Steps 1 and 3.**  Let `M₁`, `M₂` have ground set `E` and a common base, and
let `B` be a Boolean circuit that outputs in binary the rank in `N = M₁ ⊕ M₂✶` of every
`S ⊆ E × {1, 2}`.  Theorem C on `N` (`2m` elements, the `m` blocks `{(e, 1), (e, 2)}`, rank `m`),
read at `weight w`, computes the minimum weight of a common base at every `w` with at most
`3328 m³ (2m)⁴ (|B| + 2m) + 2` gates. -/
theorem exists_minCommonBase_circuit (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)))
    (B : Circuit BoolOp (m + m))
    (hB : ∀ S : Finset (Fin (m + m)), (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞)
      = (double M₁ M₂).eRk (S : Set (Fin (m + m)))) :
    ∃ C : Circuit STOp m, C.size ≤ 3328 * (m ^ 3 * (m + m) ^ 4 * (B.size + (m + m))) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w] := by
  obtain ⟨X, h₁, h₂⟩ := hX
  have hrank := rank_eq_rank_of_isBase h₁ h₂
  obtain ⟨CN, hCN, hCNe⟩ := TheoremCFinal.theoremC_final (double_ground hE₁ hE₂)
    (rank_double_eq hE₁ hE₂ hrank) ((exists_isRainbowBase_iff hE₁ hE₂ hrank).2 ⟨X, h₁, h₂⟩) B hB
  refine ⟨weightCircuit CN, (weightCircuit_spec CN).1.trans_le hCN, fun w => ?_⟩
  rw [(weightCircuit_spec CN).2, hCNe, opt_eq hE₁ hE₂ hrank]
  rfl

/-! ### Part (1): the minimum weight of a common base -/

/-- `m³ (2m)⁴ (s + 60m + 15) ≤ 1200 m⁷ (s + m)`. -/
theorem size_commonBase_le (m s : ℕ) :
    m ^ 3 * (m + m) ^ 4 * (s + 60 * m + 15) ≤ 1200 * (m ^ 7 * (s + m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · calc m ^ 3 * (m + m) ^ 4 * (s + 60 * m + 15) = 16 * m ^ 7 * (s + 60 * m + 15) := by ring
      _ ≤ 16 * m ^ 7 * (75 * (s + m)) := Nat.mul_le_mul_left _ (by omega)
      _ = 1200 * (m ^ 7 * (s + m)) := by ring

/-- **Theorem `thm:D`, first part.**  Let `M₁`, `M₂` be matroids on `E = Fin m` with ground set
`E` and a common base, and let Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` output `r₁(S)`,
`r₂(S)` in binary from the indicator vector of every `S ⊆ E`.  Then a signed tropical circuit of
size at most `3328 m³ (2m)⁴ (s₁ + s₂ + 60m + 15) + 2 ≤ 3328 · 1200 m⁷ (s₁ + s₂ + m) + 2`
computes the minimum weight of a common base at every `w ∈ ℝ^E`. -/
theorem theoremD_commonBase (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m)))
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3328 * (m ^ 3 * (m + m) ^ 4 * (C₁.size + C₂.size + 60 * m + 15)) + 2 ∧
      C.size ≤ 3328 * 1200 * (m ^ 7 * (C₁.size + C₂.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w] := by
  obtain ⟨C, hC, hCe⟩ := exists_minCommonBase_circuit hE₁ hE₂ hX _
    (doubleRankCircuit_rank hE₁ hE₂ hC₁ hC₂)
  have hB := doubleRankCircuit_size_le (rank_le_card M₂) C₁ C₂
  have h₁ : C.size ≤ 3328 * (m ^ 3 * (m + m) ^ 4 * (C₁.size + C₂.size + 60 * m + 15)) + 2 :=
    hC.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))) 2)
  refine ⟨C, h₁, h₁.trans ?_, hCe⟩
  have h₂ := size_commonBase_le m (C₁.size + C₂.size)
  calc 3328 * (m ^ 3 * (m + m) ^ 4 * (C₁.size + C₂.size + 60 * m + 15)) + 2
      ≤ 3328 * (1200 * (m ^ 7 * (C₁.size + C₂.size + m))) + 2 := by gcongr
    _ = 3328 * 1200 * (m ^ 7 * (C₁.size + C₂.size + m)) + 2 := by ring

/-! ### Step 4: common independent sets as common bases of the padded matroids -/

/-- The weight of `S` at `weight (-w)`, which is `-w_e` on `(e, 1)` and `0` on `(e, 2)`, is
`-w(fst S)`. -/
theorem sum_weight_neg (w : Fin m → ℝ) (S : Finset (Fin (m + m))) :
    ∑ x ∈ S, weight (fun e => -w e) x = -∑ e ∈ fst S, w e := by
  conv_lhs => rw [← pair_fst_snd S]
  rw [pair, sum_union (disjoint_pair _ _), sum_map, sum_map]
  simp [sum_neg_distrib]

/-- The second copies `∅ × {1} ∪ E × {2}` form a common base of the padded matroids. -/
theorem exists_commonBase_pad (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ) :
    ∃ X : Finset (Fin (m + m)), (pad M₁).IsBase (X : Set (Fin (m + m))) ∧
      (pad M₂).IsBase (X : Set (Fin (m + m))) :=
  ⟨pair ∅ univ, (isBase_pad_iff hE₁ _).2 ⟨by simp, by simp [card_pair]⟩,
    (isBase_pad_iff hE₂ _).2 ⟨by simp, by simp [card_pair]⟩⟩

/-- **Theorem `thm:D`, Step 4.**  The common bases of the padded matroids are the sets
`X × {1} ∪ Y × {2}` with `X` a common independent set of `M₁` and `M₂` and `|Y| = m - |X|`
(`isBase_pad_iff`), of weight `-w(X)` at `weight (-w)` (`sum_weight_neg`), and every common
independent set has such a `Y`.  So the least weight of a common base of the padded matroids at
`-w` on the first copies and `0` on the second is minus the greatest weight of a common
independent set of `M₁` and `M₂`. -/
theorem minCommonBaseWeight_pad (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (w : Fin m → ℝ) :
    minCommonBaseWeight (pad M₁) (pad M₂) (weight fun e => -w e) =
      -maxCommonIndepWeight M₁ M₂ w := by
  obtain ⟨⟨S, hS₁, hS₂, hS⟩, hle⟩ :=
    isLeast_minCommonBaseWeight (exists_commonBase_pad hE₁ hE₂) (weight fun e => -w e)
  obtain ⟨⟨X, hX₁, hX₂, hX⟩, hge⟩ := isGreatest_maxCommonIndepWeight M₁ M₂ w
  rw [isBase_pad_iff hE₁] at hS₁
  rw [isBase_pad_iff hE₂] at hS₂
  -- the first copies of a least common base are a common independent set
  have h₁ : ∑ e ∈ fst S, w e ≤ maxCommonIndepWeight M₁ M₂ w := hge ⟨fst S, hS₁.1, hS₂.1, rfl⟩
  -- a greatest common independent set extends to a common base
  obtain ⟨Y, -, hY⟩ := exists_subset_card_eq (show m - #X ≤ #(univ : Finset (Fin m)) by simp)
  have hXm : #X ≤ m := (card_le_univ X).trans_eq (Fintype.card_fin m)
  have hB : ∀ {M : Matroid (Fin m)}, M.E = Set.univ → M.Indep (X : Set (Fin m)) →
      (pad M).IsBase (pair X Y : Set (Fin (m + m))) := fun hE hI =>
    (isBase_pad_iff hE _).2 ⟨by simpa using hI, by rw [card_pair, hY]; omega⟩
  have h₂ := hle ⟨pair X Y, hB hE₁ hX₁, hB hE₂ hX₂, rfl⟩
  rw [sum_weight_neg, fst_pair, ← hX] at h₂
  rw [hS, sum_weight_neg] at h₂ ⊢
  linarith

/-! ### The circuit of Step 4 -/

/-- `-x_e = 0 - x_e` for every entry: `m` gates. -/
def negB (v : Fin m → Arg n) : Bld STOp n (Fin m → Arg n) :=
  tabB fun e => emit .sub .const (v e)

/-- `negB` implements `x ↦ -x` with `m` gates. -/
theorem negB_impl : Impl (realsR m) (realsR (n := n) m) negB m (fun x e => -x e) := by
  refine (Impl.tab fun e => ?_).cost (mul_one m)
  intro gs s T hs
  exact ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
    (den_emit STOp.sub (den_const gs) (hs e)).congr fun x => by simp [stInterp]⟩

/-- Run `D` on `u` and negate its first output: `|D| + 1` gates. -/
def negRunB (D : Circuit STOp m) (u : Fin m → Arg n) : Bld STOp n (Arg n) := fun gs =>
  let q := runB D u gs
  emit .sub .const (q.2.getD 0 .const) q.1

/-- `negRunB D` implements `u ↦ -D(u)₀` with `|D| + 1` gates. -/
theorem negRunB_impl (D : Circuit STOp m) :
    Impl (realsR m) (Rep.arg (stInterp ℝ)) (negRunB (n := n) D) (D.size + 1)
      (fun u => -(D.eval (stInterp ℝ) u).getD 0 0) := by
  intro gs u U hu
  obtain ⟨hp, hl, -, hr⟩ := runB_impl (stInterp ℝ) D hu
  refine ⟨hp.trans (isPrefix_emit _ _ _ _), ?_,
    (den_emit STOp.sub (den_const _) (hr.getD 0)).congr fun x => by simp [stInterp]⟩
  simp only [negRunB, length_emit, hl]
  ring

/-- `-D(-w)`: `m` negations, then `D` with its output negated. -/
def negNegB (D : Circuit STOp m) (w : Fin m → Arg n) : Bld STOp n (List (Arg n)) := fun gs =>
  let q := negB w gs
  let r := negRunB D q.2 q.1
  (r.1, [r.2])

/-- The circuit of Step 4 (`negNegB`) on the inputs `w`. -/
def negNegCircuit (D : Circuit STOp m) : Circuit STOp m :=
  circuitOf (negNegB D)

/-- `negNegCircuit D` has `m + |D| + 1` gates and outputs `-D(-w)`. -/
theorem negNegCircuit_spec (D : Circuit STOp m) :
    (negNegCircuit D).size = m + (D.size + 1) ∧
      ∀ w : Fin m → ℝ, (negNegCircuit D).eval (stInterp ℝ) w =
        [-(D.eval (stInterp ℝ) fun e => -w e).getD 0 0] := by
  have h : Impl (realsR m) (Rep.list (stInterp ℝ) 1) (negNegB (n := m) D) (m + (D.size + 1))
      (fun w => [-(D.eval (stInterp ℝ) fun e => -w e).getD 0 0]) := by
    intro gs w W hw
    obtain ⟨hp₁, hl₁, hr₁⟩ := negB_impl hw
    obtain ⟨hp₂, hl₂, hr₂⟩ := negRunB_impl (n := m) D hr₁
    refine ⟨hp₁.trans hp₂, ?_, rfl, DenL.cons hr₂ (denL_nil _)⟩
    simp only [negNegB]
    rw [hl₂, hl₁]
    ring
  exact ⟨(circuitOf_spec h).1, (circuitOf_spec h).2.2⟩

/-! ### Part (2): the maximum weight of a common independent set -/

/-- `3328 · 2048 m⁷ (s + 268m + 51) + m + 3 ≤ 3328 · 653313 m⁷ (s + m) + 3`. -/
theorem size_commonIndep_le (m s : ℕ) :
    3328 * (2048 * (m ^ 7 * (s + 268 * m + 51))) + m + 3 ≤
      3328 * 653313 * (m ^ 7 * (s + m)) + 3 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h₁ : m ^ 7 * (s + 268 * m + 51) ≤ 319 * (m ^ 7 * (s + m)) := by
      calc m ^ 7 * (s + 268 * m + 51) ≤ m ^ 7 * (319 * (s + m)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 319 * (m ^ 7 * (s + m)) := by ring
    have h₂ : m ≤ m ^ 7 * (s + m) :=
      (Nat.le_self_pow (by norm_num) m).trans (Nat.le_mul_of_pos_right _ (by omega))
    nlinarith

/-- **Theorem `thm:D`, second part.**  Let `M₁`, `M₂` be matroids on `E = Fin m` with ground set
`E`, and let Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` output `r₁(S)`, `r₂(S)` in binary
from the indicator vector of every `S ⊆ E`.  Then a signed tropical circuit of size at most
`3328 · 2048 m⁷ (s₁ + s₂ + 268m + 51) + m + 3 ≤ 3328 · 653313 m⁷ (s₁ + s₂ + m) + 3` computes the
maximum weight of a common independent set at every `w ∈ ℝ^E`: Steps 1 to 3 for the padded
matroids on `2m` elements (`padRankCircuit`, `exists_commonBase_pad`), read at `-w` on the first
copies and `0` on the second, with the output negated (`minCommonBaseWeight_pad`).  No common
base of `M₁` and `M₂` is needed. -/
theorem theoremD_commonIndep (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3328 * (2048 * (m ^ 7 * (C₁.size + C₂.size + 268 * m + 51))) + m + 3 ∧
      C.size ≤ 3328 * 653313 * (m ^ 7 * (C₁.size + C₂.size + m)) + 3 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxCommonIndepWeight M₁ M₂ w] := by
  obtain ⟨D, hD, hDe⟩ := exists_minCommonBase_circuit (M₁ := pad M₁) (M₂ := pad M₂)
    truncate_E truncate_E (exists_commonBase_pad hE₁ hE₂)
    (doubleRankCircuit (padRankCircuit C₁) (padRankCircuit C₂) (rank (pad M₂)))
    (doubleRankCircuit_rank truncate_E truncate_E (padRankCircuit_rank hE₁ hC₁)
      (padRankCircuit_rank hE₂ hC₂))
  have hB := doubleRankCircuit_size_le (rank_le_card (pad M₂)) (padRankCircuit C₁)
    (padRankCircuit C₂)
  have hP₁ := padRankCircuit_size_le C₁
  have hP₂ := padRankCircuit_size_le C₂
  have h₁ : (negNegCircuit (weightCircuit D)).size ≤
      3328 * (2048 * (m ^ 7 * (C₁.size + C₂.size + 268 * m + 51))) + m + 3 := by
    rw [(negNegCircuit_spec _).1, (weightCircuit_spec D).1]
    have h₃ : (m + m) ^ 3 * (m + m + (m + m)) ^ 4 = 2048 * m ^ 7 := by ring
    rw [h₃] at hD
    have h₄ : 2048 * m ^ 7 * ((doubleRankCircuit (padRankCircuit C₁) (padRankCircuit C₂)
        (rank (pad M₂))).size + (m + m + (m + m))) ≤
        2048 * (m ^ 7 * (C₁.size + C₂.size + 268 * m + 51)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have := Nat.mul_le_mul_left 3328 h₄
    omega
  refine ⟨negNegCircuit (weightCircuit D), h₁, h₁.trans (size_commonIndep_le m _), fun w => ?_⟩
  rw [(negNegCircuit_spec _).2, (weightCircuit_spec D).2, hDe, minCommonBaseWeight_pad hE₁ hE₂]
  simp

/-- **Theorem `thm:D` (matroid intersection).**  Let `M₁` and `M₂` be matroids on `E = Fin m`
(ground set `E`, `|E| = m`) with Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` that output the
binary digits of their rank functions, and with a common base.  Then a signed tropical circuit
of size at most `3328 · 1200 m⁷ (s₁ + s₂ + m) + 2` computes the minimum weight of a common base
at every `w ∈ ℝ^E`, and one of size at most `3328 · 653313 m⁷ (s₁ + s₂ + m) + 3` computes the
maximum weight of a common independent set. -/
theorem theoremD (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m)))
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m))) :
    (∃ C : Circuit STOp m, C.size ≤ 3328 * 1200 * (m ^ 7 * (C₁.size + C₂.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w]) ∧
    (∃ C : Circuit STOp m, C.size ≤ 3328 * 653313 * (m ^ 7 * (C₁.size + C₂.size + m)) + 3 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxCommonIndepWeight M₁ M₂ w]) :=
  let ⟨C, _, h, hC⟩ := theoremD_commonBase hE₁ hE₂ hC₁ hC₂ hX
  let ⟨C', _, h', hC'⟩ := theoremD_commonIndep hE₁ hE₂ hC₁ hC₂
  ⟨⟨C, h, hC⟩, ⟨C', h', hC'⟩⟩

end SignedTropical.Rainbow.TheoremD
