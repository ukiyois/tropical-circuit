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
  independent set); `maxCommonIndepCard`, the largest size of a common independent set.
* `weightCircuit`: a signed tropical circuit on `E × {1, 2}` read at `Doubling.weight w`, with
  no extra gate.
* Steps 1 and 3 (`exists_minCommonBase_circuit`): with a common base and a rank circuit `B` of
  `N = M₁ ⊕ M₂✶`, Theorem C (`TheoremCFinal.theoremC_final`) on `N` (`2m` elements, `m` blocks,
  rank `m`), read at `weight w`, computes the minimum weight of a common base
  (`Doubling.opt_eq`) with at most `2436 m⁴ (2m)⁶ (|B| + 2m) + 2` gates.
* **Part (1)** (`theoremD_commonBase`): with the rank circuit `doubleRankCircuit` of Step 2, at
  most `2436 m⁴ (2m)⁶ (s₁ + s₂ + 60m + 15) + 2 ≤ 2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2` gates.
* Step 4 (`isGreatest_neg_minCommonBaseWeight`, `maxCommonIndepWeight_eq`): the largest weight
  of a common independent set of size `j` is `-β_j(-w)`, `β_j` the minimum weight of a common
  base of the truncations at `j`; the maximum weight of a common independent set is the maximum
  of `0` (for `j = 0`) and these values for `j = 1, …, J`, `J` the largest size of a common
  independent set.
* The circuit of Step 4 (`maxIndepCircuit`, `maxIndepCircuit_spec`): `u = -w` (`m` gates), the
  circuits `D_j` at `u` with their outputs negated (one gate each), and the maximum with `0`
  (`J` gates).
* **Part (2)** (`theoremD_commonIndep`): with the rank circuits `doubleTruncRankCircuit` of the
  doubled truncations, at most `m + m (2436 m⁴ (2m)⁶ (s₁ + s₂ + 76m + 21) + 4) ≤
  2436 · 6209 m¹¹ (s₁ + s₂ + m)` gates.
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

/-- The largest size of a common independent set of `M₁` and `M₂`. -/
noncomputable def maxCommonIndepCard : ℕ :=
  sSup {j | ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧
    #X = j}

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

/-- The sizes of the common independent sets are at most `m`. -/
theorem bddAbove_commonIndepCards : BddAbove {j | ∃ X : Finset (Fin m),
    M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧ #X = j} := by
  refine ⟨m, ?_⟩
  rintro _ ⟨X, -, -, rfl⟩
  exact (card_le_univ X).trans_eq (Fintype.card_fin m)

/-- A common independent set has at most `maxCommonIndepCard M₁ M₂` elements. -/
theorem card_le_maxCommonIndepCard {X : Finset (Fin m)} (h₁ : M₁.Indep (X : Set (Fin m)))
    (h₂ : M₂.Indep (X : Set (Fin m))) : #X ≤ maxCommonIndepCard M₁ M₂ :=
  le_csSup bddAbove_commonIndepCards ⟨X, h₁, h₂, rfl⟩

/-- Some common independent set has `maxCommonIndepCard M₁ M₂` elements. -/
theorem exists_card_eq_maxCommonIndepCard : ∃ X : Finset (Fin m),
    M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧ #X = maxCommonIndepCard M₁ M₂ :=
  Nat.sSup_mem (s := {j | ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧
    M₂.Indep (X : Set (Fin m)) ∧ #X = j}) ⟨0, ∅, by simp, by simp, rfl⟩ bddAbove_commonIndepCards

/-- Every `j ≤ maxCommonIndepCard M₁ M₂` is the size of a common independent set. -/
theorem exists_commonIndep_card {j : ℕ} (hj : j ≤ maxCommonIndepCard M₁ M₂) :
    ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧ #X = j := by
  obtain ⟨X, h₁, h₂, hX⟩ := exists_card_eq_maxCommonIndepCard (M₁ := M₁) (M₂ := M₂)
  obtain ⟨Y, hYX, hY⟩ := exists_subset_card_eq (hj.trans_eq hX.symm)
  exact ⟨Y, h₁.subset (coe_subset.2 hYX), h₂.subset (coe_subset.2 hYX), hY⟩

/-- `maxCommonIndepCard M₁ M₂ ≤ m`. -/
theorem maxCommonIndepCard_le : maxCommonIndepCard M₁ M₂ ≤ m := by
  obtain ⟨X, -, -, hX⟩ := exists_card_eq_maxCommonIndepCard (M₁ := M₁) (M₂ := M₂)
  exact hX ▸ (card_le_univ X).trans_eq (Fintype.card_fin m)

/-- An independent set has at most `r(E)` elements. -/
theorem le_rank_of_indep {M : Matroid (Fin m)} {X : Finset (Fin m)}
    (h : M.Indep (X : Set (Fin m))) : #X ≤ rank M :=
  (card_le_rk M h (subset_univ X)).trans (rk_le_rank M univ)

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
`2436 m⁴ (2m)⁶ (|B| + 2m) + 2` gates. -/
theorem exists_minCommonBase_circuit (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m)))
    (B : Circuit BoolOp (m + m))
    (hB : ∀ S : Finset (Fin (m + m)), (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞)
      = (double M₁ M₂).eRk (S : Set (Fin (m + m)))) :
    ∃ C : Circuit STOp m, C.size ≤ 2436 * (m ^ 4 * (m + m) ^ 6 * (B.size + (m + m))) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w] := by
  obtain ⟨X, h₁, h₂⟩ := hX
  have hrank := rank_eq_rank_of_isBase h₁ h₂
  obtain ⟨CN, hCN, hCNe⟩ := TheoremCFinal.theoremC_final (double_ground hE₁ hE₂)
    (rank_double_eq hE₁ hE₂ hrank) ((exists_isRainbowBase_iff hE₁ hE₂ hrank).2 ⟨X, h₁, h₂⟩) B hB
  refine ⟨weightCircuit CN, (weightCircuit_spec CN).1.trans_le hCN, fun w => ?_⟩
  rw [(weightCircuit_spec CN).2, hCNe, opt_eq hE₁ hE₂ hrank]
  rfl

/-! ### Part (1): the minimum weight of a common base -/

/-- `m⁴ (2m)⁶ (s + 60m + 15) ≤ 4800 m¹⁰ (s + m)`. -/
theorem size_commonBase_le (m s : ℕ) :
    m ^ 4 * (m + m) ^ 6 * (s + 60 * m + 15) ≤ 4800 * (m ^ 10 * (s + m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · calc m ^ 4 * (m + m) ^ 6 * (s + 60 * m + 15) = 64 * m ^ 10 * (s + 60 * m + 15) := by ring
      _ ≤ 64 * m ^ 10 * (75 * (s + m)) := Nat.mul_le_mul_left _ (by omega)
      _ = 4800 * (m ^ 10 * (s + m)) := by ring

/-- **Theorem `thm:D`, first part.**  Let `M₁`, `M₂` be matroids on `E = Fin m` with ground set
`E` and a common base, and let Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` output `r₁(S)`,
`r₂(S)` in binary from the indicator vector of every `S ⊆ E`.  Then a signed tropical circuit of
size at most `2436 m⁴ (2m)⁶ (s₁ + s₂ + 60m + 15) + 2 ≤ 2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2`
computes the minimum weight of a common base at every `w ∈ ℝ^E`. -/
theorem theoremD_commonBase (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m)))
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ 2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 60 * m + 15)) + 2 ∧
      C.size ≤ 2436 * 4800 * (m ^ 10 * (C₁.size + C₂.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w] := by
  obtain ⟨C, hC, hCe⟩ := exists_minCommonBase_circuit hE₁ hE₂ hX _
    (doubleRankCircuit_rank hE₁ hE₂ hC₁ hC₂)
  have hB := doubleRankCircuit_size_le (rank_le_card M₂) C₁ C₂
  have h₁ : C.size ≤ 2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 60 * m + 15)) + 2 :=
    hC.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))) 2)
  refine ⟨C, h₁, h₁.trans ?_, hCe⟩
  have h₂ := size_commonBase_le m (C₁.size + C₂.size)
  calc 2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 60 * m + 15)) + 2
      ≤ 2436 * (4800 * (m ^ 10 * (C₁.size + C₂.size + m))) + 2 := by gcongr
    _ = 2436 * 4800 * (m ^ 10 * (C₁.size + C₂.size + m)) + 2 := by ring

/-! ### Step 4: common independent sets as common bases of truncations -/

/-- **Theorem `thm:D`, Step 4, one size.**  If some common independent set of `M₁` and `M₂` has
`j` elements, then `-β(-w)`, where `β(u)` is the minimum weight of a common base of the
truncations of `M₁` and `M₂` at `j`, is the greatest weight of a common independent set with
`j` elements. -/
theorem isGreatest_neg_minCommonBaseWeight (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    {j : ℕ} (hj : ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧ M₂.Indep (X : Set (Fin m)) ∧
      #X = j) (w : Fin m → ℝ) :
    IsGreatest {x | ∃ X : Finset (Fin m), M₁.Indep (X : Set (Fin m)) ∧
        M₂.Indep (X : Set (Fin m)) ∧ #X = j ∧ x = ∑ e ∈ X, w e}
      (-minCommonBaseWeight (truncate M₁ j) (truncate M₂ j) fun e => -w e) := by
  obtain ⟨X₀, h₁, h₂, rfl⟩ := hj
  have hiff := isBase_truncate_both_iff hE₁ hE₂ (le_rank_of_indep h₁) (le_rank_of_indep h₂)
  obtain ⟨⟨X, hX₁, hX₂, hX⟩, hle⟩ := isLeast_minCommonBaseWeight
    (M₁ := truncate M₁ #X₀) (M₂ := truncate M₂ #X₀) ⟨X₀, (hiff X₀).2 ⟨h₁, h₂, rfl⟩⟩ fun e => -w e
  obtain ⟨hI₁, hI₂, hXc⟩ := (hiff X).1 ⟨hX₁, hX₂⟩
  refine ⟨⟨X, hI₁, hI₂, hXc, by rw [hX, sum_neg_distrib, neg_neg]⟩, ?_⟩
  rintro x ⟨Y, hY₁, hY₂, hYc, rfl⟩
  have h := hle ⟨Y, ((hiff Y).2 ⟨hY₁, hY₂, hYc⟩).1, ((hiff Y).2 ⟨hY₁, hY₂, hYc⟩).2, rfl⟩
  rw [sum_neg_distrib] at h
  linarith

/-- `l.foldr max 0` is at least `0` and every entry of `l`, and it is `0` or an entry. -/
theorem foldr_max_spec (l : List ℝ) :
    0 ≤ l.foldr max 0 ∧ (∀ x ∈ l, x ≤ l.foldr max 0) ∧
      (l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₀, h₁, h₂⟩ := ih
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨le_max_of_le_right h₀, ⟨le_max_left _ _, fun x hx => le_max_of_le_right (h₁ x hx)⟩,
      ?_⟩
    rcases le_total a (l.foldr max 0) with h | h
    · rw [max_eq_right h]
      exact h₂.imp id Or.inr
    · rw [max_eq_left h]
      exact Or.inr (Or.inl rfl)

/-- **Theorem `thm:D`, Step 4.**  The maximum weight of a common independent set is the maximum
of `0` (the empty set) and of `-β_j(-w)` for `j = 1, …, J`, where `J` is the largest size of a
common independent set and `β_j(u)` the minimum weight of a common base of the truncations of
`M₁` and `M₂` at `j`. -/
theorem maxCommonIndepWeight_eq (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (w : Fin m → ℝ) :
    maxCommonIndepWeight M₁ M₂ w = (List.ofFn fun i : Fin (maxCommonIndepCard M₁ M₂) =>
      -minCommonBaseWeight (truncate M₁ (i + 1)) (truncate M₂ (i + 1)) fun e => -w e).foldr
        max 0 := by
  obtain ⟨h₀, hle, hmem⟩ := foldr_max_spec (List.ofFn fun i : Fin (maxCommonIndepCard M₁ M₂) =>
    -minCommonBaseWeight (truncate M₁ (i + 1)) (truncate M₂ (i + 1)) fun e => -w e)
  have ha := fun i : Fin (maxCommonIndepCard M₁ M₂) =>
    isGreatest_neg_minCommonBaseWeight hE₁ hE₂ (exists_commonIndep_card (M₁ := M₁) (M₂ := M₂)
      i.2) w
  refine (isGreatest_maxCommonIndepWeight M₁ M₂ w).unique ⟨?_, ?_⟩
  · rcases hmem with h | h
    · rw [h]
      exact ⟨∅, by simp, by simp, by simp⟩
    · obtain ⟨i, hi⟩ := List.mem_ofFn.1 h
      obtain ⟨X, h₁, h₂, -, hX⟩ := (ha i).1
      exact ⟨X, h₁, h₂, hi ▸ hX⟩
  · rintro x ⟨X, h₁, h₂, rfl⟩
    rcases Nat.eq_zero_or_pos #X with h | h
    · rw [card_eq_zero.1 h, sum_empty]
      exact h₀
    · have hX := card_le_maxCommonIndepCard h₁ h₂
      exact ((ha ⟨#X - 1, by omega⟩).2 ⟨X, h₁, h₂, by simp only; omega, rfl⟩).trans
        (hle _ (List.mem_ofFn.2 ⟨_, rfl⟩))

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

/-- The maximum of `0` and the entries of a list: one gate per entry. -/
def maxB : List (Arg n) → Bld STOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | a :: l => fun gs =>
    let q := maxB l gs
    emit .max a q.2 q.1

/-- `maxB` computes the maximum of `0` and the entries of a list with one gate per entry. -/
theorem maxB_spec :
    ∀ {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs l F →
      gs <+: (maxB l gs).1 ∧ (maxB l gs).1.length = gs.length + l.length ∧
        Den (stInterp ℝ) (maxB l gs).1 (maxB l gs).2 (fun x => (F x).foldr max 0)
  | [], F, gs, h => ⟨List.prefix_refl _, by simp [maxB], (den_const gs).congr fun x => by
      rw [show F x = [] by rw [← h.2 x]; rfl]; rfl⟩
  | a :: l, F, gs, h => by
    obtain ⟨ha, hl, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hv⟩ := maxB_spec hl
    have hr := den_emit STOp.max (ha.mono hp) hv
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), by simp [maxB, length_emit, hlen]; ring,
      hr.congr fun x => ?_⟩
    conv_rhs => rw [hF x]
    rfl

/-- The circuit of Step 4, from signed tropical circuits `D i` (`i < J`): `u = -w`, the values
`-D_i(u)`, and their maximum with `0`. -/
def maxIndepB {J : ℕ} (D : Fin J → Circuit STOp m) (w : Fin m → Arg n) :
    Bld STOp n (List (Arg n)) := fun gs =>
  let q₁ := negB w gs
  let q₂ := tabB (fun i => negRunB (D i) q₁.2) q₁.1
  let q₃ := maxB (List.ofFn q₂.2) q₂.1
  (q₃.1, [q₃.2])

/-- The circuit of Step 4 (`maxIndepB`) on the inputs `w`. -/
def maxIndepCircuit {J : ℕ} (D : Fin J → Circuit STOp m) : Circuit STOp m :=
  circuitOf (maxIndepB D)

/-- The size of the circuit of Step 4, `m + Σ_i (|D_i| + 1) + J`, and its single output
`max(0, max_i -D_i(-w))`. -/
theorem maxIndepCircuit_spec {J : ℕ} (D : Fin J → Circuit STOp m) :
    (maxIndepCircuit D).size = m + ∑ i, ((D i).size + 1) + J ∧
      ∀ w : Fin m → ℝ, (maxIndepCircuit D).eval (stInterp ℝ) w =
        [(List.ofFn fun i => -((D i).eval (stInterp ℝ) fun e => -w e).getD 0 0).foldr max 0] := by
  have h : Impl (realsR m) (Rep.list (stInterp ℝ) 1) (maxIndepB (n := m) D)
      (m + ∑ i, ((D i).size + 1) + J)
      (fun w => [(List.ofFn fun i => -((D i).eval (stInterp ℝ) fun e => -w e).getD 0 0).foldr
        max 0]) := by
    intro gs w W hw
    obtain ⟨hp₁, hl₁, hr₁⟩ := negB_impl hw
    obtain ⟨hp₂, hl₂, hr₂⟩ := (Impl.tabSum fun i => negRunB_impl (n := m) (D i)) hr₁
    obtain ⟨hp₃, hl₃, hr₃⟩ := maxB_spec (denL_ofFn hr₂)
    refine ⟨(hp₁.trans hp₂).trans hp₃, ?_, rfl, DenL.cons hr₃ (denL_nil _)⟩
    simp only [maxIndepB]
    rw [hl₃, hl₂, hl₁, List.length_ofFn]
    ring
  exact ⟨(circuitOf_spec h).1, (circuitOf_spec h).2.2⟩

/-! ### Part (2): the maximum weight of a common independent set -/

/-- `m + m (2436 m⁴ (2m)⁶ (s + 76m + 21) + 4) ≤ 2436 · 6209 m¹¹ (s + m)`. -/
theorem size_commonIndep_le (m s : ℕ) :
    m + m * (2436 * (m ^ 4 * (m + m) ^ 6 * (s + 76 * m + 21)) + 4) ≤
      2436 * 6209 * (m ^ 11 * (s + m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h₁ : m ^ 4 * (m + m) ^ 6 * (s + 76 * m + 21) ≤ 6208 * (m ^ 10 * (s + m)) := by
      calc m ^ 4 * (m + m) ^ 6 * (s + 76 * m + 21) = 64 * m ^ 10 * (s + 76 * m + 21) := by ring
        _ ≤ 64 * m ^ 10 * (97 * (s + m)) := Nat.mul_le_mul_left _ (by omega)
        _ = 6208 * (m ^ 10 * (s + m)) := by ring
    have h₂ : 5 * m ≤ 2436 * (m ^ 11 * (s + m)) := by
      have : m ≤ m ^ 11 * (s + m) :=
        (Nat.le_self_pow (by norm_num) m).trans (Nat.le_mul_of_pos_right _ (by omega))
      omega
    calc m + m * (2436 * (m ^ 4 * (m + m) ^ 6 * (s + 76 * m + 21)) + 4)
        ≤ m + m * (2436 * (6208 * (m ^ 10 * (s + m))) + 4) := by gcongr
      _ = 2436 * 6208 * (m ^ 11 * (s + m)) + 5 * m := by ring
      _ ≤ 2436 * 6208 * (m ^ 11 * (s + m)) + 2436 * (m ^ 11 * (s + m)) := by omega
      _ = 2436 * 6209 * (m ^ 11 * (s + m)) := by ring

/-- **Theorem `thm:D`, second part.**  Let `M₁`, `M₂` be matroids on `E = Fin m` with ground set
`E`, and let Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` output `r₁(S)`, `r₂(S)` in binary
from the indicator vector of every `S ⊆ E`.  Then a signed tropical circuit of size at most
`m + m (2436 m⁴ (2m)⁶ (s₁ + s₂ + 76m + 21) + 4) ≤ 2436 · 6209 m¹¹ (s₁ + s₂ + m)` computes the
maximum weight of a common independent set at every `w ∈ ℝ^E`.  No common base is needed. -/
theorem theoremD_commonIndep (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ m + m * (2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 76 * m + 21)) + 4) ∧
      C.size ≤ 2436 * 6209 * (m ^ 11 * (C₁.size + C₂.size + m)) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxCommonIndepWeight M₁ M₂ w] := by
  set Y := 2436 * (m ^ 4 * (m + m) ^ 6 * (C₁.size + C₂.size + 76 * m + 21)) with hY
  have hJ : maxCommonIndepCard M₁ M₂ ≤ m := maxCommonIndepCard_le
  -- the circuits of Steps 1 to 3 for the truncations at `i + 1`, `i < J`
  have hD : ∀ i : Fin (maxCommonIndepCard M₁ M₂), ∃ D : Circuit STOp m, D.size ≤ Y + 2 ∧
      ∀ w : Fin m → ℝ, D.eval (stInterp ℝ) w =
        [minCommonBaseWeight (truncate M₁ (i + 1)) (truncate M₂ (i + 1)) w] := by
    intro i
    obtain ⟨X, h₁, h₂, hX⟩ := exists_commonIndep_card (M₁ := M₁) (M₂ := M₂) i.2
    obtain ⟨D, hD, hDe⟩ := exists_minCommonBase_circuit truncate_E truncate_E
      ⟨X, (isBase_truncate_both_iff hE₁ hE₂ (hX ▸ le_rank_of_indep h₁)
        (hX ▸ le_rank_of_indep h₂) X).2 ⟨h₁, h₂, hX⟩⟩ _
      (doubleTruncRankCircuit_rank hE₁ hE₂ hC₁ hC₂ (i + 1))
    have := doubleTruncRankCircuit_size_le (show (i : ℕ) + 1 ≤ m by omega) C₁ C₂ (rank M₂)
    exact ⟨D, hD.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (by omega))) 2), hDe⟩
  choose D hDs hDe using hD
  have hsize : (maxIndepCircuit D).size ≤ m + m * (Y + 4) := by
    have hsum : ∑ i, ((D i).size + 1) ≤ maxCommonIndepCard M₁ M₂ * (Y + 3) := by
      calc ∑ i, ((D i).size + 1) ≤ ∑ _i : Fin (maxCommonIndepCard M₁ M₂), (Y + 3) :=
            sum_le_sum fun i _ => by have := hDs i; omega
        _ = maxCommonIndepCard M₁ M₂ * (Y + 3) := by simp
    rw [(maxIndepCircuit_spec D).1]
    calc m + ∑ i, ((D i).size + 1) + maxCommonIndepCard M₁ M₂
        ≤ m + maxCommonIndepCard M₁ M₂ * (Y + 3) + maxCommonIndepCard M₁ M₂ := by omega
      _ = m + maxCommonIndepCard M₁ M₂ * (Y + 4) := by ring
      _ ≤ m + m * (Y + 4) := by gcongr
  refine ⟨maxIndepCircuit D, hsize, hsize.trans (size_commonIndep_le m _), fun w => ?_⟩
  rw [(maxIndepCircuit_spec D).2, maxCommonIndepWeight_eq hE₁ hE₂]
  simp only [hDe, List.getD_cons_zero]

/-- **Theorem `thm:D` (matroid intersection).**  Let `M₁` and `M₂` be matroids on `E = Fin m`
(ground set `E`, `|E| = m`) with Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` that output the
binary digits of their rank functions, and with a common base.  Then a signed tropical circuit
of size at most `2436 · 4800 m¹⁰ (s₁ + s₂ + m) + 2` computes the minimum weight of a common base
at every `w ∈ ℝ^E`, and one of size at most `2436 · 6209 m¹¹ (s₁ + s₂ + m)` computes the
maximum weight of a common independent set. -/
theorem theoremD (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m)))
    (hX : ∃ X : Finset (Fin m), M₁.IsBase (X : Set (Fin m)) ∧ M₂.IsBase (X : Set (Fin m))) :
    (∃ C : Circuit STOp m, C.size ≤ 2436 * 4800 * (m ^ 10 * (C₁.size + C₂.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [minCommonBaseWeight M₁ M₂ w]) ∧
    (∃ C : Circuit STOp m, C.size ≤ 2436 * 6209 * (m ^ 11 * (C₁.size + C₂.size + m)) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxCommonIndepWeight M₁ M₂ w]) :=
  let ⟨C, _, h, hC⟩ := theoremD_commonBase hE₁ hE₂ hC₁ hC₂ hX
  let ⟨C', _, h', hC'⟩ := theoremD_commonIndep hE₁ hE₂ hC₁ hC₂
  ⟨⟨C, h, hC⟩, ⟨C', h', hC'⟩⟩

end SignedTropical.Rainbow.TheoremD
