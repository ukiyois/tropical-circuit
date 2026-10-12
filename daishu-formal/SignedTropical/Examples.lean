import SignedTropical.Polytope
import SignedTropical.Counting
import SignedTropical.Subtractionfree
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Sanity examples

Concrete instances showing that the definitions are not degenerate: the constructed
circuits are evaluated on concrete inputs by the kernel (`decide +kernel`), over `ℤ`, and
the values are transferred to `ℝ` by the homomorphism `ℤ → ℝ` (`eval_intCast`).

* `U_{1,2}`, the binary matroid of `[[1, 1]]`: its rank circuit outputs `min(|S|, 1)`, and
  the circuit of Theorem A returns the greedy value at concrete weights, which gives
  `h_M(3, -1) = 3` and `h_M(-2, -7) = -2` through `theoremACircuit_correct`.
* `U_{2,3}`, the binary matroid of `[[1,0,1],[0,1,1]]`: its rank circuit outputs
  `min(|S|, 2)` on all eight sets; so the hypothesis of Theorem A is met by a non-free,
  non-trivial matroid.
* The compiler on `F(S) = [S ≠ ∅]` at `D = (3, 1, 2)` returns `C_F(D) = 2`.
* The lattice circuit of majority on three inputs is a lattice circuit, computes majority
  over `Bool`, and over `ℝ` returns the Sugeno value, the second largest entry.
* The two's complement simulation of the one-gate circuit `max(x₀, x₁)` returns the bits of
  `max` on `{0,1}²`.
* Theorem B has non-vacuous hypotheses: from Corollary C and Theorem B, every binary matroid
  has a Boolean rank circuit obtained by simulating back.
-/

open Finset

namespace SignedTropical.Examples

/-! ### `U_{1,2}`, end to end -/

/-- `U_{1,2}` as the binary matroid of `[[1, 1]]`. -/
def A12 : Matrix (Fin 1) (Fin 2) (ZMod 2) := !![1, 1]

/-- The rank circuit of `U_{1,2}` outputs `min(|S|, 1)`. -/
theorem rankCircuit_A12 : ∀ S : Finset (Fin 2),
    bitsVal ((binaryRankCircuit A12).eval boolInterp (indicator S)) = min S.card 1 := by
  decide +kernel

theorem rank_A12 : rank (binaryMatroid A12) = 1 := by
  have h := binaryRankCircuit_rank A12 univ
  rw [rankCircuit_A12 univ] at h
  rw [← rk_univ _ (binaryMatroid_E A12)]
  have h' := coe_rk (binaryMatroid A12) univ
  rw [← h] at h'
  exact_mod_cast h'

theorem theoremA_A12_int₁ :
    (theoremACircuit (binaryRankCircuit A12) 1).eval (stInterp ℤ) ![3, -1] = [3] := by
  decide +kernel

theorem theoremA_A12_int₂ :
    (theoremACircuit (binaryRankCircuit A12) 1).eval (stInterp ℤ) ![-2, -7] = [-2] := by
  decide +kernel

/-- Evaluating the circuit of Theorem A over `ℤ` gives `h_M` over `ℝ`. -/
theorem maxBasisWeight_A12 (x : Fin 2 → ℤ) (v : ℤ)
    (hx : (theoremACircuit (binaryRankCircuit A12) 1).eval (stInterp ℤ) x = [v]) :
    maxBasisWeight (binaryMatroid A12) (fun i => (x i : ℝ)) = v := by
  have h := theoremACircuit_correct (binaryMatroid A12) (binaryMatroid_E A12)
    (binaryRankCircuit A12) (binaryRankCircuit_rank A12) (fun i => (x i : ℝ))
  rw [rank_A12, eval_intCast, hx] at h
  simpa using h.symm

/-- **Theorem A, concretely**: the heaviest basis of `U_{1,2}` at `(3, -1)` weighs `3`. -/
example : maxBasisWeight (binaryMatroid A12) ![3, -1] = 3 := by
  have h := maxBasisWeight_A12 _ _ theoremA_A12_int₁
  rw [show (fun i => (((![3, -1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = ![3, -1] by
    funext i; fin_cases i <;> simp] at h
  exact_mod_cast h

/-- At `(-2, -7)` it weighs `-2`: negative weights are handled exactly. -/
example : maxBasisWeight (binaryMatroid A12) ![-2, -7] = -2 := by
  have h := maxBasisWeight_A12 _ _ theoremA_A12_int₂
  rw [show (fun i => (((![-2, -7] : Fin 2 → ℤ) i : ℤ) : ℝ)) = ![-2, -7] by
    funext i; fin_cases i <;> simp] at h
  exact_mod_cast h

/-- The rank circuit of `U_{1,2}` has `m (9 r² + 5 r) + 11 r ⌈log₂(r+1)⌉ = 39` gates. -/
example : (binaryRankCircuit A12).size = 39 := by
  rw [binaryRankCircuit_size]; rfl

/-! ### `U_{2,3}`: a rank circuit meeting the hypothesis of Theorem A -/

/-- `U_{2,3}` as the binary matroid of `[[1,0,1],[0,1,1]]`. -/
def A23 : Matrix (Fin 2) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 1]

/-- The rank circuit of `U_{2,3}` outputs `min(|S|, 2)` on all eight sets. -/
theorem rankCircuit_A23 : ∀ S : Finset (Fin 3),
    bitsVal ((binaryRankCircuit A23).eval boolInterp (indicator S)) = min S.card 2 := by
  decide +kernel

/-- Hence the binary matroid of `[[1,0,1],[0,1,1]]` has rank `min(|S|, 2)` on every set. -/
example (S : Finset (Fin 3)) :
    (binaryMatroid A23).eRk (S : Set (Fin 3)) = (min S.card 2 : ℕ) := by
  rw [← binaryRankCircuit_rank A23 S, rankCircuit_A23 S]

/-! ### The compiler -/

/-- `F(S) = [S ≠ ∅]` on three elements, as one disjunction chain. -/
def orCircuit : Circuit BoolOp 3 :=
  ⟨[⟨.or, .input 0, .input 1⟩, ⟨.or, .wire 0, .input 2⟩], [.wire 1]⟩

theorem orCircuit_spec : ∀ S : Finset (Fin 3),
    orCircuit.eval boolInterp (indicator S) = List.ofFn fun _ : Fin 1 => decide (S.Nonempty) := by
  decide

/-- The compiled circuit at `D = (3, 1, 2)` returns `2 = (2 - 1) + (3 - 2)`. -/
theorem compiler_or_int : (compiler orCircuit).eval (stInterp ℤ) ![3, 1, 2] = [2] := by
  decide +kernel

/-- **Theorem `thm:compiler`, concretely**: `C_F(3, 1, 2) = 2` for `F(S) = [S ≠ ∅]`. -/
example : gapSum (fun S : Finset (Fin 3) => if decide S.Nonempty then 1 else 0) ![3, 1, 2] = 2 := by
  have hD : ∀ e, 0 ≤ (![3, 1, 2] : Fin 3 → ℝ) e := by intro e; fin_cases e <;> norm_num
  have h := (compVal_eq (F := fun _ S => decide S.Nonempty) orCircuit_spec hD)
  have hc := (compileB_spec (B := orCircuit) (denL_ofFn_input (stInterp ℝ) [])).2.2.eval
    ![3, 1, 2]
  have hz := eval_intCast (compiler orCircuit) ![3, 1, 2]
  rw [compiler_or_int, show (fun i => (((![3, 1, 2] : Fin 3 → ℤ) i : ℤ) : ℝ)) = ![3, 1, 2] by
    funext i; fin_cases i <;> simp] at hz
  have h3 := hc.symm.trans hz
  rw [h] at h3
  simpa using h3

/-! ### Lattice circuits -/

/-- Majority of three: `max(min(x₀, x₁), min(x₂, max(x₀, x₁)))`, four gates. -/
def majCircuit : Circuit LatOp 3 :=
  ⟨[⟨.min, .input 0, .input 1⟩, ⟨.max, .input 0, .input 1⟩, ⟨.min, .input 2, .wire 1⟩,
    ⟨.max, .wire 0, .wire 2⟩], [.wire 3]⟩

example : majCircuit.size = 4 := rfl

theorem majCircuit_isLattice : majCircuit.IsLattice := by
  refine ⟨fun k hk => ?_, fun o ho => ?_⟩
  · have hk' : k < 4 := hk
    interval_cases k <;> simp [majCircuit, Arg.Proper]
  · simp only [majCircuit, List.mem_singleton] at ho
    subst ho; simp [Arg.Proper, majCircuit]

theorem majCircuit_mon :
    MonComputes majCircuit (fun S => decide (2 ≤ S.card)) := by
  intro S
  revert S
  decide

theorem maj_monotone : MonotoneObs (fun S : Finset (Fin 3) => decide (2 ≤ S.card)) := by
  intro S T hST h
  simp only [decide_eq_true_eq] at h ⊢
  exact h.trans (Finset.card_le_card hST)

/-- **Theorem `thm:lattice`, concretely**: over `ℝ` the majority circuit returns the Sugeno
value of majority, here the second largest entry `2` of `(3, 1, 2)`. -/
example : sugeno (fun S : Finset (Fin 3) => decide (2 ≤ S.card)) ![3, 1, 2] = 2 := by
  have h := eval_eq_sugeno maj_monotone (by decide) (by decide) majCircuit_isLattice
    majCircuit_mon 0 ![3, 1, 2]
  have hz : majCircuit.eval (latInterp ℤ 0) ![3, 1, 2] = [2] := by decide
  have hcast := majCircuit.eval_map (Int.cast : ℤ → ℝ) (I := latInterp ℤ 0)
    (J := latInterp ℝ 0) ![3, 1, 2] (by simp [latInterp]) (fun o a b => by
      cases o <;> simp [latInterp])
  rw [hz, show (Int.cast ∘ ![3, 1, 2] : Fin 3 → ℝ) = ![3, 1, 2] by
    funext i; fin_cases i <;> simp] at hcast
  rw [hcast] at h
  simpa using h.symm

/-! ### The simulation of Theorem B -/

/-- The one-gate signed tropical circuit `max(x₀, x₁)`. -/
def maxCircuit : Circuit STOp 2 := ⟨[⟨.max, .input 0, .input 1⟩], [.wire 0]⟩

/-- Simulated on `3`-bit two's complement, it outputs the bits of `max` on `{0,1}²`. -/
example : ∀ S : Finset (Fin 2),
    bitsVal ((simulate 3 maxCircuit).eval boolInterp (indicator S))
      = if S.Nonempty then 1 else 0 := by
  decide +kernel

/-- **Theorem B has non-vacuous hypotheses**: simulating back the circuit of Corollary C gives
a Boolean rank circuit for every binary matroid. -/
example {r m : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    ∃ B : Circuit BoolOp m, ∀ T : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator T)) : ℕ∞)
        = (binaryMatroid A).eRk (T : Set (Fin m)) := by
  obtain ⟨C, -, hC⟩ := corollaryC_binary A
  obtain ⟨B, -, hB⟩ := theoremB_of_forall (binaryMatroid A) (binaryMatroid_E A) C hC
  exact ⟨B, hB⟩

end SignedTropical.Examples
