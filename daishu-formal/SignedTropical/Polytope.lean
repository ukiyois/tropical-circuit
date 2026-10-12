import SignedTropical.Binary
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Jensen

/-!
# Corollary E: virtual extension complexity of base polytopes

`docs/research-direction-2026-10-11.md`, Section 3.2, Corollary E: Hertrich and Loho prove
`vxc(P) ≤ O(nnc(P))`, so every linear matroid base polytope has polynomial virtual
extension complexity.

The part proved here is that the support function of the base polytope
`B(M) = conv{1_B : B a basis}` is `h_M` (`supportFn_basePolytope`), so that Theorem A and
Corollary C give signed tropical circuits for it.  Virtual extension complexity, network
complexity, and the conversion of a signed tropical circuit into a network are not
formalized: the composite of Hertrich and Loho's bound with that conversion enters as the
hypothesis `hHL` on an abstract quantity `vxc`, namely that a polytope whose support
function has a signed tropical circuit of size `s` has `vxc ≤ c s`.
-/

open Finset

namespace SignedTropical

variable {m r : ℕ}

/-- The indicator vector of a set of elements, in `ℝ^m`. -/
def indVec (B : Finset (Fin m)) : Fin m → ℝ := fun e => if e ∈ B then 1 else 0

/-- The base polytope of `M`: the convex hull of the indicator vectors of its bases. -/
def basePolytope (M : Matroid (Fin m)) : Set (Fin m → ℝ) :=
  convexHull ℝ {x | ∃ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ∧ x = indVec B}

/-- The support function of a set: `w ↦ sup_{x ∈ P} ⟨w, x⟩`. -/
noncomputable def supportFn (P : Set (Fin m → ℝ)) (w : Fin m → ℝ) : ℝ :=
  sSup ((fun x => ∑ e, w e * x e) '' P)

theorem convexOn_dot (w : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (fun x : Fin m → ℝ => ∑ e, w e * x e) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem dot_indVec (w : Fin m → ℝ) (B : Finset (Fin m)) : ∑ e, w e * indVec B e = ∑ e ∈ B, w e := by
  simp [indVec, Finset.sum_ite_mem]

/-- **The support function of the base polytope is `h_M`.** -/
theorem supportFn_basePolytope (M : Matroid (Fin m)) (w : Fin m → ℝ) :
    supportFn (basePolytope M) w = maxBasisWeight M w := by
  apply IsGreatest.csSup_eq
  obtain ⟨⟨B, hB, hBv⟩, hmax⟩ := isGreatest_maxBasisWeight M w
  refine ⟨⟨indVec B, subset_convexHull ℝ _ ⟨B, hB, rfl⟩, by beta_reduce; rw [dot_indVec, hBv]⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, ⟨B', hB', rfl⟩, hle⟩ :=
    ConvexOn.exists_ge_of_mem_convexHull (convexOn_dot w) (Set.subset_univ _) hx
  refine hle.trans ?_
  rw [dot_indVec]
  exact hmax ⟨B', hB', rfl⟩

/-- **Corollary E, for any matroid with a Boolean rank circuit.**  Assume (Hertrich and
Loho, with the conversion of circuits into networks) that a polytope whose support function
is computed at every `w` by a signed tropical circuit of size `s` has `vxc ≤ c s`.  Then the
base polytope of `M` has `vxc` at most `c` times the bound of Theorem A. -/
theorem corollaryE (vxc : Set (Fin m → ℝ) → ℕ) (c : ℕ)
    (hHL : ∀ (P : Set (Fin m → ℝ)) (C : Circuit STOp m),
      (∀ w, C.eval (stInterp ℝ) w = [supportFn P w]) → vxc P ≤ c * C.size)
    (M : Matroid (Fin m)) (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    vxc (basePolytope M) ≤ c * (3 * m * B.size + m * Nat.size (rank M) + 9 * m ^ 2 + 4 * m
      + 4 * Nat.size (rank M) + 1) := by
  obtain ⟨C, hsize, heval⟩ := theoremA M hE B hB
  refine (hHL _ C fun w => by rw [heval, supportFn_basePolytope]).trans ?_
  exact Nat.mul_le_mul_left c hsize

/-- **Corollary E, binary matroids.**  Under the same hypothesis, the base polytope of the
binary matroid of `A ∈ GF(2)^{r × m}` has `vxc ≤ 100 c (m+1)² (r+1)²`. -/
theorem corollaryE_binary (vxc : Set (Fin m → ℝ) → ℕ) (c : ℕ)
    (hHL : ∀ (P : Set (Fin m → ℝ)) (C : Circuit STOp m),
      (∀ w, C.eval (stInterp ℝ) w = [supportFn P w]) → vxc P ≤ c * C.size)
    (A : Matrix (Fin r) (Fin m) (ZMod 2)) :
    vxc (basePolytope (binaryMatroid A)) ≤ c * (100 * (m + 1) ^ 2 * (r + 1) ^ 2) := by
  obtain ⟨C, hsize, heval⟩ := corollaryC_binary_poly A
  refine (hHL _ C fun w => by rw [heval, supportFn_basePolytope]).trans ?_
  exact Nat.mul_le_mul_left c hsize

end SignedTropical
