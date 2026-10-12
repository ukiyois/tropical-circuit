import SignedTropical.Classes.Graphic
import SignedTropical.Classes.Dual

/-!
# Cographic matroids

`greedy_intersection.tex`, Corollary `cor:classes`, item 5: the dual of the cycle matroid of a multigraph
with `n` vertices and `m` edges, through the dual rank circuit of `Classes/Dual.lean` applied to
the rank circuit of `Classes/Graphic.lean`.

* `cographic_rankCircuit`: a Boolean rank circuit with
  `m(9n² + 5n) + 11n⌈log₂(n+1)⌉ + m + 1 + 11(m+1)⌈log₂(m+1)⌉` gates.
* `corollaryC_cographic`: a signed tropical circuit for `h_{M(G)✶}` with at most
  `100(m+1)²((n+1)² + m + 1)` gates.
-/

namespace SignedTropical.Classes.Graphic.Multigraph

variable {n m : ℕ} (G : Multigraph n m)

/-- **Cographic matroids, rank circuit.**  The dual of the cycle matroid has a Boolean rank
circuit with `m(9n² + 5n) + 11n⌈log₂(n+1)⌉ + m + 1 + 11(m+1)⌈log₂(m+1)⌉` gates. -/
theorem cographic_rankCircuit :
    ∃ B : Circuit BoolOp m,
      B.size = m * (9 * n ^ 2 + 5 * n) + n * (11 * Nat.size n) + m + 1
        + 11 * (m + 1) * Nat.size m ∧
      ∀ S : Finset (Fin m),
        (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = G.cycleMatroid✶.eRk (S : Set (Fin m)) := by
  obtain ⟨B, hB, h⟩ := dual_rankCircuit G.cycleMatroid G.cycleMatroid_E _ G.rankCircuit.2
  exact ⟨B, by rw [hB, G.rankCircuit.1], h⟩

/-- **Corollary `cor:classes`, item 5, cographic matroids.**  For a multigraph with `n` vertices and `m`
edges, maximum-weight bases of the dual of its cycle matroid are computed at every `w ∈ ℝ^m` by a
signed tropical circuit with at most `100(m+1)²((n+1)² + m + 1)` gates. -/
theorem corollaryC_cographic :
    ∃ C : Circuit STOp m, C.size ≤ 100 * (m + 1) ^ 2 * ((n + 1) ^ 2 + m + 1) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight G.cycleMatroid✶ w] := by
  obtain ⟨C, hC, heval⟩ := theoremA_dual G.cycleMatroid G.cycleMatroid_E _ G.rankCircuit.2
  refine ⟨C, hC.trans ?_, heval⟩
  rw [G.rankCircuit.1]
  have hsn : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  have hsm : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self
  have hsk : Nat.size (rank G.cycleMatroid✶) ≤ m :=
    (Nat.size_le.2 Nat.lt_two_pow_self).trans (rank_le_card _)
  have h1 : n * (11 * Nat.size n) ≤ 11 * n ^ 2 := by nlinarith
  have h2 : 11 * (m + 1) * Nat.size m ≤ 11 * (m + 1) * m := Nat.mul_le_mul_left _ hsm
  have h3 : m * Nat.size (rank G.cycleMatroid✶) ≤ m * m := Nat.mul_le_mul_left _ hsk
  nlinarith [Nat.zero_le (m * n), Nat.zero_le (m * n * n), Nat.zero_le (m * m * n * n)]

end SignedTropical.Classes.Graphic.Multigraph
