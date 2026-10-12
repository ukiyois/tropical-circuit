import SignedTropical.Rainbow.MinBases

/-!
# The Lagrangian and its certificate

`greedy_intersection.tex`, Section 4.1, Lemma `lem:duality`.  `M : Matroid (Fin m)` has ground
set `univ` and rank `k`, its elements are partitioned into the `k` blocks `blk : Fin m → Fin k`,
`v = w - p_blk` (`shift blk w p`), and `Ψ(p) = Σ_b p_b + β_M(v)` (`Psi`).

* `psi_le_opt`: if `M` has a rainbow base, then `Ψ(p) ≤ Opt(w)` for every `p`.
* `psi_eq_opt`: if `ν₀ = ν(M^v) = k`, then `Ψ(p) = Opt(w)`.

Both rest on one identity: a rainbow base `B` meets every block once, so
`w(B) = Σ_b p_b + v(B)` (`sum_eq_add_shift`).
-/

open Finset

namespace SignedTropical.Rainbow.Pos

open SignedTropical.Rainbow

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {w : Fin m → ℝ} {p : Fin k → ℝ}
  {B : Finset (Fin m)}

/-- A rainbow base `B` of a matroid of rank `k` satisfies `w(B) = Σ_b p_b + v(B)`. -/
theorem sum_eq_add_shift (hk : rank M = k) (hB : IsRainbowBase M blk B) :
    ∑ e ∈ B, w e = ∑ b, p b + ∑ e ∈ B, shift blk w p e := by
  simp only [shift, sum_sub_distrib, hB.sum_comp_blk hk p]
  ring

/-- **Lemma `lem:duality`, weak duality.**  If `M` has a rainbow base, then `Ψ(p) ≤ Opt(w)` for
every `p`. -/
theorem psi_le_opt (hk : rank M = k) (h : ∃ B, IsRainbowBase M blk B) (w : Fin m → ℝ)
    (p : Fin k → ℝ) : Psi M blk w p ≤ Opt M blk w := by
  obtain ⟨B, hB, hw⟩ := exists_isRainbowBase_sum_eq_Opt (w := w) h
  rw [← hw, sum_eq_add_shift (p := p) hk hB, Psi]
  exact add_le_add le_rfl (minBaseWeight_le hB.1)

/-- **Lemma `lem:duality`, certificate.**  If `ν₀ = ν(M^v) = k`, then `Ψ(p) = Opt(w)`: a rainbow
independent set of `M^v` of size `k` is a rainbow base minimum for `v`. -/
theorem psi_eq_opt (hE : M.E = Set.univ) (hk : rank M = k)
    (h : nu (minBases M (shift blk w p)) blk = k) : Psi M blk w p = Opt M blk w := by
  obtain ⟨B, hB⟩ := (nu_eq_iff ((rank_minBases hE _).trans hk)).1 h
  have hmin : IsMinBase M (shift blk w p) B := (isBase_minBases_iff hE).1 hB.1
  have hrb : IsRainbowBase M blk B := ⟨hmin.1, hB.2⟩
  refine le_antisymm (psi_le_opt hk ⟨B, hrb⟩ w p) ?_
  rw [Psi, ← hmin.sum_eq, ← sum_eq_add_shift hk hrb]
  exact Opt_le hrb

end SignedTropical.Rainbow.Pos
