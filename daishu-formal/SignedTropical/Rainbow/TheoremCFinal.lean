import SignedTropical.Rainbow.Observer
import SignedTropical.Rainbow.TheoremC

/-!
# Theorem C, unconditional

`greedy_intersection.tex`, Theorem `thm:C`: if a Boolean circuit of size `s` outputs the binary
digits of the rank of `M` and `M` has a rainbow base, then a signed tropical circuit of size
`O(k³ m⁴ (s + m))` computes `Opt(w)` at every `w`.

`Rainbow/TheoremC.lean` (`TheoremC.theoremC`, `TheoremC.theoremC_bigO`) takes the observers of
Lemma `lem:observer` as a hypothesis (`TheoremC.IsObserver`).  Here the observer circuits of
`Rainbow/Observer.lean` discharge it:

* `isObserver_observer`: `observer M B blk r` satisfies `TheoremC.IsObserver M blk r`, for every
  `r`;
* `observer_size_le`: its size is at most `424 (r + 2) m² (s + m)` for `m ≥ 1`, `k ≤ m` and
  `r < k`;
* `theoremC_final`: Theorem `thm:C` with the explicit bound `3328 k³ m⁴ (s + m) + 2`;
  `theoremC_final_poly`: the same with the explicit polynomial bound of `TheoremC.theoremC`;
* `theoremC_final_rankOne`: when every component of `M` has rank at most one (Corollary
  `cor:rankone`), the bound `1390 k³ m³ (s + m) + 2`.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremCFinal

open SignedTropical SignedTropical.Rainbow SignedTropical.Rainbow.Observer

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k}

/-- **The observer of Lemma `lem:observer` is an observer of stage `r`** in the sense of the
proof of Theorem C (`TheoremC.IsObserver`), for every `r`. -/
theorem isObserver_observer (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r : ℕ) :
    TheoremC.IsObserver M blk r (observer M B blk r) :=
  (lem_observer hE hB blk r).2.2.2

/-- **The size of the observer in the form of `TheoremC.theoremC_bigO`**: for `m ≥ 1`, `k ≤ m`
and `r < k`, at most `424 (r + 2) m² (s + m)`. -/
theorem observer_size_le (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) {r : ℕ} (hm : 1 ≤ m) (hkm : k ≤ m) (hr : r < k) :
    (observer M B blk r).size ≤ 424 * ((r + 2) * m ^ 2 * (B.size + m)) :=
  (lem_observer hE hB blk r).1 ▸ obsCost_le_bigO hm hkm hr

/-- **Theorem `thm:C`.**  Let `M` be a matroid on `E = Fin m` with ground set `E` and rank `k`,
with a rainbow base for the blocks `blk`, and let the Boolean circuit `B` of size `s` output the
binary digits of the rank of `M`.  Then a signed tropical circuit of size at most
`3328 k³ m⁴ (s + m) + 2` computes `Opt(w)` at every `w ∈ ℝ^E`. -/
theorem theoremC_final (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m, C.size ≤ 3328 * (k ^ 3 * m ^ 4 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] := by
  have hkm : k ≤ m := hk ▸ rank_le_card M
  obtain ⟨C, hC, hCe⟩ := TheoremC.theoremC_bigO hE hk hM B hB (fun r => observer M B blk r) 424
    fun r h₁ h₂ => ⟨isObserver_observer hE B hB blk r,
      observer_size_le hE B hB blk ((h₁.trans_lt h₂).le.trans hkm) hkm h₂⟩
  exact ⟨C, by omega, hCe⟩

/-- **Theorem `thm:C`, with the explicit polynomial of `TheoremC.theoremC`**: the observer of
stage `r` has at most `(r+2)(m+1)²(s + 52(m+1)) + ms + 2m² + 3k(m+1) + 5⌈log₂(r+1)⌉` gates. -/
theorem theoremC_final_poly (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ ∑ r ∈ range k, Schedule.stageLength k m r *
          (6 * m * ((r + 2) * (m + 1) ^ 2 * (B.size + 52 * (m + 1)) + m * B.size + 2 * m ^ 2 +
            3 * k * (m + 1) + 5 * Nat.size r) + TheoremC.updOver m k B.size) +
        (3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  TheoremC.theoremC hE hk hM B hB (fun r => observer M B blk r) _ fun r _ _ =>
    ⟨isObserver_observer hE B hB blk r, (lem_observer hE hB blk r).2.1⟩

/-- **Theorem `thm:C` for components of rank one** (Corollary `cor:rankone`).  Under the hypotheses
of `theoremC_final`, if every component of `M` has rank at most one (the assignment problem is
the case of a partition matroid with unit capacities), then a signed tropical circuit of size at
most `1390 k³ m³ (s + m) + 2` computes `Opt(w)` at every `w ∈ ℝ^E`. -/
theorem theoremC_final_rankOne (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m, C.size ≤ 1390 * (k ^ 3 * m ^ 3 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] := by
  have hkm : k ≤ m := hk ▸ rank_le_card M
  obtain ⟨C, hC, hCe⟩ := TheoremC.theoremC_bigO_rankOne hE hk hM hcomp B hB
    (fun r => observer M B blk r) 424 fun r h₁ h₂ => ⟨isObserver_observer hE B hB blk r,
      observer_size_le hE B hB blk ((h₁.trans_lt h₂).le.trans hkm) hkm h₂⟩
  exact ⟨C, by omega, hCe⟩

end SignedTropical.Rainbow.TheoremCFinal
