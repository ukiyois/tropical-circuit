import SignedTropical.Rainbow.Observer
import SignedTropical.Rainbow.TheoremC

/-!
# Theorem C, unconditional

`greedy_intersection.tex`, Theorem `thm:C`: if a Boolean circuit of size `s` outputs the binary
digits of the rank of `M` and `M` has a rainbow base, then a signed tropical circuit of size
`O(k⁴ m⁶ (s + m))` computes `Opt(w)` at every `w`.

The proof of agent P7 (`Rainbow/TheoremC.lean`, `TheoremC.theoremC`, `TheoremC.theoremC_bigO`)
takes the observers of Lemma `lem:observer` as a hypothesis (`TheoremC.IsObserver`).  Here the
observer circuits of `Rainbow/Observer.lean` discharge it:

* `isObserver_observer`: `observer M B blk r` satisfies `TheoremC.IsObserver M blk r`, for every
  `r`;
* `observer_size_le`: its size is at most `800 k m³ (s + m)` for `m ≥ 1` and `r < k`;
* `theoremC_final`: Theorem `thm:C` with the explicit bound `2436 k⁴ m⁶ (s + m) + 2`;
  `theoremC_final_poly`: the same with the explicit polynomial bound of `TheoremC.theoremC`, whose
  number of rounds `Schedule.rounds k m` is at most both `(⌊m²/4⌋ + 1) k(k-1)/2` and `k³ m`;
* `theoremC_final_rankOne`: when every component of `M` has rank at most one (every circuit has
  at most two elements; Corollary `cor:rankone`), the bound `2436 k³ m⁵ (s + m) + 2`.
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
  (lem_observer hE hB blk r).2.2.2.1

/-- **The size of the observer in the form of `TheoremC.theoremC_bigO`**: for `m ≥ 1` and
`r < k`, at most `800 k m³ (s + m)`. -/
theorem observer_size_le (hE : M.E = Set.univ) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) {r : ℕ} (hm : 1 ≤ m) (hr : r < k) :
    (observer M B blk r).size ≤ 800 * (k * m ^ 3 * (B.size + m)) :=
  (lem_observer hE hB blk r).1 ▸ obsCost_le_bigO hm hr

/-- **Theorem `thm:C`.**  Let `M` be a matroid on `E = Fin m` with ground set `E` and rank `k`,
with a rainbow base for the blocks `blk`, and let the Boolean circuit `B` of size `s` output the
binary digits of the rank of `M`.  Then a signed tropical circuit of size at most
`2436 k⁴ m⁶ (s + m) + 2` computes `Opt(w)` at every `w ∈ ℝ^E`. -/
theorem theoremC_final (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m, C.size ≤ 2436 * (k ^ 4 * m ^ 6 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  TheoremC.theoremC_bigO hE hk hM B hB (fun r => observer M B blk r) 800 fun r h₁ h₂ =>
    ⟨isObserver_observer hE B hB blk r, observer_size_le hE B hB blk
      ((h₁.trans_lt h₂).le.trans (hk ▸ rank_le_card M)) h₂⟩

/-- **Theorem `thm:C`, with the explicit polynomial of `TheoremC.theoremC`**: the observers have
at most `sO = (k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(k+1)⌉` gates. -/
theorem theoremC_final_poly (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m,
      C.size ≤ Schedule.rounds k m *
          (3 * m ^ 2 * ((k + 1) * (m + 1) ^ 2 * (m * B.size + 70 * m ^ 2 + 10 * m + 11) +
            3 * m * B.size + 21 * m ^ 3 + 1 + 5 * Nat.size k) +
            k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) +
        (3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  TheoremC.theoremC hE hk hM B hB (fun r => observer M B blk r) _ fun r _ h₂ =>
    ⟨isObserver_observer hE B hB blk r, (lem_observer hE hB blk r).2.1.trans (by
      have := Nat.size_le_size h₂.le
      omega)⟩

/-- **Theorem `thm:C` for components of rank one** (Corollary `cor:rankone`).  Under the hypotheses
of `theoremC_final`, if every circuit of `M` has at most two elements (every component has rank
at most one; the assignment problem is the case of a partition matroid with unit capacities),
then a signed tropical circuit of size at most `2436 k³ m⁵ (s + m) + 2` computes `Opt(w)` at
every `w ∈ ℝ^E`. -/
theorem theoremC_final_rankOne (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hpar : ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    ∃ C : Circuit STOp m, C.size ≤ 2436 * (k ^ 3 * m ^ 5 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  TheoremC.theoremC_bigO_rankOne hE hk hM hpar B hB (fun r => observer M B blk r) 800
    fun r h₁ h₂ => ⟨isObserver_observer hE B hB blk r, observer_size_le hE B hB blk
      ((h₁.trans_lt h₂).le.trans (hk ▸ rank_le_card M)) h₂⟩

end SignedTropical.Rainbow.TheoremCFinal
