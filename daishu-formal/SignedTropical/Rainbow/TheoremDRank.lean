import SignedTropical.BoolAlg.Count
import SignedTropical.Rainbow.Doubling
import SignedTropical.Rainbow.Truncation

/-!
# Theorem D: the rank circuits

`greedy_intersection.tex`, proof of Theorem `thm:D`, Steps 2 and 4: Boolean rank circuits of the
doubled matroid `N = M₁ ⊕ M₂✶` of Lemma `lem:doubling` and of truncations, built on top of
Boolean rank circuits `C₁`, `C₂` of `M₁`, `M₂` (matroids on `E = Fin m` with ground set `univ`).
A rank circuit of `M` outputs `r(S)` in binary from the indicator vector of every `S`, the
hypothesis of Theorem A (`theoremA`).  Gate counts are exact; `W = ⌈log₂(m+1)⌉` is
`Nat.size m`, and `popCost m ≤ 22 m` is the size of a population count of `m` bits.

* Rank queries (`queryB`): run a rank circuit and keep `W` outputs, which carry the rank, since
  `r(S) ≤ m < 2^W` (`rk_lt_two_pow`).
* The dual part (`dualB`): `r₂✶(B) = |B| + r₂(E \ B) - r₂(E)` from the indicator vector of `B`,
  by a population count, `m` negations feeding `E \ B` to `C₂`, an addition and the subtraction
  of the constant `r₂(E)`.
* **Step 2** (`doubleRankCircuit`, `doubleRankCircuit_rank`, `double_rankCircuit`): the rank
  circuit of `N` on the `m + m` inputs `E × {1, 2}`, computing
  `r_N(A × {1} ∪ B × {2}) = r₁(A) + |B| + r₂(E \ B) - r₂(E)` (`Doubling.rk_pair_eq_sub`), with
  exactly `s₁ + s₂ + m + popCost m + 35 W + 15 ≤ s₁ + s₂ + 58 m + 15` gates.
* The truncation (`truncRankCircuit`, `truncRankCircuit_rank`): the rank circuit of the
  truncation at `j`, whose rank function is `min(r, j)` (`Trunc.rk_truncate`): a rank query, a
  comparison with `j` and a selection on `W` bits, exactly `s + 8 W + 3` gates for `j ≤ m`.
* **Step 4, the padded matroid** (`pad`, `isBase_pad_iff`, `padRankCircuit`,
  `padRankCircuit_rank`): `pad M = (M ⊕ U_{m,m})|_{≤m}` on `E × {1, 2}`, written
  `truncate (double M (loops m)) m` with `loops m` the matroid of loops, whose dual is free.  Its
  bases are the sets of `m` elements whose first copies are independent in `M`, and its rank
  circuit `min(r(A) + |B|, m)` has at most `s + 74 m + 18` gates.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremD

open SignedTropical.BoolAlg SignedTropical.Rainbow.Doubling SignedTropical.Rainbow.Trunc

variable {m n : ℕ}

/-! ### Ranks

`rk_le_card`, `rank_le_card` (`Matroid.lean`) and `rk_lt_two_pow` (`TheoremA.lean`) bound the
ranks. -/

/-- The hypothesis of Theorem A, read in `ℕ`: the circuit outputs `r(S)`. -/
theorem bitsVal_eq_rk {M : Matroid (Fin m)} {C : Circuit BoolOp m}
    (hC : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (S : Finset (Fin m)) : bitsVal (C.eval boolInterp (indicator S)) = rk M S :=
  Nat.cast_injective ((hC S).trans (coe_rk M S).symm)

/-! ### Rank queries -/

/-- A rank query: run `C` and keep `⌈log₂(m+1)⌉` outputs. -/
def queryB (C : Circuit BoolOp m) : (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (runB C) (pureB (fit (Nat.size m)))

/-- `queryB C` carries the output of `C` modulo `2 ^ ⌈log₂(m+1)⌉`, with `C.size` gates. -/
theorem queryB_impl (C : Circuit BoolOp m) :
    Impl (vecR m) (numR (n := n) (Nat.size m)) (queryB C) C.size
      (fun V => bitsVal (C.eval boolInterp V) % 2 ^ Nat.size m) :=
  ((runB_num C).comp numFit_impl).cost (Nat.add_zero _)

/-! ### The dual part: `r₂✶(B) = |B| + r₂(E \ B) - r₂(E)` -/

/-- `|B| + r₂(E \ B) - k₂` from the indicator vector of `B`: a population count, `m` negations
feeding `E \ B` to the rank query, an addition and the subtraction of the constant `k₂`. -/
def dualB (C₂ : Circuit BoolOp m) (k₂ : ℕ) : (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (seqB (pairB vecPopcountB (seqB vecNotB (queryB C₂))) numAddB) (numSubConstB k₂)

/-- `dualB C₂ k₂` on `⌈log₂(m+1)⌉ + 1` bits, with
`m + s₂ + popCost m + 11 W + 12 max(W + 1, ⌈log₂(k₂+1)⌉) + W + 3` gates. -/
theorem dualB_impl (C₂ : Circuit BoolOp m) (k₂ : ℕ) :
    Impl (vecR m) (numR (n := n) (Nat.size m + 1)) (dualB C₂ k₂)
      (m + C₂.size + popCost m + 11 * Nat.size m
        + (12 * max (Nat.size m + 1) (Nat.size k₂) + Nat.size m + 3))
      (fun V => (univ.filter fun i => V i = true).card
        + bitsVal (C₂.eval boolInterp fun i => !V i) % 2 ^ Nat.size m - k₂) := by
  have hadd := numAddB_impl (n := n) (Nat.size m) (Nat.size m)
  rw [max_self] at hadd
  exact (((vecPopcountB_impl.pair (vecNotB_impl.comp (queryB_impl C₂))).comp hadd).comp
    (numSubConstB_impl k₂ (Nat.size m + 1))).cost (by ring)

/-! ### Step 2: the rank circuit of `N = M₁ ⊕ M₂✶` -/

/-- `r₁(A) + r₂✶(B)` from the indicator vector of `A × {1} ∪ B × {2}`: a rank query on the
first copies, the dual part on the second copies, and an addition. -/
def doubleB (C₁ C₂ : Circuit BoolOp m) (k₂ : ℕ) :
    (Fin (m + m) → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (pairB (fun v => queryB C₁ fun e => v (Fin.castAdd m e))
    (fun v => seqB (dualB C₂ k₂) (pureB (fit (Nat.size m))) fun e => v (Fin.addNat e m)))
    numAddB

/-- `doubleB C₁ C₂ k₂` on `⌈log₂(m+1)⌉ + 1` bits, with
`s₁ + s₂ + m + popCost m + 23 W + 12 max(W + 1, ⌈log₂(k₂+1)⌉) + 3` gates. -/
theorem doubleB_impl (C₁ C₂ : Circuit BoolOp m) (k₂ : ℕ) :
    Impl (vecR (m + m)) (numR (n := n) (Nat.size m + 1)) (doubleB C₁ C₂ k₂)
      (C₁.size + C₂.size + m + popCost m + 23 * Nat.size m
        + 12 * max (Nat.size m + 1) (Nat.size k₂) + 3)
      (fun V => bitsVal (C₁.eval boolInterp fun e => V (Fin.castAdd m e)) % 2 ^ Nat.size m
        + ((univ.filter fun e => V (Fin.addNat e m) = true).card
          + bitsVal (C₂.eval boolInterp fun e => !V (Fin.addNat e m)) % 2 ^ Nat.size m - k₂)
          % 2 ^ Nat.size m) := by
  have hadd := numAddB_impl (n := n) (Nat.size m) (Nat.size m)
  rw [max_self] at hadd
  have h₁ := (queryB_impl (n := n) C₁).pre (R := vecR (m + m))
    (g := fun v e => v (Fin.castAdd m e)) (G := fun V e => V (Fin.castAdd m e))
    fun _ _ _ hs _ => hs _
  have h₂ := ((dualB_impl (n := n) C₂ k₂).comp (numFit_impl (W := Nat.size m))).pre
    (R := vecR (m + m)) (g := fun v e => v (Fin.addNat e m))
    (G := fun V e => V (Fin.addNat e m)) fun _ _ _ hs _ => hs _
  exact ((h₁.pair h₂).comp hadd).cost (by ring)

/-- **The rank circuit of the doubled matroid** (Theorem `thm:D`, Step 2), for rank circuits
`C₁`, `C₂` of `M₁`, `M₂` and the rank `k₂ = r₂(E)`. -/
def doubleRankCircuit (C₁ C₂ : Circuit BoolOp m) (k₂ : ℕ) : Circuit BoolOp (m + m) :=
  circuitOf (doubleB C₁ C₂ k₂)

/-- The size of `doubleRankCircuit`, its `⌈log₂(m+1)⌉ + 1` outputs, and what it computes. -/
theorem doubleRankCircuit_spec (C₁ C₂ : Circuit BoolOp m) (k₂ : ℕ) :
    (doubleRankCircuit C₁ C₂ k₂).size = C₁.size + C₂.size + m + popCost m + 23 * Nat.size m
        + 12 * max (Nat.size m + 1) (Nat.size k₂) + 3 ∧
      (doubleRankCircuit C₁ C₂ k₂).outs.length = Nat.size m + 1 ∧
      ∀ x : Fin (m + m) → Bool, bitsVal ((doubleRankCircuit C₁ C₂ k₂).eval boolInterp x)
        = bitsVal (C₁.eval boolInterp fun e => x (Fin.castAdd m e)) % 2 ^ Nat.size m
          + ((univ.filter fun e => x (Fin.addNat e m) = true).card
            + bitsVal (C₂.eval boolInterp fun e => !x (Fin.addNat e m)) % 2 ^ Nat.size m - k₂)
            % 2 ^ Nat.size m :=
  circuitOf_num (doubleB_impl C₁ C₂ k₂)

/-- For `k₂ ≤ m`, `doubleRankCircuit` has `s₁ + s₂ + m + popCost m + 35 ⌈log₂(m+1)⌉ + 15`
gates. -/
theorem doubleRankCircuit_size {k₂ : ℕ} (hk : k₂ ≤ m) (C₁ C₂ : Circuit BoolOp m) :
    (doubleRankCircuit C₁ C₂ k₂).size
      = C₁.size + C₂.size + m + popCost m + 35 * Nat.size m + 15 := by
  have h := Nat.size_le_size hk
  rw [(doubleRankCircuit_spec C₁ C₂ k₂).1, max_eq_left (by omega)]
  ring

/-- For `k₂ ≤ m`, `doubleRankCircuit` has at most `s₁ + s₂ + 58 m + 15` gates. -/
theorem doubleRankCircuit_size_le {k₂ : ℕ} (hk : k₂ ≤ m) (C₁ C₂ : Circuit BoolOp m) :
    (doubleRankCircuit C₁ C₂ k₂).size ≤ C₁.size + C₂.size + 58 * m + 15 := by
  rw [doubleRankCircuit_size hk]
  have h₁ := popCost_le m
  have h₂ := size_le_self m
  omega

variable {M M₁ M₂ : Matroid (Fin m)} {C C₁ C₂ : Circuit BoolOp m}

/-- **`doubleRankCircuit` computes the rank function of `N = M₁ ⊕ M₂✶`** (Theorem `thm:D`,
Step 2): `r_N(A × {1} ∪ B × {2}) = r₁(A) + |B| + r₂(E \ B) - r₂(E)`. -/
theorem doubleRankCircuit_rank (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m)))
    (S : Finset (Fin (m + m))) :
    (bitsVal ((doubleRankCircuit C₁ C₂ (rank M₂)).eval boolInterp (indicator S)) : ℕ∞)
      = (double M₁ M₂).eRk (S : Set (Fin (m + m))) := by
  have h₁ : (fun e => indicator S (Fin.castAdd m e)) = indicator (fst S) := by
    funext e
    simp [indicator]
  have h₂ : (fun e => !indicator S (Fin.addNat e m)) = indicator (univ \ snd S) := by
    funext e
    simp [indicator]
  have h₃ : (univ.filter fun e => indicator S (Fin.addNat e m) = true) = snd S := by
    ext e
    simp [indicator]
  have hd := rk_dual_add_rank hE₂ (snd S)
  have hd' : #(snd S) + rk M₂ (univ \ snd S) - rank M₂ = rk M₂✶ (snd S) := by omega
  rw [(doubleRankCircuit_spec C₁ C₂ (rank M₂)).2.2, h₁, h₂, h₃, bitsVal_eq_rk hC₁,
    bitsVal_eq_rk hC₂, Nat.mod_eq_of_lt (rk_lt_two_pow M₁ _),
    Nat.mod_eq_of_lt (rk_lt_two_pow M₂ _), hd', Nat.mod_eq_of_lt (rk_lt_two_pow M₂✶ _),
    ← rk_pair_eq_add hE₁ hE₂, pair_fst_snd, coe_rk]

/-- **Theorem `thm:D`, Step 2.**  Let `M₁`, `M₂` be matroids on `E = Fin m` (ground set `univ`)
and let Boolean circuits `C₁`, `C₂` of sizes `s₁`, `s₂` output `r₁(S)`, `r₂(S)` in binary from
the indicator vector of every `S ⊆ E`.  Then a Boolean circuit of size
`s₁ + s₂ + m + popCost m + 35 ⌈log₂(m+1)⌉ + 15 ≤ s₁ + s₂ + 58 m + 15` outputs in binary the rank
in `N = M₁ ⊕ M₂✶` of every `S ⊆ E × {1, 2}` from its indicator vector. -/
theorem double_rankCircuit (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (hC₁ : ∀ S : Finset (Fin m),
      (bitsVal (C₁.eval boolInterp (indicator S)) : ℕ∞) = M₁.eRk (S : Set (Fin m)))
    (hC₂ : ∀ S : Finset (Fin m),
      (bitsVal (C₂.eval boolInterp (indicator S)) : ℕ∞) = M₂.eRk (S : Set (Fin m))) :
    ∃ C : Circuit BoolOp (m + m),
      C.size = C₁.size + C₂.size + m + popCost m + 35 * Nat.size m + 15 ∧
      C.size ≤ C₁.size + C₂.size + 58 * m + 15 ∧
      ∀ S : Finset (Fin (m + m)), (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞)
        = (double M₁ M₂).eRk (S : Set (Fin (m + m))) :=
  ⟨doubleRankCircuit C₁ C₂ (rank M₂), doubleRankCircuit_size (rank_le_card M₂) C₁ C₂,
    doubleRankCircuit_size_le (rank_le_card M₂) C₁ C₂, doubleRankCircuit_rank hE₁ hE₂ hC₁ hC₂⟩

/-! ### Step 4: the rank circuit of a truncation -/

/-- `min(r(T), j)`: a rank query, then a comparison with the constant `j` and a selection
(`numMinConstB`). -/
def truncB (C : Circuit BoolOp m) (j : ℕ) : (Fin m → Arg n) → Bld BoolOp n (List (Arg n)) :=
  seqB (queryB C) (numMinConstB j)

/-- `truncB C j` on `max(W, ⌈log₂(j+1)⌉)` bits, with `C.size + 8 max(W, ⌈log₂(j+1)⌉) + 3`
gates. -/
theorem truncB_impl (C : Circuit BoolOp m) (j : ℕ) :
    Impl (vecR m) (numR (n := n) (max (Nat.size m) (Nat.size j))) (truncB C j)
      (C.size + (8 * max (Nat.size m) (Nat.size j) + 3))
      (fun V => min (bitsVal (C.eval boolInterp V) % 2 ^ Nat.size m) j) :=
  (queryB_impl C).comp (numMinConstB_impl j (Nat.size m))

/-- **The rank circuit of the truncation at `j`** (Theorem `thm:D`, Step 4), for a rank circuit
`C` of `M`. -/
def truncRankCircuit (C : Circuit BoolOp m) (j : ℕ) : Circuit BoolOp m :=
  circuitOf (truncB C j)

/-- The size of `truncRankCircuit`, its `max(⌈log₂(m+1)⌉, ⌈log₂(j+1)⌉)` outputs, and what it
computes. -/
theorem truncRankCircuit_spec (C : Circuit BoolOp m) (j : ℕ) :
    (truncRankCircuit C j).size = C.size + 8 * max (Nat.size m) (Nat.size j) + 3 ∧
      (truncRankCircuit C j).outs.length = max (Nat.size m) (Nat.size j) ∧
      ∀ x : Fin m → Bool, bitsVal ((truncRankCircuit C j).eval boolInterp x)
        = min (bitsVal (C.eval boolInterp x) % 2 ^ Nat.size m) j := by
  obtain ⟨h₁, h₂, h₃⟩ := circuitOf_num (truncB_impl (n := m) C j)
  exact ⟨h₁.trans (Nat.add_assoc _ _ _).symm, h₂, h₃⟩

/-- For `j ≤ m`, `truncRankCircuit C j` has `C.size + 8 ⌈log₂(m+1)⌉ + 3` gates. -/
theorem truncRankCircuit_size {j : ℕ} (hj : j ≤ m) (C : Circuit BoolOp m) :
    (truncRankCircuit C j).size = C.size + 8 * Nat.size m + 3 := by
  rw [(truncRankCircuit_spec C j).1, max_eq_left (Nat.size_le_size hj)]

/-- **`truncRankCircuit` computes the rank function `min(r, j)` of the truncation at `j`**
(Theorem `thm:D`, Step 4). -/
theorem truncRankCircuit_rank (hE : M.E = Set.univ)
    (hC : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (j : ℕ) (S : Finset (Fin m)) :
    (bitsVal ((truncRankCircuit C j).eval boolInterp (indicator S)) : ℕ∞)
      = (truncate M j).eRk (S : Set (Fin m)) := by
  rw [(truncRankCircuit_spec C j).2.2, bitsVal_eq_rk hC, Nat.mod_eq_of_lt (rk_lt_two_pow M S),
    ← rk_truncate hE, coe_rk]

/-! ### Step 4: the padded matroids -/

/-- The matroid on `E` whose elements are all loops; its dual is free. -/
noncomputable def loops (m : ℕ) : Matroid (Fin m) := Matroid.loopyOn Set.univ

@[simp] theorem loops_E : (loops m).E = Set.univ := rfl

/-- `loops m` has rank `0`. -/
theorem rank_loops : rank (loops m) = 0 := by
  simp [rank, loops]

/-- **The padded matroid** of `M` on `E × {1, 2}`: `M` on the first copies, every set of second
copies independent (`double M (loops m)`, as `(loops m)✶` is free), truncated at `m`.  At
`A × {1} ∪ B × {2}` its rank is `min(r(A) + |B|, m)`. -/
noncomputable def pad (M : Matroid (Fin m)) : Matroid (Fin (m + m)) :=
  truncate (double M (loops m)) m

/-- A set of `M ⊕ U_{m,m}` is independent iff its first copies are independent in `M`. -/
theorem indep_double_loops (S : Finset (Fin (m + m))) :
    (double M (loops m)).Indep (S : Set (Fin (m + m))) ↔ M.Indep (fst S : Set (Fin m)) := by
  rw [double, Matroid.mapEquiv_indep_iff, Matroid.sum_indep_iff, preimage_inl_image_symm,
    preimage_inr_image_symm, loops, Matroid.loopyOn_dual_eq, Matroid.freeOn_indep_iff, coe_fst]
  simp

/-- `M ⊕ U_{m,m}` has rank `r(E) + m`. -/
theorem rank_double_loops (hE : M.E = Set.univ) : rank (double M (loops m)) = rank M + m := by
  have h := rank_double (M₂ := loops m) hE loops_E
  rw [rank_loops] at h
  omega

/-- **The bases of the padded matroid** are the sets of `m` elements whose first copies are
independent in `M`. -/
theorem isBase_pad_iff (hE : M.E = Set.univ) (S : Finset (Fin (m + m))) :
    (pad M).IsBase (S : Set (Fin (m + m))) ↔ M.Indep (fst S : Set (Fin m)) ∧ #S = m := by
  rw [pad, isBase_truncate_iff (double_ground hE loops_E)
    (by rw [rank_double_loops hE]; omega), indep_double_loops]

/-- The rank circuit of `loops m`: no gates and no outputs, which read as the number `0`. -/
def zeroCircuit (m : ℕ) : Circuit BoolOp m := ⟨[], []⟩

/-- `zeroCircuit m` outputs the rank `0` of every set in `loops m`. -/
theorem zeroCircuit_rank (S : Finset (Fin m)) :
    (bitsVal ((zeroCircuit m).eval boolInterp (indicator S)) : ℕ∞) =
      (loops m).eRk (S : Set (Fin m)) := by
  simp [zeroCircuit, Circuit.eval, loops]

/-- **The rank circuit of the padded matroid** (Theorem `thm:D`, Step 4), for a rank circuit `C`
of `M`: the rank circuit of `double M (loops m)` (`r(A) + |B|`), then the truncation at `m`. -/
def padRankCircuit (C : Circuit BoolOp m) : Circuit BoolOp (m + m) :=
  truncRankCircuit (doubleRankCircuit C (zeroCircuit m) 0) m

/-- `padRankCircuit C` has `s + m + popCost m + 35 ⌈log₂(m+1)⌉ + 8 ⌈log₂(2m+1)⌉ + 18` gates. -/
theorem padRankCircuit_size (C : Circuit BoolOp m) :
    (padRankCircuit C).size =
      C.size + m + popCost m + 35 * Nat.size m + 8 * Nat.size (m + m) + 18 := by
  rw [padRankCircuit, truncRankCircuit_size (by omega), doubleRankCircuit_size (Nat.zero_le m)]
  simp only [zeroCircuit, Circuit.size, List.length_nil]
  ring

/-- `padRankCircuit C` has at most `s + 74 m + 18` gates. -/
theorem padRankCircuit_size_le (C : Circuit BoolOp m) :
    (padRankCircuit C).size ≤ C.size + 74 * m + 18 := by
  rw [padRankCircuit_size]
  have h₁ := popCost_le m
  have h₂ := size_le_self m
  have h₃ := size_le_self (m + m)
  omega

/-- **`padRankCircuit` computes the rank function of the padded matroid** (Theorem `thm:D`,
Step 4). -/
theorem padRankCircuit_rank (hE : M.E = Set.univ)
    (hC : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (S : Finset (Fin (m + m))) :
    (bitsVal ((padRankCircuit C).eval boolInterp (indicator S)) : ℕ∞)
      = (pad M).eRk (S : Set (Fin (m + m))) :=
  truncRankCircuit_rank (double_ground hE loops_E) (fun S => by
    have h := doubleRankCircuit_rank hE loops_E hC zeroCircuit_rank S
    rwa [rank_loops] at h) m S

end SignedTropical.Rainbow.TheoremD
