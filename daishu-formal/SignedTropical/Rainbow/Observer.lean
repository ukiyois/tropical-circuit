import SignedTropical.Rainbow.ObserverOracle
import SignedTropical.Rainbow.MICircuit
import SignedTropical.Rainbow.GapUpdate

/-!
# The observer (Lemma `lem:observer`)

`greedy_intersection.tex`, Lemma `lem:observer`: from a Boolean circuit `C` of size `s` that
outputs the binary digits of the rank of `M` (the hypothesis of Theorem `thm:A`) and from
`r₀`, a Boolean circuit `observer M C blk r₀` on `m · m` inputs, input `i` the bit
`[pairOf i ∈ G]` (`GapUpdate.pairOf`, the pair indexing of `lem:oneupdate`), outputs the `k` bits
`F_b(G) = [ν(N_G) ≤ r₀] ∧ [b ∈ Av(N_G)]`, correct whenever `G = G_t`, `t ≥ 0`.

* Steps 1 to 3 (`Rainbow/ObserverOracle.lean`): the context of `G` (`ctxB_impl`) and the
  exchange tests of `N_G` (`locB_impl`, `locV_correct`), one rank run each.
* Step 4 (`Rainbow/MICircuit.lean`): `r₀ + 1` rounds of the augmenting path algorithm, one more
  exchange graph for `Av`, and the guard, with the exchange tests of Step 3 (`avGuardB_impl`,
  `avGuardV_eq`).  After `r₀ + 1` rounds the state has at least `min(r₀ + 1, ν)` elements, so
  `[|I| ≤ r₀] = [ν ≤ r₀]`, and when `ν ≤ r₀` it is a largest rainbow independent set.
* The input: the bits of `G` are read from the inputs `finProdFinEquiv (g, f)`, a free
  rearrangement (`inputRel`, `inputRel_pairOf`).
* `lem_observer`: the size (`obsCost`, exact), the explicit bound
  `(r₀+2)(m+1)²(s + 52(m+1)) + 3ms + 17m³ + 3k(m+1) + 1 + 5⌈log₂(r₀+1)⌉` (`obsCost_le`), the `k`
  outputs, their values at `G_t` for every `v` and `t ≥ 0`, and Step 5: at `G = E × E` every
  output is `0` when `M` has a rainbow base, `rank M = k` and `r₀ < k`.  `obsCost_le_bigO`: the
  size is at most `440 (r₀ + 2) m² (s + m)` for `1 ≤ m`, `k ≤ m` and `r₀ < k`.
-/

open Finset

namespace SignedTropical.Rainbow.Observer

open SignedTropical SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.POSL
  SignedTropical.Rainbow.MI

variable {m k n : ℕ} {M : Matroid (Fin m)} {C : Circuit BoolOp m}

/-! ### The input -/

/-- The bits of the relation read from the `m · m` inputs: `R g f` is the input with the pair
index `finProdFinEquiv (g, f)`, the inverse of `GapUpdate.pairOf`. -/
def inputRel (X : Fin (m * m) → Bool) : Fin m → Fin m → Bool :=
  fun g f => X (finProdFinEquiv (g, f))

/-- On the input vector of a relation `G` (input `i` the bit `[pairOf i ∈ G]`), the bits read
are the bits of `G`. -/
theorem inputRel_pairOf (G : Finset (Fin m × Fin m)) :
    inputRel (fun i => decide (GapUpdate.pairOf i ∈ G)) = relBits G := by
  funext g f
  simp [inputRel, relBits, GapUpdate.pairOf]

/-! ### The circuit -/

/-- The value of the observer at the input `X`: the bits `[|I| ≤ r₀] ∧ [b ∈ Av]` of the matroid
intersection circuit with `r₀ + 1` rounds, run with the exchange tests of
`Rainbow/ObserverOracle.lean` at the context of the relation read from `X`. -/
noncomputable def obsV (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r₀ : ℕ)
    (X : Fin (m * m) → Bool) (b : Fin k) : Bool :=
  (miV (fun y => locV M y) blk (r₀ + 1) r₀ (ctxV M (inputRel X))).2.2.1 &&
    (miV (fun y => locV M y) blk (r₀ + 1) r₀ (ctxV M (inputRel X))).2.2.2 b

/-- The builder of the observer: read the relation, compute its context (Steps 1 to 3), and run
the matroid intersection circuit with `r₀ + 1` rounds and the exchange tests (Step 4). -/
noncomputable def obsB (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : (Fin (m * m) → Arg n) → Bld BoolOp n (Fin k → Arg n) :=
  seqB (pureB fun x g f => x (finProdFinEquiv (g, f)))
    (seqB (ctxB M C) (avGuardB (locB C) blk (r₀ + 1) r₀))

/-- The gates of the observer: the context, the matroid intersection circuit with `r₀ + 1`
rounds and `locCost` gates per exchange test, and the `k` output gates. -/
def obsCost (m k s r₀ : ℕ) : ℕ :=
  ctxCost m s + (miCost m k (r₀ + 1) (locCost m s) r₀ + k)

/-- **The observer as an implementation**: from the `m · m` input bits, `obsB` computes
`obsV M blk r₀` with `obsCost m k s r₀` gates. -/
theorem obsB_impl
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    Impl (vecR (m * m)) (vecR (n := n) k) (obsB M C blk r₀) (obsCost m k C.size r₀)
      (obsV M blk r₀) :=
  ((Impl.free (R₁ := vecR (m * m)) (R₂ := relR m) (g := fun x g f => x (finProdFinEquiv (g, f)))
    (F := inputRel) fun _ _ _ hs _ _ => hs _).comp
    ((ctxB_impl hB).comp (avGuardB_impl (locB_impl hB) blk (r₀ + 1) r₀))).cost
    (by rw [obsCost, Nat.zero_add])

/-- **The observer circuit** of Lemma `lem:observer`, on the `m · m` inputs `[pairOf i ∈ G]`. -/
noncomputable def observer (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : Circuit BoolOp (m * m) :=
  vecCircuit (obsB M C blk r₀)

/-! ### The size -/

/-- **The size of the observer**, an explicit polynomial:
`obsCost m k s r₀ ≤ (r₀+2)(m+1)²(s + 52(m+1)) + 3ms + 17m³ + 3k(m+1) + 1 + 5⌈log₂(r₀+1)⌉`. -/
theorem obsCost_le (m k s r₀ : ℕ) :
    obsCost m k s r₀ ≤ (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1)) + 3 * m * s + 17 * m ^ 3 +
      3 * k * (m + 1) + 1 + 5 * Nat.size r₀ := by
  have h₁ := miCost_add_le m k (r₀ + 1) (locCost m s) r₀
  have h₂ : (r₀ + 1 + 1) * (m + 1) ^ 2 * (locCost m s + 10 * (m + 1)) ≤
      (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1)) :=
    Nat.mul_le_mul_left _ (by have := locCost_le m s; omega)
  have h₃ := ctxCost_le m s
  unfold obsCost
  omega

/-- **The size of the observer is `O((r₀ + 2) m² (s + m))`**: for `1 ≤ m`, `k ≤ m` and
`r₀ < k`, at most `440 (r₀ + 2) m² (s + m)`. -/
theorem obsCost_le_bigO {m k s r₀ : ℕ} (hm : 1 ≤ m) (hkm : k ≤ m) (hr : r₀ < k) :
    obsCost m k s r₀ ≤ 440 * ((r₀ + 2) * m ^ 2 * (s + m)) := by
  have hX : 1 ≤ s + m := by omega
  have hm2 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  have hY : m ^ 2 ≤ m ^ 2 * (s + m) := Nat.le_mul_of_pos_right _ hX
  -- the leading term
  have h₁ : (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1)) ≤
      416 * ((r₀ + 2) * m ^ 2 * (s + m)) := by
    have a : (m + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
    have b : s + 52 * (m + 1) ≤ 104 * (s + m) := by omega
    calc (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1))
        ≤ (r₀ + 2) * (4 * m ^ 2) * (104 * (s + m)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a) b
      _ = 416 * ((r₀ + 2) * m ^ 2 * (s + m)) := by ring
  -- the other terms are at most `32 m² (s + m) ≤ 16 (r₀ + 2) m² (s + m)`
  have h₂ : 3 * m * s + 17 * m ^ 3 + 3 * k * (m + 1) + 1 + 5 * Nat.size r₀ ≤
      32 * (m ^ 2 * (s + m)) := by
    have a : m * s ≤ m ^ 2 * (s + m) := by
      calc m * s ≤ m ^ 2 * s := Nat.mul_le_mul_right s hm2
        _ ≤ m ^ 2 * (s + m) := Nat.mul_le_mul_left _ (Nat.le_add_right s m)
    have b : m ^ 3 ≤ m ^ 2 * (s + m) := by
      calc m ^ 3 = m ^ 2 * m := by ring
        _ ≤ m ^ 2 * (s + m) := Nat.mul_le_mul_left _ (Nat.le_add_left m s)
    have c : 3 * k * (m + 1) ≤ 6 * m ^ 2 := by nlinarith
    have d : Nat.size r₀ ≤ m := (size_le_self r₀).trans (by omega)
    have e : 3 * m * s = 3 * (m * s) := Nat.mul_assoc 3 m s
    omega
  have h₃ : 32 * (m ^ 2 * (s + m)) ≤ 16 * ((r₀ + 2) * m ^ 2 * (s + m)) := by
    have := Nat.mul_le_mul_right (m ^ 2 * (s + m)) (show 2 ≤ r₀ + 2 by omega)
    nlinarith
  have := obsCost_le m k s r₀
  omega

/-! ### Lemma `lem:observer` -/

/-- **Lemma `lem:observer`.**  Let `M` be a matroid on `E = Fin m` with ground set `E`, `blk`
the blocks, and let the Boolean circuit `C` of size `s` output the binary digits of the rank of
`M`.  For every `r₀`, the Boolean circuit `observer M C blk r₀` on the `m · m` inputs
`[pairOf i ∈ G]`, `G ⊆ E × E`:

1. has `obsCost m k s r₀ ≤ (r₀+2)(m+1)²(s + 52(m+1)) + 3ms + 17m³ + 3k(m+1) + 1 +
   5⌈log₂(r₀+1)⌉` gates (`O((r₀ + 2) m² (s + m))`, `obsCost_le_bigO`);
2. has `k` outputs;
3. for every `v` and every `t ≥ 0`, outputs at `G = G_t` the bits
   `F_b(G_t) = [ν(N_{G_t}) ≤ r₀] ∧ [b ∈ Av(N_{G_t})]`, `b = 0, …, k - 1`;
4. (Step 5) outputs `0` at `G = E × E` when `M` has a rainbow base, `rank M = k` and `r₀ < k`. -/
theorem lem_observer (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    (observer M C blk r₀).size = obsCost m k C.size r₀ ∧
      (observer M C blk r₀).size ≤ (r₀ + 2) * (m + 1) ^ 2 * (C.size + 52 * (m + 1)) +
        3 * m * C.size + 17 * m ^ 3 + 3 * k * (m + 1) + 1 + 5 * Nat.size r₀ ∧
      (observer M C blk r₀).outs.length = k ∧
      (∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        (observer M C blk r₀).eval boolInterp (fun i => decide (GapUpdate.pairOf i ∈ Gt v t)) =
          List.ofFn fun b : Fin k =>
            decide (nu (NG M (Gt v t)) blk ≤ r₀ ∧ b ∈ Av (NG M (Gt v t)) blk)) ∧
      ((∃ B, IsRainbowBase M blk B) → rank M = k → r₀ < k →
        (observer M C blk r₀).eval boolInterp
            (fun i => decide (GapUpdate.pairOf i ∈ (univ : Finset (Fin m × Fin m)))) =
          List.replicate k false) := by
  obtain ⟨hsize, hlen, heval⟩ := vecCircuit_spec (obsB_impl (n := m * m) hB blk r₀)
  have hG : ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
      (observer M C blk r₀).eval boolInterp (fun i => decide (GapUpdate.pairOf i ∈ Gt v t)) =
        List.ofFn fun b : Fin k =>
          decide (nu (NG M (Gt v t)) blk ≤ r₀ ∧ b ∈ Av (NG M (Gt v t)) blk) := by
    intro v t ht
    rw [observer, heval]
    congr 1
    funext b
    rw [obsV, inputRel_pairOf, avGuardV_eq (locV_correct hE ht) (Nat.lt_succ_self r₀) b,
      Bool.decide_and]
  refine ⟨hsize, hsize.trans_le (obsCost_le _ _ _ _), hlen, hG, fun hM hk hr => ?_⟩
  have hu : Gt (0 : Fin m → ℝ) 0 = univ := Gt_eq_univ fun _ _ => by simp
  have h := hG 0 0 le_rfl
  rw [hu, NG_univ hE, (nu_eq_iff hk).2 hM] at h
  rw [h, ← List.ofFn_const]
  congr 1
  funext b
  simp [Nat.not_le.2 hr]

end SignedTropical.Rainbow.Observer
