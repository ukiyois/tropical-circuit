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
  independence oracle of `N_G` (`oracleB_impl`, `oracle_correct`).
* Step 4 (`Rainbow/MICircuit.lean`, agent P6b): `k` rounds of the augmenting path algorithm, one
  more exchange graph for `Av`, and the guard, with the oracle of Step 3 (`avGuardB_impl`,
  `avGuardV_eq`).
* The input: the bits of `G` are read from the inputs `finProdFinEquiv (g, f)`, a free
  rearrangement (`inputRel`, `inputRel_pairOf`).
* `lem_observer`: the size (`obsCost`, exact), the explicit bound
  `(k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(r₀+1)⌉` (`obsCost_le`), the `k`
  outputs, their values at `G_t` for every `v` and `t ≥ 0`, and Step 5: at `G = E × E` every output
  is `0` when `M` has a rainbow base, `rank M = k` and `r₀ < k`.  `obsCost_le_bigO`: the size is
  at most `800 k m³ (s + m)` for `m ≥ 1` and `r₀ < k`.
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
intersection circuit, run with the oracle of `Rainbow/ObserverOracle.lean` at the context of the
relation read from `X`. -/
noncomputable def obsV (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r₀ : ℕ)
    (X : Fin (m * m) → Bool) (b : Fin k) : Bool :=
  (miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M (inputRel X))).2.2.1 &&
    (miV (fun P => oracleV M P.1 P.2) blk r₀ (ctxV M (inputRel X))).2.2.2 b

/-- The builder of the observer: read the relation, compute its context (Steps 1 to 3), and run
the matroid intersection circuit with the oracle (Step 4). -/
noncomputable def obsB (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : (Fin (m * m) → Arg n) → Bld BoolOp n (Fin k → Arg n) :=
  seqB (pureB fun x g f => x (finProdFinEquiv (g, f)))
    (seqB (ctxB M C) (avGuardB (oracleB C) blk r₀))

/-- The gates of the observer: the context, the matroid intersection circuit with `oracleCost`
gates per query, and the `k` output gates. -/
def obsCost (m k s r₀ : ℕ) : ℕ :=
  ctxCost m s + (miCost m k (oracleCost m s) r₀ + k)

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
    ((ctxB_impl hB).comp (avGuardB_impl (oracleB_impl hB) blk r₀))).cost
    (by rw [obsCost, Nat.zero_add])

/-- **The observer circuit** of Lemma `lem:observer`, on the `m · m` inputs `[pairOf i ∈ G]`. -/
noncomputable def observer (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : Circuit BoolOp (m * m) :=
  vecCircuit (obsB M C blk r₀)

/-! ### The size -/

/-- **The size of the observer**, an explicit polynomial:
`obsCost m k s r₀ ≤ (k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(r₀+1)⌉`. -/
theorem obsCost_le (m k s r₀ : ℕ) :
    obsCost m k s r₀ ≤ (k + 1) * (m + 1) ^ 2 * (m * s + 70 * m ^ 2 + 10 * m + 11) +
      3 * m * s + 21 * m ^ 3 + 1 + 5 * Nat.size r₀ := by
  have h₁ := miCost_add_le m k (oracleCost m s) r₀
  have h₂ : (k + 1) * (m + 1) ^ 2 * (oracleCost m s + 10 * (m + 1)) ≤
      (k + 1) * (m + 1) ^ 2 * (m * s + 70 * m ^ 2 + 10 * m + 11) :=
    Nat.mul_le_mul_left _ (by have := oracleCost_le m s; omega)
  have h₃ := ctxCost_le m s
  unfold obsCost
  omega

/-- **The size of the observer is `O(k m³ (s + m))`**: for `m ≥ 1` and `r₀ < k`, at most
`800 k m³ (s + m)`. -/
theorem obsCost_le_bigO {m k s r₀ : ℕ} (hm : 1 ≤ m) (hr : r₀ < k) :
    obsCost m k s r₀ ≤ 800 * (k * m ^ 3 * (s + m)) := by
  have hk : 1 ≤ k := by omega
  have hX : 1 ≤ k * m ^ 3 * (s + m) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have hm3 : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h₁ : (k + 1) * (m + 1) ^ 2 * (m * s + 70 * m ^ 2 + 10 * m + 11) ≤
      728 * (k * m ^ 3 * (s + m)) := by
    have a : k + 1 ≤ 2 * k := by omega
    have b : (m + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
    have c : m * s + 70 * m ^ 2 + 10 * m + 11 ≤ 91 * (m * (s + m)) := by nlinarith
    calc (k + 1) * (m + 1) ^ 2 * (m * s + 70 * m ^ 2 + 10 * m + 11)
        ≤ 2 * k * (4 * m ^ 2) * (91 * (m * (s + m))) := Nat.mul_le_mul (Nat.mul_le_mul a b) c
      _ = 728 * (k * m ^ 3 * (s + m)) := by ring
  have h₂ : 3 * m * s + 21 * m ^ 3 ≤ 24 * (k * m ^ 3 * (s + m)) := by
    have a : m * s ≤ k * m ^ 3 * (s + m) := by
      calc m * s ≤ k * m ^ 3 * s := Nat.mul_le_mul_right s (by nlinarith)
        _ ≤ k * m ^ 3 * (s + m) := Nat.mul_le_mul_left _ (Nat.le_add_right s m)
    have b : m ^ 3 ≤ k * m ^ 3 * (s + m) := by
      calc m ^ 3 = 1 * m ^ 3 * 1 := by ring
        _ ≤ k * m ^ 3 * (s + m) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) (by omega)
    have c : 3 * m * s = 3 * (m * s) := Nat.mul_assoc 3 m s
    omega
  have h₃ : 5 * Nat.size r₀ ≤ 5 * (k * m ^ 3 * (s + m)) := by
    have := size_le_self r₀
    have : k ≤ k * m ^ 3 * (s + m) := by
      calc k = k * 1 * 1 := by ring
        _ ≤ k * m ^ 3 * (s + m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hm)) (by omega)
    omega
  have := obsCost_le m k s r₀
  omega

/-! ### Lemma `lem:observer` -/

/-- **Lemma `lem:observer`.**  Let `M` be a matroid on `E = Fin m` with ground set `E`, `blk`
the blocks, and let the Boolean circuit `C` of size `s` output the binary digits of the rank of
`M`.  For every `r₀`, the Boolean circuit `observer M C blk r₀` on the `m · m` inputs
`[pairOf i ∈ G]`, `G ⊆ E × E`:

1. has `obsCost m k s r₀ ≤ (k+1)(m+1)²(ms + 70m² + 10m + 11) + 3ms + 21m³ + 1 + 5⌈log₂(r₀+1)⌉`
   gates (`O(k m³ (s + m))`, `obsCost_le_bigO`);
2. has `k` outputs;
3. for every `v` and every `t ≥ 0`, outputs at `G = G_t` the bits
   `F_b(G_t) = [ν(N_{G_t}) ≤ r₀] ∧ [b ∈ Av(N_{G_t})]`, `b = 0, …, k - 1`;
4. (Step 5) outputs `0` at `G = E × E` when `M` has a rainbow base, `rank M = k` and `r₀ < k`. -/
theorem lem_observer (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    (observer M C blk r₀).size = obsCost m k C.size r₀ ∧
      (observer M C blk r₀).size ≤ (k + 1) * (m + 1) ^ 2 *
        (m * C.size + 70 * m ^ 2 + 10 * m + 11) + 3 * m * C.size + 21 * m ^ 3 + 1 +
          5 * Nat.size r₀ ∧
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
    rw [obsV, inputRel_pairOf, avGuardV_eq (Fo := fun P => oracleV M P.1 P.2)
      (a := ctxV M (relBits (Gt v t))) (fun A => oracle_correct hE ht A) r₀ b, Bool.decide_and]
  refine ⟨hsize, hsize.trans_le (obsCost_le _ _ _ _), hlen, hG, fun hM hk hr => ?_⟩
  have hu : Gt (0 : Fin m → ℝ) 0 = univ := Gt_eq_univ fun _ _ => by simp
  have h := hG 0 0 le_rfl
  rw [hu, NG_univ hE, (nu_eq_iff hk).2 hM] at h
  rw [h, ← List.ofFn_const]
  congr 1
  funext b
  simp [Nat.not_le.2 hr]

end SignedTropical.Rainbow.Observer
