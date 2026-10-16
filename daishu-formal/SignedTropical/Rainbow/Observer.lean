import SignedTropical.Rainbow.ObserverOracle
import SignedTropical.Rainbow.MICircuit

/-!
# The observer (Lemma `lem:observer`)

`greedy_intersection.tex`, Lemma `lem:observer`: from a Boolean circuit `C` of size `s` that
outputs the binary digits of the rank of `M` (the hypothesis of Theorem `thm:A`) and from `r₀`,
a Boolean circuit `observer M C blk r₀` on the `qn m = m + 2m²` event bits of
`Rainbow/Events.lean` (the entry bits `[t_x ≤ t]`, the merge bits `[T_xy ≤ t]`, the order bits
`[U_xy ≤ t]`) outputs at the event bits of every `t ≥ 0` the `k` bits
`F_b = [ν(N(t)) ≤ r₀] ∧ [b ∈ Av(N(t))]`.

* Steps 1 and 2 (`Rainbow/ObserverOracle.lean`): the context from the event bits
  (`evCtxB_impl`, `m(2m + s)` gates), which is the context of `G_t` (`evCtxV_eq`), and the
  exchange tests of `N_{G_t}` (`locB_impl`, `locV_exchOracle`), one rank run each.
* Step 3 (`Rainbow/MICircuit.lean`): `r₀ + 1` rounds of the augmenting path algorithm, one more
  exchange graph for `Av`, and the guard, with the exchange tests of Step 2 (`avGuardB_impl`,
  `avGuardV_eq`).  After `r₀ + 1` rounds the state has at least `min(r₀ + 1, ν)` elements, so
  `[|I| ≤ r₀] = [ν ≤ r₀]`, and when `ν ≤ r₀` it is a largest rainbow independent set.
* `lem_observer`: the size (`obsCost`, exact), the explicit bound
  `(r₀+2)(m+1)²(s + 52(m+1)) + ms + 2m² + 3k(m+1) + 5⌈log₂(r₀+1)⌉` (`obsCost_le`), the `k`
  outputs, and their values at the event bits of every `t ≥ 0`, by `N(t) = N_{G_t}`
  (`POSL.N_eq_NG`).  `obsCost_le_bigO`: the size is at most `424 (r₀ + 2) m² (s + m)` for
  `m ≥ 1`, `k ≤ m` and `r₀ < k`.  Reading the context from the event bits replaces the
  `3ms + O(m³)` gates that computed `PO_G` and the clusters from a relation `G`.
-/

open Finset

namespace SignedTropical.Rainbow.Observer

open SignedTropical SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.POSL
  SignedTropical.Rainbow.MI SignedTropical.Rainbow.Events

variable {m k n : ℕ} {M : Matroid (Fin m)} {C : Circuit BoolOp m}

/-! ### The circuit -/

/-- The value of the observer at the event bits `X`: the bits `[|I| ≤ r₀] ∧ [b ∈ Av]` of the
matroid intersection circuit with `r₀ + 1` rounds, run with the exchange tests of
`Rainbow/ObserverOracle.lean` at the context read from `X`. -/
noncomputable def obsV (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r₀ : ℕ)
    (X : Fin (qn m) → Bool) (b : Fin k) : Bool :=
  (miV (fun y => locV M y) blk (r₀ + 1) r₀ (evCtxV M X)).2.2.1 &&
    (miV (fun y => locV M y) blk (r₀ + 1) r₀ (evCtxV M X)).2.2.2 b

/-- The builder of the observer: the context from the event bits (Steps 1 and 2), and the matroid
intersection circuit with `r₀ + 1` rounds and the exchange tests (Step 3). -/
noncomputable def obsB (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : (Fin (qn m) → Arg n) → Bld BoolOp n (Fin k → Arg n) :=
  seqB (evCtxB M C) (avGuardB (locB C) blk (r₀ + 1) r₀)

/-- The gates of the observer: the context, the matroid intersection circuit with `r₀ + 1`
rounds and `locCost` gates per exchange test, and the `k` output gates. -/
def obsCost (m k s r₀ : ℕ) : ℕ :=
  m * (m * 2) + m * s + (miCost m k (r₀ + 1) (locCost m s) r₀ + k)

/-- **The observer as an implementation**: from the event bits, `obsB` computes `obsV M blk r₀`
with `obsCost m k s r₀` gates. -/
theorem obsB_impl
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    Impl (vecR (qn m)) (vecR (n := n) k) (obsB M C blk r₀) (obsCost m k C.size r₀)
      (obsV M blk r₀) :=
  ((evCtxB_impl hB).comp (avGuardB_impl (locB_impl hB) blk (r₀ + 1) r₀)).cost
    (by rw [obsCost])

/-- **The observer circuit** of Lemma `lem:observer`, on the `qn m` event bits. -/
noncomputable def observer (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (r₀ : ℕ) : Circuit BoolOp (qn m) :=
  vecCircuit (obsB M C blk r₀)

/-! ### The size -/

/-- **The size of the observer**, an explicit polynomial:
`obsCost m k s r₀ ≤ (r₀+2)(m+1)²(s + 52(m+1)) + ms + 2m² + 3k(m+1) + 5⌈log₂(r₀+1)⌉`. -/
theorem obsCost_le (m k s r₀ : ℕ) :
    obsCost m k s r₀ ≤ (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1)) + m * s + 2 * m ^ 2 +
      3 * k * (m + 1) + 5 * Nat.size r₀ := by
  have h₁ := miCost_add_le m k (r₀ + 1) (locCost m s) r₀
  have h₂ : (r₀ + 1 + 1) * (m + 1) ^ 2 * (locCost m s + 10 * (m + 1)) ≤
      (r₀ + 2) * (m + 1) ^ 2 * (s + 52 * (m + 1)) :=
    Nat.mul_le_mul_left _ (by have := locCost_le m s; omega)
  have e : m * (m * 2) = 2 * m ^ 2 := by ring
  unfold obsCost
  omega

/-- **The size of the observer is `O((r₀ + 2) m² (s + m))`**: for `1 ≤ m`, `k ≤ m` and
`r₀ < k`, at most `424 (r₀ + 2) m² (s + m)`. -/
theorem obsCost_le_bigO {m k s r₀ : ℕ} (hm : 1 ≤ m) (hkm : k ≤ m) (hr : r₀ < k) :
    obsCost m k s r₀ ≤ 424 * ((r₀ + 2) * m ^ 2 * (s + m)) := by
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
  -- the other terms are at most `16 m² (s + m) ≤ 8 (r₀ + 2) m² (s + m)`
  have h₂ : m * s + 2 * m ^ 2 + 3 * k * (m + 1) + 5 * Nat.size r₀ ≤
      16 * (m ^ 2 * (s + m)) := by
    have a : m * s ≤ m ^ 2 * (s + m) := by
      calc m * s ≤ m ^ 2 * s := Nat.mul_le_mul_right s hm2
        _ ≤ m ^ 2 * (s + m) := Nat.mul_le_mul_left _ (Nat.le_add_right s m)
    have c : 3 * k * (m + 1) ≤ 6 * m ^ 2 := by nlinarith
    have d : Nat.size r₀ ≤ m := (size_le_self r₀).trans (by omega)
    omega
  have h₃ : 16 * (m ^ 2 * (s + m)) ≤ 8 * ((r₀ + 2) * m ^ 2 * (s + m)) := by
    have := Nat.mul_le_mul_right (m ^ 2 * (s + m)) (show 2 ≤ r₀ + 2 by omega)
    nlinarith
  have := obsCost_le m k s r₀
  omega

/-! ### Lemma `lem:observer` -/

/-- **Lemma `lem:observer`.**  Let `M` be a matroid on `E = Fin m` with ground set `E`, `blk`
the blocks, and let the Boolean circuit `C` of size `s` output the binary digits of the rank of
`M`.  For every `r₀`, the Boolean circuit `observer M C blk r₀` on the `qn m` event bits:

1. has `obsCost m k s r₀ ≤ (r₀+2)(m+1)²(s + 52(m+1)) + ms + 2m² + 3k(m+1) + 5⌈log₂(r₀+1)⌉`
   gates (`O((r₀ + 2) m² (s + m))`, `obsCost_le_bigO`);
2. has `k` outputs;
3. for every `v` and every `t ≥ 0`, outputs at the event bits `[Q_j ≤ t]` the bits
   `F_b = [ν(N(t)) ≤ r₀] ∧ [b ∈ Av(N(t))]`, `b = 0, …, k - 1`. -/
theorem lem_observer (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    (observer M C blk r₀).size = obsCost m k C.size r₀ ∧
      (observer M C blk r₀).size ≤ (r₀ + 2) * (m + 1) ^ 2 * (C.size + 52 * (m + 1)) +
        m * C.size + 2 * m ^ 2 + 3 * k * (m + 1) + 5 * Nat.size r₀ ∧
      (observer M C blk r₀).outs.length = k ∧
      ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        (observer M C blk r₀).eval boolInterp (fun j => decide (Qv M v j ≤ t)) =
          List.ofFn fun b : Fin k =>
            decide (nu (N M v t) blk ≤ r₀ ∧ b ∈ Av (N M v t) blk) := by
  obtain ⟨hsize, hlen, heval⟩ := vecCircuit_spec (obsB_impl (n := qn m) hB blk r₀)
  refine ⟨hsize, hsize.trans_le (obsCost_le _ _ _ _), hlen, fun v t ht => ?_⟩
  rw [observer, heval]
  congr 1
  funext b
  rw [obsV, evCtxV_eq ht, avGuardV_eq (locV_exchOracle hE ht) (Nat.lt_succ_self r₀) b,
    Bool.decide_and, N_eq_NG ht]

end SignedTropical.Rainbow.Observer
