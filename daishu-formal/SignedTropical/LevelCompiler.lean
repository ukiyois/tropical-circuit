import SignedTropical.Compiler

/-!
# The compiler at given levels

`greedy_intersection.tex`, Lemma `lem:levelcompiler`: the compiler of `signed_assignment.tex`
(Theorem `thm:compiler`) run at levels that are computed inside the circuit and are not the
values it reads.  Given a Boolean circuit `B` with `q` inputs and `N` outputs, operands carrying
levels `Λ ∈ ℝ^L` and operands carrying query values `Q ∈ ℝ^q`, the circuit (`levB`):

1. sorts `Λ` with the insertion-sort network, `3 L (L - 1) / 2` gates, and prepends `s₀ = 0`;
2. for each gap `k < L`: forms `Δ_k = s_{k+1} - s_k`, the `q` membership values
   `max(Δ_k - max(Q_j - s_k, 0), 0)`, lifts `B` at amplitude `Δ_k` and adds the `N` lifted
   outputs to `N` running sums (`gapB` of `Compiler.lean`, with `gapB_spec` for different query
   values and levels).

Its size is `levCost B L = 3 L(L-1)/2 + L (1 + 4 q + Σ liftCost + N)` (`levB_spec`), at most
`3 L²/2 + L (1 + 4 q + 3 s + N)` (`levCost_le`).  When `Λ ≥ 0` and every `Q_j` is one of
`s_0 = 0, s_1, …, s_L`, the membership values are exact (`bitQ_eq`), and output `u` is
`Σ_{k<L} Δ_k F_u([Q ≤ s_k])` (`levVal_eq`), `F_u` the `u`-th output of `B` as a function of its
input bits.  With `Q = Λ = D` this is the compiler of Theorem `thm:compiler`.
-/

open Finset

namespace SignedTropical

variable {n q L : ℕ}

/-- The compiler at the levels `lam`, reading the query values `d`. -/
def levB (B : Circuit BoolOp q) (d lam : List (Arg n)) : Bld STOp n (List (Arg n)) := fun gs =>
  let p := isortB lam gs
  gapsB B d p.2 (List.range lam.length) (List.replicate B.outs.length .const) p.1

/-- What the compiler at given levels computes. -/
noncomputable def levVal (B : Circuit BoolOp q) (Q : Fin q → ℝ) (Λ : Fin L → ℝ) : List ℝ :=
  (List.range L).foldl (fun a k => List.zipWith (· + ·) a (gapOutQ B Q Λ k))
    (List.replicate B.outs.length 0)

/-- Gates of the compiler at `L` levels. -/
def levCost (B : Circuit BoolOp q) (L : ℕ) : ℕ := 3 * (List.range L).sum + L * gapCost B

/-- **The compiler at given levels**: `levCost B L` gates, and it computes `levVal B Q Λ`. -/
theorem levB_spec {B : Circuit BoolOp q} {d lam : List (Arg n)}
    {Q : (Fin n → ℝ) → Fin q → ℝ} {Λ : (Fin n → ℝ) → Fin L → ℝ} {gs : List (Gate STOp n)}
    (hd : DenL (stInterp ℝ) gs d (fun x => List.ofFn (Q x)))
    (hl : DenL (stInterp ℝ) gs lam (fun x => List.ofFn (Λ x))) :
    gs <+: (levB B d lam gs).1 ∧ (levB B d lam gs).1.length = gs.length + levCost B L ∧
      DenL (stInterp ℝ) (levB B d lam gs).1 (levB B d lam gs).2
        (fun x => levVal B (Q x) (Λ x)) := by
  obtain ⟨hp, hlen, hsort⟩ := isortB_spec hl
  have hs : DenL (stInterp ℝ) (isortB lam gs).1 (isortB lam gs).2 (fun x => sortedVals (Λ x)) :=
    hsort.congr fun x => isortV_eq_insertionSort _
  have hacc : DenL (stInterp ℝ) (isortB lam gs).1 (List.replicate B.outs.length .const)
      (fun _ => List.replicate B.outs.length 0) := by
    refine ⟨by simp [Arg.Valid], fun x => ?_⟩
    simp only [List.map_replicate]; rfl
  have hL : lam.length = L := by rw [← hl.length_eq (fun _ => 0)]; simp
  obtain ⟨hq, hlen', hden⟩ := gapsB_spec (B := B) (Q := Q) (Λ := Λ) (List.range lam.length)
    (hd.mono hp) hs hacc (by simp)
  refine ⟨hp.trans hq, ?_, hden.congr fun x => by rw [levVal, hL]⟩
  have e : (levB B d lam gs).1.length =
      (isortB lam gs).1.length + (List.range lam.length).length * gapCost B := hlen'
  rw [e, hlen, List.length_range, hL, levCost]
  ring

/-- **The size of the compiler at given levels**: `2 levCost ≤ 3 L² + 2 L (1 + 4 q + 3 s + N)`. -/
theorem levCost_le (B : Circuit BoolOp q) (L : ℕ) :
    2 * levCost B L ≤ 3 * L ^ 2 + 2 * L * (1 + 4 * q + 3 * B.size + B.outs.length) := by
  have hs := sum_range_mul_two L
  have hL := liftCost_sum_le B
  have hmL := Nat.mul_le_mul_left L hL
  simp only [levCost, gapCost]
  generalize (B.gates.map fun g => liftCost g.op).sum = c at *
  generalize (List.range L).sum = s at *
  have h1 : L * (L - 1) ≤ L ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left L (Nat.sub_le L 1)
  nlinarith

/-! ### What the compiler computes when the query values are levels -/

/-- A value equal to one of `s_0, …, s_L` lies outside every open gap. -/
theorem le_or_succ_le_of_eq {Λ : Fin L → ℝ} (hΛ : ∀ i, 0 ≤ Λ i) {c : ℝ} {i : ℕ} (hi : i ≤ L)
    (hc : sortedVal Λ i = c) {k : ℕ} (hk : k < L) :
    c ≤ sortedVal Λ k ∨ sortedVal Λ (k + 1) ≤ c := by
  rcases le_or_gt i k with hik | hik
  · exact Or.inl (hc ▸ sortedVal_mono hΛ hik hk.le)
  · exact Or.inr (hc ▸ sortedVal_mono hΛ hik hi)

/-- **Exact membership at amplitude** (Lemma `lem:bit` for query values that are levels): if
`Q_j` is one of `s_0, …, s_L`, then `max(Δ_k - max(Q_j - s_k, 0), 0) = Δ_k [Q_j ≤ s_k]`. -/
theorem bitQ_eq {Q : Fin q → ℝ} {Λ : Fin L → ℝ} (hΛ : ∀ i, 0 ≤ Λ i)
    (hQ : ∀ j, ∃ i ≤ L, sortedVal Λ i = Q j) {k : ℕ} (hk : k < L) (j : Fin q) :
    bitQ Q Λ k j =
      ampl (sortedVal Λ (k + 1) - sortedVal Λ k) (decide (Q j ≤ sortedVal Λ k)) := by
  have hmono := sortedVal_mono hΛ (Nat.le_succ k) hk
  simp only [bitQ, ampl]
  by_cases h : Q j ≤ sortedVal Λ k
  · rw [decide_eq_true h, if_pos rfl, max_eq_right (by linarith : Q j - sortedVal Λ k ≤ 0),
      sub_zero, max_eq_left (by linarith)]
  · obtain ⟨i, hi, hc⟩ := hQ j
    have h' := (le_or_succ_le_of_eq hΛ hi hc hk).resolve_left h
    rw [decide_eq_false h, if_neg (by simp), max_eq_left (by linarith : 0 ≤ Q j - sortedVal Λ k),
      max_eq_right (by linarith)]

/-- The lifted outputs at gap `k < L` are `Δ_k F_u([Q ≤ s_k])`. -/
theorem gapOutQ_eq {N : ℕ} {F : Fin N → (Fin q → Bool) → Bool} {B : Circuit BoolOp q}
    (hB : ∀ X, B.eval boolInterp X = List.ofFn fun u => F u X) {Q : Fin q → ℝ}
    {Λ : Fin L → ℝ} (hΛ : ∀ i, 0 ≤ Λ i) (hQ : ∀ j, ∃ i ≤ L, sortedVal Λ i = Q j) {k : ℕ}
    (hk : k < L) :
    gapOutQ B Q Λ k = List.ofFn fun u => (sortedVal Λ (k + 1) - sortedVal Λ k) *
      if F u (fun j => decide (Q j ≤ sortedVal Λ k)) then 1 else 0 := by
  have hΔ : 0 ≤ sortedVal Λ (k + 1) - sortedVal Λ k :=
    sub_nonneg.2 (sortedVal_mono hΛ (Nat.le_succ k) hk)
  have hbit : bitQ Q Λ k = fun j => ampl (sortedVal Λ (k + 1) - sortedVal Λ k)
      (decide (Q j ≤ sortedVal Λ k)) := funext (bitQ_eq hΛ hQ hk)
  rw [gapOutQ, hbit, eval_liftInterp hΔ, hB, List.map_ofFn]
  congr 1
  funext u
  simp only [Function.comp, ampl]
  split_ifs <;> simp

/-- **What the compiler at given levels computes**: for `Λ ≥ 0` and query values among
`s_0, …, s_L`, output `u` is `Σ_{k<L} Δ_k F_u([Q ≤ s_k])`. -/
theorem levVal_eq {N : ℕ} {F : Fin N → (Fin q → Bool) → Bool} {B : Circuit BoolOp q}
    (hB : ∀ X, B.eval boolInterp X = List.ofFn fun u => F u X) {Q : Fin q → ℝ}
    {Λ : Fin L → ℝ} (hΛ : ∀ i, 0 ≤ Λ i) (hQ : ∀ j, ∃ i ≤ L, sortedVal Λ i = Q j) :
    levVal B Q Λ = List.ofFn fun u => ∑ k ∈ range L, (sortedVal Λ (k + 1) - sortedVal Λ k) *
      if F u (fun j => decide (Q j ≤ sortedVal Λ k)) then 1 else 0 := by
  have hN : B.outs.length = N := by
    have := congrArg List.length (hB fun _ => false); simpa [Circuit.eval] using this
  have hfold : ∀ ks : List ℕ, (∀ k ∈ ks, k < L) →
      ks.foldl (fun a k => List.zipWith (· + ·) a (gapOutQ B Q Λ k))
          (List.replicate B.outs.length 0)
        = ks.foldl (fun a k => List.zipWith (· + ·) a (List.ofFn fun u =>
            (sortedVal Λ (k + 1) - sortedVal Λ k) *
              if F u (fun j => decide (Q j ≤ sortedVal Λ k)) then 1 else 0))
          (List.ofFn fun _ : Fin N => (0 : ℝ)) := by
    intro ks hks
    rw [List.ofFn_const, hN]
    suffices ∀ (ks : List ℕ) (a : List ℝ), (∀ k ∈ ks, k < L) →
        ks.foldl (fun a k => List.zipWith (· + ·) a (gapOutQ B Q Λ k)) a
          = ks.foldl (fun a k => List.zipWith (· + ·) a (List.ofFn fun u =>
            (sortedVal Λ (k + 1) - sortedVal Λ k) *
              if F u (fun j => decide (Q j ≤ sortedVal Λ k)) then 1 else 0)) a
      from this ks _ hks
    intro ks
    induction ks with
    | nil => intro _ _; rfl
    | cons k ks ih =>
      intro a hks
      simp only [List.foldl_cons]
      rw [gapOutQ_eq hB hΛ hQ (hks k (by simp))]
      exact ih _ fun j hj => hks j (by simp [hj])
  rw [levVal, hfold _ (fun k hk => List.mem_range.1 hk), foldl_zipWith_ofFn]
  congr 1
  funext u
  rw [zero_add, sum_range_eq_list]

theorem length_levVal (B : Circuit BoolOp q) (Q : Fin q → ℝ) (Λ : Fin L → ℝ) :
    (levVal B Q Λ).length = B.outs.length := by
  rw [levVal]
  suffices ∀ (ks : List ℕ) (a : List ℝ), a.length = B.outs.length →
      (ks.foldl (fun a k => List.zipWith (· + ·) a (gapOutQ B Q Λ k)) a).length
        = B.outs.length from this _ _ (by simp)
  intro ks
  induction ks with
  | nil => intro a h; exact h
  | cons k ks ih =>
    intro a h
    exact ih _ (by simp [h, gapOutQ, Circuit.eval])

end SignedTropical
