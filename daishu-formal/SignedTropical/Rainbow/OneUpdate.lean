import SignedTropical.Rainbow.GapUpdate
import SignedTropical.BoolAlg.Impl
import SignedTropical.Compiler

/-!
# Lemma `lem:oneupdate`: one PO-SL update as a signed tropical circuit

`greedy_intersection.tex`, Section 4.7, Lemma `lem:oneupdate`.  `M : Matroid (Fin m)` has ground
set `univ`, rank `k` and a rainbow base, and the blocks are the fibres of `blk : Fin m → Fin k`.
The ordered pairs `(e, f)` are indexed by `Fin (m * m)` (`GapUpdate.pairOf`).

* `IsObserver M blk r O`: the Boolean circuit `O` on the `m·m` pairs, input `i` the bit
  `[pairOf i ∈ G]`, outputs at every relation `G = G_t`, `t ≥ 0`, the `k` bits
  `F_b(G) = [ν(N_G) ≤ r] ∧ [b ∈ Av(N_G)]` of Lemma `lem:observer`.
* `updCircuit blk O`, a signed tropical circuit on the `m + k` inputs `(w, p)`
  (`Fin.append w p`): `v = w - p_blk` (`m` gates), `D⁺_{ef} = max(v_f - v_e, 0)` over all `m·m`
  ordered pairs (`2 m²` gates), the compiler of Theorem `thm:compiler` with the observer on the
  `m·m` pairs (`compileB`), and `p + a` (`k` gates).  Its size is `m + 2 m² + compileCost O + k`
  and it outputs `p + C_F(D⁺)`, `C_{F_b}` the gap sum of the `b`-th output bit of `O`
  (`updCircuit_spec`).
* `gapV_eq_update`: for an observer of stage `r < k`, at every state with `ν₀ = ν(M^v) ≥ r`, the
  compiled gap sums are the PO-SL update: by `GapUpdate.gapSum_congr_sublevel` the gap sum of the
  observed bits equals that of `F_b`, since the sublevel sets of `D⁺` are the relations `G_t`
  (`GapUpdate.relOf_sublevel`), and `GapUpdate.update_eq_gapSum` identifies the latter with
  `a_b`.
* `oneUpdate` (Lemma `lem:oneupdate`): a circuit of size at most
  `3 m² s_O + k m² + 6 m⁴ + 2 m² + m + k` maps `(w, p)` to `p + a` at every state of stage `r`;
  `oneUpdate_bigO`: with `s_O ≤ c (r + 2) m² (s + m)`, the order of Lemma `lem:observer`, the
  size is at most `(3 c + 11)(r + 2) m⁴ (s + m)`, the paper's `O(k m⁴ (s + m))`.

The builders are composed with the representations and implementations of `BoolAlg/Impl.lean`
(`Rep`, `Impl`), which serve any gate set.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremC

open SignedTropical.Rainbow SignedTropical.Rainbow.GapUpdate SignedTropical.BoolAlg

variable {m k n : ℕ}

/-! ### Observers -/

/-- `O` is an observer for stage `r` (Lemma `lem:observer`): a Boolean circuit on the `m·m`
pairs, input `i` the bit `[pairOf i ∈ G]`, whose outputs at every relation `G = G_t`, `t ≥ 0`,
are the `k` bits `F_b(G) = [ν(N_G) ≤ r] ∧ [b ∈ Av(N_G)]`, `b = 0, …, k - 1`. -/
def IsObserver (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (O : Circuit BoolOp (m * m)) :
    Prop :=
  ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
    O.eval boolInterp (fun i => decide (pairOf i ∈ POSL.Gt v t)) =
      List.ofFn fun b : Fin k =>
        decide (nu (POSL.NG M (POSL.Gt v t)) blk ≤ r ∧ b ∈ Av (POSL.NG M (POSL.Gt v t)) blk)

/-- An observer of stage `r` has `k` outputs. -/
theorem IsObserver.length_outs {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (m * m)} (hO : IsObserver M blk r O) : O.outs.length = k := by
  simpa [Circuit.eval] using congrArg List.length (hO 0 0 le_rfl)

/-- For `t ≥ 0`, the indicator vector of the sublevel set of `D⁺` at `t` is the input vector
of the relation `G_t`. -/
theorem indicator_sublevel (v : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    indicator (Integral.sublevel (Dplus v) t) = fun i => decide (pairOf i ∈ POSL.Gt v t) := by
  funext i
  simp [indicator, Dplus, POSL.Gt, ht]

/-- Entry `i` of `List.ofFn f` is `f i`. -/
theorem getD_ofFn {α : Type} {r : ℕ} (f : Fin r → α) (d : α) (i : Fin r) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-! ### The builders -/

/-- A vector of reals, carried by a family of operands. -/
abbrev realsR (r : ℕ) : Rep STOp ℝ n (Fin r → Arg n) (Fin r → ℝ) :=
  Rep.pi (Fin r) (Rep.arg (stInterp ℝ))

/-- Step 1, `v = w - p_blk`: one gate per element. -/
def shiftB (blk : Fin m → Fin k) (s : (Fin m → Arg n) × (Fin k → Arg n)) :
    Bld STOp n (Fin m → Arg n) :=
  tabB fun e => emit .sub (s.1 e) (s.2 (blk e))

/-- `shiftB` implements `(w, p) ↦ w - p_blk` with `m` gates. -/
theorem shiftB_impl (blk : Fin m → Fin k) :
    Impl ((realsR m).prod (realsR k)) (realsR (n := n) m) (shiftB blk) m
      (fun t => shift blk t.1 t.2) := by
  refine (Impl.tab fun e => ?_).cost (mul_one m)
  intro gs s T hs
  exact ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, den_emit STOp.sub (hs.1 e) (hs.2 (blk e))⟩

/-- Step 1, `D⁺_{ef} = max(v_f - v_e, 0)` over all `m·m` ordered pairs: two gates per pair. -/
def dplusB (s : Fin m → Arg n) : Bld STOp n (Fin (m * m) → Arg n) :=
  tabB fun i gs =>
    let q := emit .sub (s (pairOf i).2) (s (pairOf i).1) gs
    emit .max q.2 .const q.1

/-- `dplusB` implements `v ↦ D⁺(v)` with `2 m²` gates. -/
theorem dplusB_impl : Impl (realsR m) (realsR (n := n) (m * m)) dplusB (m * m * 2) Dplus := by
  refine Impl.tab fun i => ?_
  intro gs s T hs
  have h₁ := den_emit STOp.sub (hs (pairOf i).2) (hs (pairOf i).1)
  have h₂ := den_emit STOp.max h₁ (den_const _)
  exact ⟨(isPrefix_emit _ _ _ _).trans (isPrefix_emit _ _ _ _), by simp [length_emit], h₂⟩

/-- Step 2, the compiler of Theorem `thm:compiler` on the `m·m` pairs, with `O`. -/
theorem compileB_impl (O : Circuit BoolOp (m * m)) :
    Impl (realsR (m * m)) (Rep.list (stInterp ℝ) O.outs.length)
      (fun d => compileB (n := n) O (List.ofFn d)) (compileCost O) (compVal O) := by
  intro gs d D hd
  obtain ⟨hp, hl, hden⟩ := compileB_spec (B := O) (denL_ofFn hd)
  exact ⟨hp, hl, by rw [← hden.length_eq fun _ => 0, length_compVal], hden⟩

/-- Step 3, `p + a`: one gate per block. -/
theorem addB_impl :
    Impl ((realsR k).prod (realsR k)) (realsR (n := n) k)
      (fun s => tabB fun b => emit .add (s.1 b) (s.2 b)) k (fun t => t.1 + t.2) := by
  refine (Impl.tab fun b => ?_).cost (mul_one k)
  intro gs s T hs
  exact ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, den_emit STOp.add (hs.1 b) (hs.2 b)⟩

/-- The compiled gap sums at `D⁺(v)`, block by block: `a_b = C_{F_b}(D⁺)` for the observable
`F_b` read from the `b`-th output of `O`. -/
noncomputable def gapV (O : Circuit BoolOp (m * m)) (v : Fin m → ℝ) (b : Fin k) : ℝ :=
  (compVal O (Dplus v)).getD b 0

/-- The one-update builder: from operands carrying `(w, p)`, operands carrying `p + a`, where
`a_b` is the `b`-th output of the compiler at `D⁺(w - p_blk)`. -/
def updB (blk : Fin m → Fin k) (O : Circuit BoolOp (m * m)) :
    (Fin m → Arg n) × (Fin k → Arg n) → Bld STOp n (List (Arg n)) :=
  seqB (pairB (pureB Prod.snd) (seqB (shiftB blk) (seqB dplusB
      (seqB (fun d => compileB O (List.ofFn d)) (pureB fun as b => as.getD b .const)))))
    (seqB (fun s => tabB fun b => emit .add (s.1 b) (s.2 b)) (pureB List.ofFn))

/-- `updB` implements `(w, p) ↦ p + C_F(D⁺(w - p_blk))` with `m + 2 m² + compileCost O + k`
gates. -/
theorem updB_impl (blk : Fin m → Fin k) (O : Circuit BoolOp (m * m)) :
    Impl ((realsR m).prod (realsR k)) (Rep.list (stInterp ℝ) k) (updB (n := n) blk O)
      (m + m * m * 2 + compileCost O + k)
      (fun t => List.ofFn (t.2 + gapV O (shift blk t.1 t.2))) :=
  ((Impl.snd.pair ((shiftB_impl blk).comp (dplusB_impl.comp ((compileB_impl O).comp
    (Impl.free (R₂ := realsR k) (g := fun (as : List (Arg n)) (b : Fin k) => as.getD b .const)
      (F := fun (A : List ℝ) (b : Fin k) => A.getD b 0) fun _ _ _ hs b => hs.2.getD b))))).comp
    (addB_impl.comp (ofFn_impl _ k))).cost (by ring)

/-! ### The circuit -/

/-- The circuit of Lemma `lem:oneupdate`, on the `m + k` inputs `(w, p)`. -/
def updCircuit (blk : Fin m → Fin k) (O : Circuit BoolOp (m * m)) : Circuit STOp (m + k) :=
  circuitOf fun x => updB blk O (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b))

/-- The size of the one-update circuit, and what it computes at every `(w, p)`. -/
theorem updCircuit_spec (blk : Fin m → Fin k) (O : Circuit BoolOp (m * m)) :
    (updCircuit blk O).size = m + m * m * 2 + compileCost O + k ∧
      ∀ w p, (updCircuit blk O).eval (stInterp ℝ) (Fin.append w p) =
        List.ofFn (p + gapV O (shift blk w p)) := by
  have h := circuitOf_spec ((updB_impl blk O).pre (R := realsR (m + k))
    (g := fun x => (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b)))
    (G := fun x => (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b)))
    fun _ _ _ hs => ⟨fun e => hs _, fun b => hs _⟩)
  refine ⟨h.1, fun w p => ?_⟩
  rw [updCircuit, h.2.2]
  simp only [Fin.append_left, Fin.append_right]

/-- **The observed gap sums are the update.**  For an observer of stage `r < k`, at every `v` with
`ν(M^v) ≥ r`, `C_{F_b}(D⁺) = a_b` for every block `b`. -/
theorem gapV_eq_update {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (m * m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hO : IsObserver M blk r O)
    {v : Fin m → ℝ} (hr : r ≤ nu (minBases M v) blk) :
    gapV O v = Validity.update (POSL.N M v) blk r := by
  set F : Fin k → Finset (Fin (m * m)) → Bool := fun b S =>
    (O.eval boolInterp (indicator S)).getD b false
  have hB : ∀ S, O.eval boolInterp (indicator S) = List.ofFn fun b => F b S := by
    intro S
    refine List.ext_getElem (by simp [Circuit.eval, hO.length_outs]) fun i h₁ h₂ => ?_
    simp only [List.getElem_ofFn, F]
    rw [List.getD_eq_getElem _ _ h₁]
  funext b
  rw [gapV, compVal_eq hB (Dplus_nonneg v), getD_ofFn, update_eq_gapSum hE hk hM hr hrk b]
  refine gapSum_congr_sublevel (Dplus_nonneg v) fun t ht => ?_
  simp only [F, obs, indicator_sublevel v ht, hO v t ht, getD_ofFn, relOf_sublevel v ht]
  split_ifs <;> simp_all

/-- The size bound of the one-update circuit, for a Boolean circuit `O` with `k` outputs:
`m` gates for `v`, `2 m²` for `D⁺`, at most `3 m² s_O + k m² + 6 m⁴` for the compiler on the
`m·m` pairs (`compileCost_le`), and `k` for `p + a`. -/
theorem updCircuit_size_le (blk : Fin m → Fin k) {O : Circuit BoolOp (m * m)}
    (hO : O.outs.length = k) :
    (updCircuit blk O).size ≤ 3 * m ^ 2 * O.size + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k := by
  have h := compileCost_le O
  rw [hO] at h
  rw [(updCircuit_spec blk O).1]
  nlinarith [h]

/-- The one-update circuit of an observer of stage `r < k` outputs `p + a` at every state with
`ν₀ ≥ r`. -/
theorem updCircuit_eval {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (m * m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hO : IsObserver M blk r O)
    {w : Fin m → ℝ} {p : Fin k → ℝ} (hr : r ≤ nu (minBases M (shift blk w p)) blk) :
    (updCircuit blk O).eval (stInterp ℝ) (Fin.append w p) =
      List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r) := by
  rw [(updCircuit_spec blk O).2, gapV_eq_update hE hk hM hrk hO hr]

/-- **Lemma `lem:oneupdate`.**  Let `M` have ground set `E`, rank `k` and a rainbow base, let
`r < k`, and let `O` be an observer for stage `r` (Lemma `lem:observer`) of size `s_O`.  A signed
tropical circuit of size at most `3 m² s_O + k m² + 6 m⁴ + 2 m² + m + k` on the `m + k` inputs
`(w, p)` outputs `p + a`, `a` the PO-SL update at `v = w - p_blk`, at every state of stage `r`,
that is with `ν₀ = ν(M^v) ≥ r`. -/
theorem oneUpdate {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (m * m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hO : IsObserver M blk r O) :
    ∃ U : Circuit STOp (m + k),
      U.size ≤ 3 * m ^ 2 * O.size + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k ∧
        ∀ w p, r ≤ nu (minBases M (shift blk w p)) blk →
          U.eval (stInterp ℝ) (Fin.append w p) =
            List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r) :=
  ⟨updCircuit blk O, updCircuit_size_le blk hO.length_outs,
    fun _ _ hr => updCircuit_eval hE hk hM hrk hO hr⟩

/-! ### The order of the size -/

/-- `k^i m^j ≤ k^{i'} m^{j'} a` for `i ≤ i'`, `j ≤ j'` and `k, m, a ≥ 1`. -/
theorem pow_mul_pow_le {k m a i j i' j' : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (ha : 1 ≤ a)
    (hi : i ≤ i') (hj : j ≤ j') : k ^ i * m ^ j ≤ k ^ i' * m ^ j' * a :=
  (Nat.mul_le_mul (Nat.pow_le_pow_right hk hi) (Nat.pow_le_pow_right hm hj)).trans
    (Nat.le_mul_of_pos_right _ ha)

/-- The bound of `oneUpdate` with an observer of size at most `c (r + 2) m² (s + m)` is at most
`3 c (r + 2) m⁴ (s + m) + 11 m⁴`, for `k ≤ m`. -/
theorem updSize_le {m k s c r : ℕ} (hkm : k ≤ m) :
    3 * m ^ 2 * (c * ((r + 2) * m ^ 2 * (s + m))) + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k ≤
      3 * c * ((r + 2) * (m ^ 4 * (s + m))) + 11 * m ^ 4 := by
  have e0 : 3 * m ^ 2 * (c * ((r + 2) * m ^ 2 * (s + m))) =
      3 * c * ((r + 2) * (m ^ 4 * (s + m))) := by ring
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : k = 0 := by omega
    simp
  have h1 : k * m ^ 2 ≤ m ^ 4 :=
    calc k * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ hkm
      _ = m ^ 3 := by ring
      _ ≤ m ^ 4 := Nat.pow_le_pow_right hm (by norm_num)
  have h2 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right hm (by norm_num)
  have h3 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  rw [e0]
  omega

/-- **Lemma `lem:oneupdate`, the order of the size.**  Under the hypotheses of `oneUpdate`, with
an observer of size at most `c (r + 2) m² (s + m)` (the order `O((r + 2) m² (s + m))` of Lemma
`lem:observer`, `s` the size of a Boolean rank circuit), the circuit has at most
`(3 c + 11)(r + 2) m⁴ (s + m)` gates: the paper's `O(k m⁴ (s + m))`. -/
theorem oneUpdate_bigO {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (m * m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hO : IsObserver M blk r O) {s c : ℕ}
    (hs : O.size ≤ c * ((r + 2) * m ^ 2 * (s + m))) :
    ∃ U : Circuit STOp (m + k), U.size ≤ (3 * c + 11) * ((r + 2) * m ^ 4 * (s + m)) ∧
      ∀ w p, r ≤ nu (minBases M (shift blk w p)) blk →
        U.eval (stInterp ℝ) (Fin.append w p) =
          List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r) := by
  obtain ⟨U, hU, hUe⟩ := oneUpdate hE hk hM hrk hO
  have hkm : k ≤ m := hk ▸ rank_le_card M
  have hm : 1 ≤ m := (show 1 ≤ k by omega).trans hkm
  refine ⟨U, hU.trans ?_, hUe⟩
  have h1 := Nat.mul_le_mul_left (3 * m ^ 2) hs
  have h2 := updSize_le (s := s) (c := c) (r := r) hkm
  have h3 : m ^ 4 ≤ (r + 2) * m ^ 4 * (s + m) :=
    calc m ^ 4 = 1 * m ^ 4 * 1 := by ring
      _ ≤ (r + 2) * m ^ 4 * (s + m) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  have e : 3 * c * ((r + 2) * (m ^ 4 * (s + m))) + 11 * ((r + 2) * m ^ 4 * (s + m)) =
      (3 * c + 11) * ((r + 2) * m ^ 4 * (s + m)) := by ring
  omega

end SignedTropical.Rainbow.TheoremC
