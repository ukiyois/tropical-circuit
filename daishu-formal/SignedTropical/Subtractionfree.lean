import SignedTropical.TheoremA
import SignedTropical.Lattice
import Mathlib.Algebra.BigOperators.Fin

/-!
# Corollary F: the subtraction-free side

`docs/research-direction-2026-10-11.md`, Section 3.2, Corollary F:

`Mon(Span_M) ≤ Size_{min,+,max}(h_M) ≤ ∑_{u=1}^{k} Mon(1[r ≥ u]) + k - 1`.

Upper bound (proved).  For the rank thresholds `g_u(S) = [u ≤ r(S)]`,
`h_M(w) = ∑_{u=1}^{k} Λ_{g_u}(w)` at every `w ∈ ℝ^m` (`maxBasisWeight_eq_sum_sugeno`): on
`D ≥ 0` this is the Sugeno form (`prop:sugeno`) summed over `u` against the greedy
identity, and both sides move by `k c` under `w ↦ w + c·1`.  Each `Λ_{g_u}` is computed on
all of `ℝ^m` by the lattice circuit of a monotone Boolean circuit for `g_u`
(`thm:lattice`, `eval_eq_sugeno`), and `k - 1` additions sum them (`corollaryF_upper`).
`Mon(g)` is attained because every monotone `g` with `g(∅) = 0` and `g(E) = 1` has a
monotone circuit (`exists_monCircuit`, a disjunctive normal form), which gives the
statement with `Mon` (`corollaryF_upper_mon`).

Lower bound (from an external result).  Jukna, Seiwert and Sergeev, Proposition 2: a
`(min, +, max)` circuit computing a minimization problem yields a monotone Boolean circuit
of the same size for its Boolean version.  For minimum-weight bases the Boolean version is
the spanning predicate `Span_M(S) = [r(S) = k]`.  This enters as the hypothesis `hJSS` of
`corollaryF_lower`.  The part proved here is the reduction from the maximization form:
exchanging `min` and `max` in a circuit for `h_M` gives a circuit of the same size for
`min_B w(B) = -h_M(-w)` (`swap_eval`).
-/

open Finset

namespace SignedTropical

variable {n m : ℕ}

/-! ### Rank thresholds -/

section Thresholds

variable (M : Matroid (Fin m))

/-- The rank threshold `g_u(S) = [u ≤ r(S)]`. -/
noncomputable def rankThreshold (u : ℕ) (S : Finset (Fin m)) : Bool := decide (u ≤ rk M S)

theorem rk_mono {S T : Finset (Fin m)} (h : S ⊆ T) : rk M S ≤ rk M T := by
  have := M.eRk_mono (Finset.coe_subset.2 h)
  rw [← coe_rk, ← coe_rk] at this
  exact_mod_cast this

theorem rk_empty : rk M ∅ = 0 := by
  simp [rk, Matroid.eRk_empty]

theorem rankThreshold_monotone (u : ℕ) : MonotoneObs (rankThreshold M u) := by
  intro S T hST h
  simp only [rankThreshold, decide_eq_true_eq] at h ⊢
  exact h.trans (rk_mono M hST)

theorem rankThreshold_empty {u : ℕ} (hu : 1 ≤ u) : rankThreshold M u ∅ = false := by
  simp [rankThreshold, rk_empty]; omega

theorem rankThreshold_univ (hE : M.E = Set.univ) {u : ℕ} (hu : u ≤ rank M) :
    rankThreshold M u univ = true := by
  simp [rankThreshold, rk_univ M hE, hu]

end Thresholds

/-- `∑_{u<k} [u + 1 ≤ r] = r` for `r ≤ k`. -/
theorem sum_thresholds (r k : ℕ) (h : r ≤ k) :
    ∑ u ∈ range k, (if u + 1 ≤ r then (1 : ℝ) else 0) = r := by
  rw [sum_boole]
  rw [show (range k).filter (fun u => u + 1 ≤ r) = range r by
    ext u; simp only [mem_filter, mem_range]; omega]
  simp

/-- **Translation of the Sugeno value.** -/
theorem sugeno_add_const {g : Finset (Fin m) → Bool} (hg : MonotoneObs g) (hg0 : g ∅ = false)
    (hg1 : g univ = true) (w : Fin m → ℝ) (c : ℝ) :
    sugeno g (fun e => w e + c) = sugeno g w + c := by
  refine le_antisymm ?_ ?_
  · have h := (le_sugeno_iff hg hg0 hg1 _ _).1 (le_refl (sugeno g fun e => w e + c))
    have : sugeno g (fun e => w e + c) - c ≤ sugeno g w := by
      rw [le_sugeno_iff hg hg0 hg1]
      convert h using 2
      ext e; simp only [mem_filter, mem_univ, true_and]; constructor <;> intro h' <;> linarith
    linarith
  · have h := (le_sugeno_iff hg hg0 hg1 _ _).1 (le_refl (sugeno g w))
    rw [le_sugeno_iff hg hg0 hg1]
    convert h using 2
    ext e; simp only [mem_filter, mem_univ, true_and]; constructor <;> intro h' <;> linarith

/-- **`h_M` is the sum of the Sugeno values of the rank thresholds**, at every `w ∈ ℝ^m`. -/
theorem maxBasisWeight_eq_sum_sugeno {M : Matroid (Fin m)} (hE : M.E = Set.univ)
    (w : Fin m → ℝ) :
    maxBasisWeight M w = ∑ u ∈ range (rank M), sugeno (rankThreshold M (u + 1)) w := by
  set μ := minV (List.ofFn w)
  set D : Fin m → ℝ := fun e => w e - μ
  have hD : ∀ e, 0 ≤ D e := fun e => sub_nonneg.2 (minV_le _ (List.mem_ofFn.2 ⟨e, rfl⟩))
  have hw : w = fun e => D e + μ := by funext e; simp [D]
  have hmon := fun u => rankThreshold_monotone M (u + 1)
  have h0 : ∀ u : ℕ, rankThreshold M (u + 1) ∅ = false := fun u =>
    rankThreshold_empty M (by omega)
  have h1 : ∀ u ∈ range (rank M), rankThreshold M (u + 1) univ = true := fun u hu =>
    rankThreshold_univ M hE (by simpa using hu)
  -- shift both sides by `μ`
  rw [hw, maxBasisWeight_add_const, sum_congr rfl fun u hu =>
    sugeno_add_const (hmon u) (h0 u) (h1 u hu) D μ, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul, mul_comm (rank M : ℝ) μ]
  congr 1
  -- on `D ≥ 0`: the Sugeno form, summed over `u`, against the greedy identity
  rw [maxBasisWeight_eq_gapSum hE hD, sum_congr rfl fun u _ =>
    (gapSum_eq_sugeno (hmon u) (h0 u) hD).symm, ← gapSum_finsetSum]
  congr 1
  funext S
  rw [← sum_thresholds (rk M (univ \ S)) (rank M) (rk_le_rank M _)]
  exact sum_congr rfl fun u _ => by simp [rankThreshold]

/-! ### The `(min, +, max)` circuit -/

/-- Lattice gates as `(min, +, max)` gates. -/
def latToTrop : LatOp → TropOp
  | .min => .min
  | .max => .max

/-- Inline a lattice circuit into a `(min, +, max)` builder; return its first output. -/
def latB (C : Circuit LatOp m) : Bld TropOp m (Arg m) := fun gs =>
  let p := inline (fun o a b => emit (latToTrop o) a b) (fun i => .input i) .const C gs
  (p.1, p.2.headD .const)

theorem latB_spec {C : Circuit LatOp m} {f : (Fin m → ℝ) → ℝ}
    (hC : ∀ x, C.eval (latInterp ℝ 0) x = [f x]) (gs : List (Gate TropOp m)) :
    gs <+: (latB C gs).1 ∧ (latB C gs).1.length = gs.length + C.size ∧
      Den tropInterp (latB C gs).1 (latB C gs).2 f := by
  obtain ⟨hp, h⟩ := inline_spec (R := Den tropInterp) (J := fun _ => latInterp ℝ 0)
    (φ := fun i x => x i) (gad := fun o a b => emit (latToTrop o) a b)
    (inp := fun i => .input i) (c := .const) (gs₀ := gs)
    (fun _ _ _ _ hp h => h.mono hp) (den_const gs) (fun i => den_input gs i)
    (fun o _ _ _ _ gs' _ h₁ h₂ => ⟨isPrefix_emit _ _ _ _, (den_emit (latToTrop o) h₁ h₂).congr
      fun x => by cases o <;> rfl⟩) C
  refine ⟨hp, ?_, ?_⟩
  · simp only [latB, Circuit.size]
    rw [length_inline (fun _ => 1) (fun o a b gs => length_emit _ a b gs) C gs]
    simp
  · have hlen : C.outs.length = 1 := by
      have := congrArg List.length (hC fun _ => 0); simpa [Circuit.eval] using this
    obtain ⟨o, ho⟩ := List.length_eq_one_iff.1 hlen
    rw [ho, List.map_singleton] at h
    show Den tropInterp (inline (fun o a b => emit (latToTrop o) a b) (fun i => .input i) .const
      C gs).1 ((inline (fun o a b => emit (latToTrop o) a b) (fun i => .input i) .const
      C gs).2.headD .const) f
    generalize inline (fun o a b => emit (latToTrop o) a b) (fun i => .input i) .const C gs
      = p at h ⊢
    obtain ⟨gs', outs⟩ := p
    cases h with
    | cons hr hnil =>
      cases hnil
      refine hr.congr fun x => ?_
      have := hC x
      simp only [Circuit.eval, ho, List.map_singleton, List.cons.injEq, and_true] at this
      exact this

/-- Sum of a list of operands, `length - 1` gates. -/
def sumB : List (Arg n) → Bld TropOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | [a] => fun gs => (gs, a)
  | a :: b :: l => fun gs =>
    let p := sumB (b :: l) gs
    emit .add a p.2 p.1

theorem sumB_spec :
    ∀ {as : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate TropOp n)},
      DenL tropInterp gs as F →
      gs <+: (sumB as gs).1 ∧ (sumB as gs).1.length = gs.length + (as.length - 1) ∧
        Den tropInterp (sumB as gs).1 (sumB as gs).2 (fun x => (F x).sum)
  | [], F, gs, h => ⟨List.prefix_refl _, by simp [sumB], (den_const gs).congr fun x => by
      rw [show F x = [] by rw [← h.2 x]; rfl]; rfl⟩
  | [a], F, gs, h => by
    obtain ⟨ha, hnil, hF⟩ := h.uncons
    refine ⟨List.prefix_refl _, by simp [sumB], ha.congr fun x => ?_⟩
    rw [hF x, show (F x).tail = [] from (hnil.2 x).symm]; simp
  | a :: b :: l, F, gs, h => by
    obtain ⟨ha, hbl, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hden⟩ := sumB_spec hbl
    have hr := den_emit TropOp.add (ha.mono hp) hden
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), ?_, hr.congr fun x => ?_⟩
    · simp only [sumB, length_emit, hlen, List.length_cons]; omega
    · conv_rhs => rw [hF x]
      simp [tropInterp]

/-- Inline a list of lattice circuits, collecting their outputs. -/
theorem mapB_latB_spec :
    ∀ {Cs : List (Circuit LatOp m)} {fs : List ((Fin m → ℝ) → ℝ)} (gs : List (Gate TropOp m)),
      List.Forall₂ (fun C f => ∀ x, C.eval (latInterp ℝ 0) x = [f x]) Cs fs →
      gs <+: (mapB latB Cs gs).1 ∧
        (mapB latB Cs gs).1.length = gs.length + (Cs.map Circuit.size).sum ∧
        DenL tropInterp (mapB latB Cs gs).1 (mapB latB Cs gs).2 (fun x => fs.map (· x))
  | [], [], gs, _ => ⟨List.prefix_refl _, by simp [mapB], denL_nil gs⟩
  | C :: Cs, f :: fs, gs, List.Forall₂.cons hC hCs => by
    obtain ⟨hp, hlen, hden⟩ := latB_spec hC gs
    obtain ⟨hq, hlen', hden'⟩ := mapB_latB_spec (latB C gs).1 hCs
    refine ⟨hp.trans hq, ?_, DenL.cons (hden.mono hq) hden'⟩
    simp only [mapB, hlen', hlen, List.map_cons, List.sum_cons]; ring

/-- The circuit of Corollary F: the lattice circuits, inlined, then summed. -/
def corFCircuit (Cs : List (Circuit LatOp m)) : Circuit TropOp m :=
  let p := mapB latB Cs []
  let q := sumB p.2 p.1
  ⟨q.1, [q.2]⟩

/-- **Corollary F, upper bound, circuit form.**  Let `M` be a matroid on `Fin m` with ground
set `univ` and rank `k`.  Given lattice circuits `C₁, …, C_k`, where `C_u`, read over
`Bool`, computes the threshold `[r(S) ≥ u]`, the `(min, +, max)` circuit that inlines them
and adds their outputs has `∑_u size(C_u) + k - 1` gates and computes `h_M` at every
`w ∈ ℝ^m`. -/
theorem corollaryF_upper {M : Matroid (Fin m)} (hE : M.E = Set.univ)
    (Cs : Fin (rank M) → Circuit LatOp m)
    (hC : ∀ u, (Cs u).IsLattice ∧ MonComputes (Cs u) (rankThreshold M (u + 1))) :
    (corFCircuit (List.ofFn Cs)).size = ∑ u, (Cs u).size + (rank M - 1) ∧
      ∀ w : Fin m → ℝ, (corFCircuit (List.ofFn Cs)).eval tropInterp w = [maxBasisWeight M w] := by
  have hsug : ∀ u : Fin (rank M), ∀ x, (Cs u).eval (latInterp ℝ 0) x
      = [sugeno (rankThreshold M (u + 1)) x] := fun u x =>
    eval_eq_sugeno (rankThreshold_monotone M _) (rankThreshold_empty M (by omega))
      (rankThreshold_univ M hE (by omega)) (hC u).1 (hC u).2 0 x
  have hf : List.Forall₂ (fun C f => ∀ x, C.eval (latInterp ℝ 0) x = [f x]) (List.ofFn Cs)
      (List.ofFn fun u : Fin (rank M) => sugeno (rankThreshold M (u + 1))) := by
    rw [List.forall₂_iff_get]
    exact ⟨by simp, fun i h₁ h₂ => by simpa using hsug ⟨i, by simpa using h₁⟩⟩
  obtain ⟨-, hlen, hden⟩ := mapB_latB_spec [] hf
  obtain ⟨-, hlen', hsum⟩ := sumB_spec hden
  refine ⟨?_, fun w => ?_⟩
  · simp only [Circuit.size, corFCircuit, hlen', hlen, List.length_nil, zero_add]
    have hl : (mapB latB (List.ofFn Cs) []).2.length = rank M := by
      rw [← hden.length_eq (fun _ => 0)]; simp
    rw [hl, List.map_ofFn, List.sum_ofFn]
    rfl
  · simp only [Circuit.eval, corFCircuit, List.map_cons, List.map_nil]
    rw [hsum.2 w, maxBasisWeight_eq_sum_sugeno hE]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
    rw [Fin.sum_univ_eq_sum_range (fun u => sugeno (rankThreshold M (u + 1)) w)]

/-! ### Monotone circuits exist -/

/-- Fold a nonempty list of operands with one lattice operation. -/
def foldLatB (o : LatOp) : List (Arg n) → Bld LatOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | [a] => fun gs => (gs, a)
  | a :: b :: l => fun gs =>
    let p := foldLatB o (b :: l) gs
    emit o a p.2 p.1

theorem Arg.Proper.mono {a : Arg n} {k k' : ℕ} (h : a.Proper k) (hk : k ≤ k') : a.Proper k' := by
  cases a <;> simp_all [Arg.Proper]; omega

/-- Folding keeps the circuit proper. -/
theorem foldLatB_proper (o : LatOp) :
    ∀ {as : List (Arg n)} {gs : List (Gate LatOp n)}, as ≠ [] → ProperGates gs →
      (∀ a ∈ as, a.Proper gs.length) →
      gs <+: (foldLatB o as gs).1 ∧ ProperGates (foldLatB o as gs).1 ∧
        (foldLatB o as gs).2.Proper (foldLatB o as gs).1.length
  | [], _, h, _, _ => absurd rfl h
  | [a], gs, _, hg, ha => ⟨List.prefix_refl _, hg, ha a (by simp)⟩
  | a :: b :: l, gs, _, hg, ha => by
    obtain ⟨hp, hg', hr⟩ := foldLatB_proper o (as := b :: l) (gs := gs) (by simp) hg
      fun c hc => ha c (by simp_all)
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), properGates_concat.2 ⟨hg', ?_, hr⟩, ?_⟩
    · exact (ha a (by simp)).mono hp.length_le
    · simp only [foldLatB, emit, Arg.Proper, List.length_append, List.length_singleton]; omega

/-- The value of a fold over `Bool`. -/
def foldV : LatOp → List Bool → Bool
  | .min, l => l.all id
  | .max, l => l.any id

theorem foldLatB_spec (o : LatOp) :
    ∀ {as : List (Arg n)} {F : (Fin n → Bool) → List Bool} {gs : List (Gate LatOp n)},
      as ≠ [] → DenL (latInterp Bool false) gs as F →
      gs <+: (foldLatB o as gs).1 ∧
        Den (latInterp Bool false) (foldLatB o as gs).1 (foldLatB o as gs).2
          (fun x => foldV o (F x))
  | [], _, _, h, _ => absurd rfl h
  | [a], F, gs, _, h => by
    obtain ⟨ha, hnil, hF⟩ := h.uncons
    refine ⟨List.prefix_refl _, ha.congr fun x => ?_⟩
    rw [hF x, show (F x).tail = [] from (hnil.2 x).symm]
    cases o <;> simp [foldV, latInterp]
  | a :: b :: l, F, gs, _, h => by
    obtain ⟨ha, hbl, hF⟩ := h.uncons
    obtain ⟨hp, hden⟩ := foldLatB_spec o (as := b :: l) (by simp) hbl
    have hr := den_emit o (ha.mono hp) hden
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), hr.congr fun x => ?_⟩
    conv_rhs => rw [hF x]
    cases o <;> simp [foldV, latInterp, min_bool, max_bool]

theorem forall₂_den {Op α β : Type} {I : Interp Op α} {gs : List (Gate Op n)}
    {F : β → (Fin n → α) → α} {R : Arg n → Prop} :
    ∀ {l : List β} {rs : List (Arg n)}, List.Forall₂ (fun a r => R r ∧ Den I gs r (F a)) l rs →
      DenL I gs rs (fun x => l.map fun a => F a x) ∧ ∀ r ∈ rs, R r
  | [], [], _ => ⟨denL_nil gs, by simp⟩
  | _ :: _, _ :: _, List.Forall₂.cons h hs => by
    obtain ⟨hd, hr⟩ := forall₂_den hs
    exact ⟨DenL.cons h.2 hd, by simpa [h.1] using hr⟩

/-- One conjunction of the normal form: the minimum over the elements of `A`. -/
noncomputable def termB (A : Finset (Fin m)) : Bld LatOp m (Arg m) :=
  foldLatB .min (A.toList.map .input)

theorem termB_spec {A : Finset (Fin m)} (hA : A.Nonempty) (gs : List (Gate LatOp m))
    (hg : ProperGates gs) :
    gs <+: (termB A gs).1 ∧ ProperGates (termB A gs).1 ∧
      ((termB A gs).2.Proper (termB A gs).1.length ∧
        Den (latInterp Bool false) (termB A gs).1 (termB A gs).2
          (fun x => decide (∀ e ∈ A, x e = true))) := by
  have hne : A.toList.map Arg.input ≠ [] := by simpa using hA.ne_empty
  obtain ⟨hp, hP, hr⟩ := foldLatB_proper LatOp.min hne hg (by simp [Arg.Proper])
  obtain ⟨-, hden⟩ := foldLatB_spec LatOp.min hne
    (DenL.map (I := latInterp Bool false) _ fun i _ => den_input gs i)
  exact ⟨hp, hP, hr, hden.congr fun x => by
    rw [foldV, Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]; simp⟩

/-- A monotone circuit in disjunctive normal form: the maximum, over the sets `A` with
`g(A) = 1`, of the minimum over `A`. -/
noncomputable def dnfCircuit (g : Finset (Fin m) → Bool) : Circuit LatOp m :=
  let p := mapB termB (univ.filter fun A => g A = true).toList []
  let q := foldLatB .max p.2 p.1
  ⟨q.1, [q.2]⟩

/-- **Monotone circuits exist** for every monotone `g` with `g(∅) = 0` and `g(E) = 1`. -/
theorem exists_monCircuit {g : Finset (Fin m) → Bool} (hg : MonotoneObs g)
    (hg0 : g ∅ = false) (hg1 : g univ = true) :
    (dnfCircuit g).IsLattice ∧ MonComputes (dnfCircuit g) g := by
  set As := (univ.filter fun A => g A = true).toList
  have hAs : ∀ A ∈ As, A.Nonempty := by
    intro A hA
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [As, hg0] at hA
  obtain ⟨-, hP, hQ⟩ := mapB_gen (b := termB) ProperGates
    (fun gs A r => r.Proper gs.length ∧
      Den (latInterp Bool false) gs r (fun x => decide (∀ e ∈ A, x e = true)))
    (fun gs gs' A r hp h => ⟨h.1.mono hp.length_le, h.2.mono hp⟩) As
    (fun A hA gs hgs => termB_spec (hAs A hA) gs hgs) [] (fun k hk => absurd hk (by simp))
  obtain ⟨hden, hprop⟩ := forall₂_den hQ
  set p := mapB termB As []
  have hne : p.2 ≠ [] := by
    intro h
    have hl := hden.length_eq (fun _ => false)
    rw [h] at hl
    have hu : univ ∈ As := by simp [As, hg1]
    simp only [List.length_map, List.length_nil] at hl
    exact List.ne_nil_of_mem hu (List.eq_nil_of_length_eq_zero hl)
  obtain ⟨-, hPq, hrq⟩ := foldLatB_proper LatOp.max hne hP hprop
  obtain ⟨-, hdq⟩ := foldLatB_spec LatOp.max hne hden
  refine ⟨⟨hPq, ?_⟩, fun S => ?_⟩
  · show ∀ o ∈ [(foldLatB LatOp.max p.2 p.1).2], Arg.Proper (foldLatB LatOp.max p.2 p.1).1.length o
    simpa using hrq
  have h := hdq.2 (indicator S)
  show [Arg.read _ (indicator S) (wires _ (indicator S) (foldLatB LatOp.max p.2 p.1).1)
    (foldLatB LatOp.max p.2 p.1).2] = [g S]
  rw [h]
  simp only [foldV, List.any_map, Function.comp_def, id, List.cons.injEq, and_true]
  by_cases hS : g S = true
  · rw [hS, List.any_eq_true]
    exact ⟨S, by simp [As, hS], by simp [indicator]⟩
  · rw [Bool.not_eq_true] at hS
    rw [hS, List.any_eq_false]
    intro A hA hAS
    have hgA : g A = true := by simpa [As] using hA
    have hsub : A ⊆ S := fun e he => by simpa [indicator] using of_decide_eq_true hAS e he
    rw [hg A S hsub hgA] at hS
    exact absurd hS (by decide)

/-! ### Corollary F, with `Mon` -/

/-- `Size_{min,+,max}(h)`: the least size of a `(min, +, max)` circuit computing `h` at every
`w ∈ ℝ^m`. -/
noncomputable def tropSize (h : (Fin m → ℝ) → ℝ) : ℕ :=
  sInf {s | ∃ C : Circuit TropOp m, (∀ w, C.eval tropInterp w = [h w]) ∧ C.size = s}

theorem monSize_spec {g : Finset (Fin m) → Bool} (hg : MonotoneObs g) (hg0 : g ∅ = false)
    (hg1 : g univ = true) :
    ∃ C : Circuit LatOp m, C.IsLattice ∧ MonComputes C g ∧ C.size = monSize g := by
  have hne : {s | ∃ C : Circuit LatOp m, C.IsLattice ∧ MonComputes C g ∧ C.size = s}.Nonempty :=
    ⟨_, dnfCircuit g, (exists_monCircuit hg hg0 hg1).1, (exists_monCircuit hg hg0 hg1).2, rfl⟩
  exact Nat.sInf_mem hne

/-- **Corollary F, upper bound.**
`Size_{min,+,max}(h_M) ≤ ∑_{u=1}^{k} Mon(1[r ≥ u]) + k - 1`. -/
theorem corollaryF_upper_mon {M : Matroid (Fin m)} (hE : M.E = Set.univ) :
    tropSize (maxBasisWeight M)
      ≤ ∑ u : Fin (rank M), monSize (rankThreshold M (u + 1)) + (rank M - 1) := by
  have hC : ∀ u : Fin (rank M), ∃ C : Circuit LatOp m, C.IsLattice ∧
      MonComputes C (rankThreshold M (u + 1)) ∧ C.size = monSize (rankThreshold M (u + 1)) :=
    fun u => monSize_spec (rankThreshold_monotone M _) (rankThreshold_empty M (by omega))
      (rankThreshold_univ M hE (by omega))
  choose Cs hCs using hC
  obtain ⟨hsize, heval⟩ := corollaryF_upper hE Cs fun u => ⟨(hCs u).1, (hCs u).2.1⟩
  refine Nat.sInf_le ⟨_, heval, ?_⟩
  rw [hsize]
  simp only [(hCs _).2.2]

/-! ### Corollary F, lower bound, from Jukna, Seiwert and Sergeev -/

/-- `min_B w(B)`. -/
noncomputable def minBasisWeight (M : Matroid (Fin m)) (w : Fin m → ℝ) : ℝ :=
  sInf (basisWeights M w)

/-- The spanning predicate `Span_M(S) = [r(S) = k]`. -/
noncomputable def spanning (M : Matroid (Fin m)) (S : Finset (Fin m)) : Bool :=
  decide (rk M S = rank M)

theorem minBasisWeight_eq (M : Matroid (Fin m)) (w : Fin m → ℝ) :
    minBasisWeight M w = -maxBasisWeight M (fun e => -w e) := by
  obtain ⟨⟨B, hB, hBv⟩, hmax⟩ := isGreatest_maxBasisWeight M (fun e => -w e)
  have hleast : IsLeast (basisWeights M w) (-maxBasisWeight M fun e => -w e) := by
    refine ⟨⟨B, hB, ?_⟩, ?_⟩
    · rw [hBv, Finset.sum_neg_distrib, neg_neg]
    · rintro x ⟨B', hB', rfl⟩
      have := hmax ⟨B', hB', rfl⟩
      rw [Finset.sum_neg_distrib] at this
      linarith
  exact hleast.csInf_eq

/-- Exchange `min` and `max`. -/
def swapOp : TropOp → TropOp
  | .min => .max
  | .max => .min
  | .add => .add

/-- `(min, +, max)` gates with `min` and `max` exchanged. -/
noncomputable def tropSwapInterp : Interp TropOp ℝ := ⟨0, fun o => tropInterp.op (swapOp o)⟩

/-- The circuit with `min` and `max` exchanged. -/
def swapMinMax (C : Circuit TropOp m) : Circuit TropOp m :=
  ⟨C.gates.map fun g => ⟨swapOp g.op, g.a, g.b⟩, C.outs⟩

theorem wires_swap (x : Fin m → ℝ) :
    ∀ gs : List (Gate TropOp m),
      wires tropInterp x (gs.map fun g => ⟨swapOp g.op, g.a, g.b⟩) = wires tropSwapInterp x gs := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, wires_concat, wires_concat, ih]
    rfl

/-- **Exchanging `min` and `max`** turns a circuit for `f` into one for `w ↦ -f(-w)`. -/
theorem swap_eval (C : Circuit TropOp m) (w : Fin m → ℝ) :
    (swapMinMax C).eval tropInterp w = (C.eval tropInterp (fun e => -w e)).map Neg.neg := by
  have h := C.eval_map Neg.neg (I := tropInterp) (J := tropSwapInterp) (fun e => -w e)
    (by simp [tropInterp, tropSwapInterp]) (fun o a b => by
      cases o
      · simp only [tropInterp, tropSwapInterp, swapOp]; exact (max_neg_neg a b).symm
      · simp only [tropInterp, tropSwapInterp, swapOp]; exact (min_neg_neg a b).symm
      · simp only [tropInterp, tropSwapInterp, swapOp]; ring)
  rw [← h]
  simp only [Circuit.eval, swapMinMax, wires_swap, Function.comp_def, neg_neg]
  rfl

/-- **Corollary F, lower bound.**  Assume Jukna, Seiwert and Sergeev's Proposition 2 for the
minimum-weight basis problem of `M`: every `(min, +, max)` circuit computing `min_B w(B)` at
every `w ∈ ℝ^m` has at least `Mon(Span_M)` gates.  Then
`Mon(Span_M) ≤ Size_{min,+,max}(h_M)`. -/
theorem corollaryF_lower {M : Matroid (Fin m)} (hE : M.E = Set.univ)
    (hJSS : ∀ C : Circuit TropOp m, (∀ w, C.eval tropInterp w = [minBasisWeight M w]) →
      monSize (spanning M) ≤ C.size) :
    monSize (spanning M) ≤ tropSize (maxBasisWeight M) := by
  have hne : {s | ∃ C : Circuit TropOp m,
      (∀ w, C.eval tropInterp w = [maxBasisWeight M w]) ∧ C.size = s}.Nonempty := by
    have hC : ∀ u : Fin (rank M), ∃ C : Circuit LatOp m, C.IsLattice ∧
        MonComputes C (rankThreshold M (u + 1)) := fun u =>
      ⟨_, exists_monCircuit (rankThreshold_monotone M _) (rankThreshold_empty M (by omega))
        (rankThreshold_univ M hE (by omega))⟩
    choose Cs hCs using hC
    exact ⟨_, _, (corollaryF_upper hE Cs hCs).2, rfl⟩
  obtain ⟨C, hC, hsize⟩ := Nat.sInf_mem hne
  rw [tropSize, ← hsize]
  refine (hJSS (swapMinMax C) fun w => ?_).trans (le_of_eq (by simp [swapMinMax, Circuit.size]))
  rw [swap_eval, hC, minBasisWeight_eq]
  rfl

end SignedTropical
