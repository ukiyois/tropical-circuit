import SignedTropical.GapSum
import SignedTropical.Lift

/-!
# The compiler

`signed_assignment.tex`, Theorem `thm:compiler` and Corollary `cor:integer-observable`.

Given one Boolean circuit `B` with `N` outputs, computing `F = (F₁, …, F_N)` from the
indicator vector of its argument, the compiled circuit on input `D`:

1. sorts `D` with the insertion-sort network (`isortB`), `3 · m (m - 1) / 2` gates;
2. for each gap `k < m`: forms `Δ_k = s_{k+1} - s_k` (one gate), the `m` membership
   values `max(Δ_k - max(D_e - s_k, 0), 0) = Δ_k · 1[e ∈ G_k]` (four gates each,
   Lemma `lem:bit`), lifts `B` once at amplitude `Δ_k` (at most `3 s` gates,
   Lemma `lem:lift`), and adds the `N` lifted outputs to `N` running sums (`N` gates).

On `D ≥ 0` the `u`-th running sum ends at `∑_k Δ_k F_u(G_k) = C_{F_u}(D)`
(`compVal_eq`).  At a gap with `Δ_k = 0` every membership value and every lifted output
is `0`, so it does not matter which set the membership values describe there; in the proof
this is the case `Δ = 0` of the homomorphism lemma, and no separate argument is needed.

The size is at most `3 m s + m N + 6 m²` (`compiler_size`).  The paper's bound
`O(ms + mN + m² + m log² m)` has the extra term for Batcher's network; the insertion
network costs `O(m²)` and is absorbed by the `m²` term.

For an integer observable `f` whose `L` bits are the outputs of `B`, Horner's rule on the
`L` compiled outputs gives `∑ⱼ 2ʲ C_{bⱼ}(D) = C_f(D)` at `2 L` more gates
(`integer_observable`).  The paper applies Horner's rule inside each gap and accumulates
one sum; the order of the two summations is exchanged here, by linearity of the gap sum.
-/

open Finset

namespace SignedTropical

variable {n m : ℕ}

/-! ### Generic list builders -/

/-- Run a builder for each element of a list, collecting the results. -/
def mapB {Op β γ : Type} (b : β → Bld Op n γ) : List β → Bld Op n (List γ)
  | [] => fun gs => (gs, [])
  | a :: l => fun gs =>
    let p := b a gs
    let q := mapB b l p.1
    (q.1, p.2 :: q.2)

theorem mapB_spec {Op α β : Type} {I : Interp Op α} {b : β → Bld Op n (Arg n)} {c : ℕ}
    {F : β → (Fin n → α) → α} {gs₀ : List (Gate Op n)}
    (hb : ∀ a gs, gs₀ <+: gs → gs <+: (b a gs).1 ∧ (b a gs).1.length = gs.length + c ∧
      Den I (b a gs).1 (b a gs).2 (F a)) :
    ∀ (l : List β) (gs : List (Gate Op n)), gs₀ <+: gs →
      gs <+: (mapB b l gs).1 ∧ (mapB b l gs).1.length = gs.length + c * l.length ∧
        DenL I (mapB b l gs).1 (mapB b l gs).2 (fun x => l.map fun a => F a x)
  | [], gs, _ => ⟨List.prefix_refl _, by simp [mapB], denL_nil gs⟩
  | a :: l, gs, h0 => by
    obtain ⟨hp, hlen, hden⟩ := hb a gs h0
    obtain ⟨hq, hlen', hden'⟩ := mapB_spec hb l (b a gs).1 (h0.trans hp)
    refine ⟨hp.trans hq, by simp [mapB, hlen', hlen]; ring, DenL.cons (hden.mono hq) hden'⟩

/-- `mapB` with an arbitrary stable invariant `Q` on the results and `P` on the state. -/
theorem mapB_gen {Op β γ : Type} {b : β → Bld Op n γ} (P : List (Gate Op n) → Prop)
    (Q : List (Gate Op n) → β → γ → Prop)
    (hQ : ∀ gs gs' a r, gs <+: gs' → Q gs a r → Q gs' a r) :
    ∀ (l : List β), (∀ a ∈ l, ∀ gs, P gs → gs <+: (b a gs).1 ∧ P (b a gs).1 ∧
      Q (b a gs).1 a (b a gs).2) →
      ∀ gs, P gs → gs <+: (mapB b l gs).1 ∧ P (mapB b l gs).1 ∧
        List.Forall₂ (Q (mapB b l gs).1) l (mapB b l gs).2
  | [], _, gs, hP => ⟨List.prefix_refl _, hP, List.Forall₂.nil⟩
  | a :: l, hb, gs, hP => by
    obtain ⟨hp, hP', hQa⟩ := hb a (by simp) gs hP
    obtain ⟨hq, hP'', hQl⟩ := mapB_gen P Q hQ l (fun c hc => hb c (by simp [hc])) _ hP'
    exact ⟨hp.trans hq, hP'', List.Forall₂.cons (hQ _ _ _ _ hq hQa) hQl⟩

/-- Add two lists of operands entrywise, one gate per pair. -/
def addListsB : List (Arg n) → List (Arg n) → Bld STOp n (List (Arg n))
  | a :: as, b :: bs => fun gs =>
    let p := emit .add a b gs
    let q := addListsB as bs p.1
    (q.1, p.2 :: q.2)
  | _, _ => fun gs => (gs, [])

theorem addListsB_spec :
    ∀ {as bs : List (Arg n)} {A B : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs as A → DenL (stInterp ℝ) gs bs B →
      gs <+: (addListsB as bs gs).1 ∧
        (addListsB as bs gs).1.length = gs.length + min as.length bs.length ∧
        DenL (stInterp ℝ) (addListsB as bs gs).1 (addListsB as bs gs).2
          (fun x => List.zipWith (· + ·) (A x) (B x))
  | [], bs, A, B, gs, ha, _ => by
    refine ⟨List.prefix_refl _, by simp [addListsB], (denL_nil gs).congr fun x => ?_⟩
    rw [show A x = [] by rw [← ha.2 x]; rfl]; rfl
  | a :: as, [], A, B, gs, _, hb => by
    refine ⟨List.prefix_refl _, by simp [addListsB], (denL_nil gs).congr fun x => ?_⟩
    rw [show B x = [] by rw [← hb.2 x]; rfl]; simp
  | a :: as, b :: bs, A, B, gs, ha, hb => by
    obtain ⟨ha₀, has, hA⟩ := ha.uncons
    obtain ⟨hb₀, hbs, hB⟩ := hb.uncons
    have h₁ := den_emit STOp.add ha₀ hb₀
    obtain ⟨hq, hlen, hden⟩ := addListsB_spec (has.mono (isPrefix_emit _ _ _ gs))
      (hbs.mono (isPrefix_emit .add a b gs))
    refine ⟨(isPrefix_emit _ _ _ _).trans hq, ?_, (DenL.cons (h₁.mono hq) hden).congr ?_⟩
    · simp [addListsB, hlen, length_emit]; omega
    · intro x
      rw [hA x, hB x]
      rfl

/-! ### One gap -/

/-- The membership value at amplitude: `max(Δ - max(d - lo, 0), 0)`, four gates. -/
def bitB (d lo Δ : Arg n) : Bld STOp n (Arg n) := fun gs =>
  let p₁ := emit .sub d lo gs
  let p₂ := emit .max p₁.2 .const p₁.1
  let p₃ := emit .sub Δ p₂.2 p₂.1
  emit .max p₃.2 .const p₃.1

theorem bitB_spec {gs : List (Gate STOp n)} {d lo Δ : Arg n} {f l δ : (Fin n → ℝ) → ℝ}
    (hd : Den (stInterp ℝ) gs d f) (hlo : Den (stInterp ℝ) gs lo l)
    (hΔ : Den (stInterp ℝ) gs Δ δ) :
    gs <+: (bitB d lo Δ gs).1 ∧ (bitB d lo Δ gs).1.length = gs.length + 4 ∧
      Den (stInterp ℝ) (bitB d lo Δ gs).1 (bitB d lo Δ gs).2
        (fun x => max (δ x - max (f x - l x) 0) 0) := by
  have p₁ : gs <+: (emit STOp.sub d lo gs).1 := isPrefix_emit _ _ _ _
  have h₁ := den_emit STOp.sub hd hlo
  have h₂ := den_emit STOp.max h₁ (den_const _)
  have p₂ : (emit STOp.sub d lo gs).1 <+:
      (emit STOp.max (emit STOp.sub d lo gs).2 .const (emit STOp.sub d lo gs).1).1 :=
    isPrefix_emit _ _ _ _
  have h₃ := den_emit STOp.sub (hΔ.mono (p₁.trans p₂)) h₂
  have h₄ := den_emit STOp.max h₃ (den_const _)
  exact ⟨((p₁.trans p₂).trans (isPrefix_emit _ _ _ _)).trans (isPrefix_emit _ _ _ _),
    by simp [bitB, length_emit], h₄.congr fun x => rfl⟩

/-- The membership value `max(Δ_k - max(D_e - s_k, 0), 0)` as a function of `D`. -/
noncomputable def bitV (D : Fin m → ℝ) (k : ℕ) (e : Fin m) : ℝ :=
  max ((sortedVal D (k + 1) - sortedVal D k) - max (D e - sortedVal D k) 0) 0

/-- The lifted outputs at gap `k`. -/
noncomputable def gapOut (B : Circuit BoolOp m) (D : Fin m → ℝ) (k : ℕ) : List ℝ :=
  B.eval (liftInterp (sortedVal D (k + 1) - sortedVal D k)) (bitV D k)

/-- The membership values of query values `Q` at the gaps of the sorted values of `Λ`:
`max(Δ_k - max(Q_j - s_k, 0), 0)`, `s` the sorted values of `Λ` (`bitV D = bitQ D D`). -/
noncomputable def bitQ {q L : ℕ} (Q : Fin q → ℝ) (Λ : Fin L → ℝ) (k : ℕ) (j : Fin q) : ℝ :=
  max ((sortedVal Λ (k + 1) - sortedVal Λ k) - max (Q j - sortedVal Λ k) 0) 0

/-- The lifted outputs at gap `k` of `Λ`, at the membership values of `Q`
(`gapOut B D = gapOutQ B D D`). -/
noncomputable def gapOutQ {q L : ℕ} (B : Circuit BoolOp q) (Q : Fin q → ℝ) (Λ : Fin L → ℝ)
    (k : ℕ) : List ℝ :=
  B.eval (liftInterp (sortedVal Λ (k + 1) - sortedVal Λ k)) (bitQ Q Λ k)

/-- One gap: the gap value, the membership values, the lifted circuit, and the update of
the running sums `acc`. -/
def gapB (B : Circuit BoolOp m) (d s : List (Arg n)) (k : ℕ) (acc : List (Arg n)) :
    Bld STOp n (List (Arg n)) := fun gs =>
  let lo := (Arg.const :: s).getD k .const
  let hi := s.getD k .const
  let p₁ := emit .sub hi lo gs
  let p₂ := mapB (fun e : Fin m => bitB (d.getD e .const) lo p₁.2) (List.finRange m) p₁.1
  let p₃ := liftB B (fun e => p₂.2.getD e .const) p₁.2 p₂.1
  addListsB acc p₃.2 p₃.1

/-- Gates of one gap, with `N` running sums. -/
def gapCost (B : Circuit BoolOp m) : ℕ :=
  1 + 4 * m + (B.gates.map fun g => liftCost g.op).sum + B.outs.length

theorem length_gapOut (B : Circuit BoolOp m) (D : Fin m → ℝ) (k : ℕ) :
    (gapOut B D k).length = B.outs.length := by
  simp [gapOut, Circuit.eval]

/-- One gap, for query values `Q` and levels `Λ` carried by different operands: the gap of the
sorted values of `Λ`, the membership values of the `Q_j`, the lifted circuit and the running
sums. -/
theorem gapB_spec {B : Circuit BoolOp m} {d s acc : List (Arg n)} {k L : ℕ}
    {gs : List (Gate STOp n)} {Q : (Fin n → ℝ) → Fin m → ℝ} {Λ : (Fin n → ℝ) → Fin L → ℝ}
    {A : (Fin n → ℝ) → List ℝ}
    (hd : DenL (stInterp ℝ) gs d (fun x => List.ofFn (Q x)))
    (hs : DenL (stInterp ℝ) gs s (fun x => sortedVals (Λ x)))
    (hacc : DenL (stInterp ℝ) gs acc A) (hlen : acc.length = B.outs.length) :
    gs <+: (gapB B d s k acc gs).1 ∧
      (gapB B d s k acc gs).1.length = gs.length + gapCost B ∧
      (gapB B d s k acc gs).2.length = B.outs.length ∧
      DenL (stInterp ℝ) (gapB B d s k acc gs).1 (gapB B d s k acc gs).2
        (fun x => List.zipWith (· + ·) (A x) (gapOutQ B (Q x) (Λ x) k)) := by
  -- the operands `s_k` and `s_{k+1}`
  have hlo : Den (stInterp ℝ) gs ((Arg.const :: s).getD k .const)
      (fun x => sortedVal (Λ x) k) := (DenL.cons (den_const gs) hs).getD k
  have hhi : Den (stInterp ℝ) gs (s.getD k .const) (fun x => sortedVal (Λ x) (k + 1)) :=
    hs.getD k
  -- the gap
  set p₁ := emit STOp.sub (s.getD k .const) ((Arg.const :: s).getD k .const) gs
  have hp₁ : gs <+: p₁.1 := isPrefix_emit _ _ _ _
  have hΔ : Den (stInterp ℝ) p₁.1 p₁.2
      (fun x => sortedVal (Λ x) (k + 1) - sortedVal (Λ x) k) := den_emit STOp.sub hhi hlo
  -- the membership values
  have hde : ∀ e : Fin m, Den (stInterp ℝ) gs (d.getD e .const) (fun x => Q x e) := fun e =>
    (hd.getD e).congr fun x => by rw [List.getD_eq_getElem _ _ (by simp)]; simp
  obtain ⟨hp₂, hlen₂, hmem⟩ := mapB_spec (I := stInterp ℝ) (c := 4) (gs₀ := p₁.1)
    (F := fun e x => bitQ (Q x) (Λ x) k e)
    (fun e gs' h => bitB_spec ((hde e).mono (hp₁.trans h)) (hlo.mono (hp₁.trans h))
      (hΔ.mono h)) (List.finRange m) p₁.1 (List.prefix_refl _)
  set p₂ := mapB (fun e : Fin m => bitB (d.getD e .const) ((Arg.const :: s).getD k .const) p₁.2)
    (List.finRange m) p₁.1
  have hinp : ∀ e : Fin m, Den (stInterp ℝ) p₂.1 (p₂.2.getD e .const)
      (fun x => bitQ (Q x) (Λ x) k e) := fun e =>
    (hmem.getD e).congr fun x => by rw [List.getD_eq_getElem _ _ (by simp)]; simp
  -- the lifted circuit
  obtain ⟨hp₃, hlift⟩ := liftB_spec (B := B) (hΔ.mono hp₂) hinp
  have hlen₃ := length_liftB B (fun e => p₂.2.getD e .const) p₁.2 p₂.1
  set p₃ := liftB B (fun e => p₂.2.getD e .const) p₁.2 p₂.1
  -- the running sums
  obtain ⟨hp₄, hlen₄, hsum⟩ := addListsB_spec ((hacc.mono hp₁).mono (hp₂.trans hp₃)) hlift
  have hl3 : p₃.2.length = B.outs.length := by
    rw [← hlift.length_eq (fun _ => 0)]; simp [Circuit.eval]
  refine ⟨((hp₁.trans hp₂).trans hp₃).trans hp₄, ?_, ?_, hsum⟩
  · simp only [gapB, gapCost] at hlen₄ ⊢
    rw [hlen₄, hlen₃, hlen₂, length_emit, hlen, hl3, List.length_finRange, min_self]
    ring
  · show (addListsB acc p₃.2 p₃.1).2.length = _
    rw [← hsum.length_eq (fun _ => 0), List.length_zipWith, hacc.length_eq (fun _ => 0),
      hlen]
    simp [Circuit.eval]

/-! ### All gaps -/

/-- Process the gaps `ks` in order. -/
def gapsB (B : Circuit BoolOp m) (d s : List (Arg n)) :
    List ℕ → List (Arg n) → Bld STOp n (List (Arg n))
  | [], acc => fun gs => (gs, acc)
  | k :: ks, acc => fun gs =>
    let p := gapB B d s k acc gs
    gapsB B d s ks p.2 p.1

theorem gapsB_spec {B : Circuit BoolOp m} {d s : List (Arg n)} {L : ℕ}
    {Q : (Fin n → ℝ) → Fin m → ℝ} {Λ : (Fin n → ℝ) → Fin L → ℝ} :
    ∀ (ks : List ℕ) {acc : List (Arg n)} {A : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs d (fun x => List.ofFn (Q x)) →
      DenL (stInterp ℝ) gs s (fun x => sortedVals (Λ x)) →
      DenL (stInterp ℝ) gs acc A → acc.length = B.outs.length →
      gs <+: (gapsB B d s ks acc gs).1 ∧
        (gapsB B d s ks acc gs).1.length = gs.length + ks.length * gapCost B ∧
        DenL (stInterp ℝ) (gapsB B d s ks acc gs).1 (gapsB B d s ks acc gs).2
          (fun x => ks.foldl (fun a k => List.zipWith (· + ·) a (gapOutQ B (Q x) (Λ x) k)) (A x))
  | [], acc, A, gs, _, _, hacc, _ => ⟨List.prefix_refl _, by simp [gapsB], hacc⟩
  | k :: ks, acc, A, gs, hd, hs, hacc, hlen => by
    obtain ⟨hp, hlen₁, hlen₂, hden⟩ := gapB_spec (k := k) hd hs hacc hlen
    obtain ⟨hq, hlen₃, hden'⟩ := gapsB_spec ks (hd.mono hp) (hs.mono hp) hden hlen₂
    refine ⟨hp.trans hq, ?_, hden'⟩
    simp only [gapsB, hlen₃, hlen₁, List.length_cons]
    ring

/-! ### The compiled circuit -/

/-- The compiler as a builder, reading `D` from the operands `d`. -/
def compileB (B : Circuit BoolOp m) (d : List (Arg n)) : Bld STOp n (List (Arg n)) :=
  fun gs =>
    let p := isortB d gs
    gapsB B d p.2 (List.range m) (List.replicate B.outs.length .const) p.1

/-- What the compiled circuit computes, as a function of `D`, at every `D`. -/
noncomputable def compVal (B : Circuit BoolOp m) (D : Fin m → ℝ) : List ℝ :=
  (List.range m).foldl (fun a k => List.zipWith (· + ·) a (gapOut B D k))
    (List.replicate B.outs.length 0)

/-- Gates of the compiled circuit. -/
def compileCost (B : Circuit BoolOp m) : ℕ := 3 * (List.range m).sum + m * gapCost B

theorem compileB_spec {B : Circuit BoolOp m} {d : List (Arg n)}
    {D : (Fin n → ℝ) → Fin m → ℝ} {gs : List (Gate STOp n)}
    (hd : DenL (stInterp ℝ) gs d (fun x => List.ofFn (D x))) :
    gs <+: (compileB B d gs).1 ∧ (compileB B d gs).1.length = gs.length + compileCost B ∧
      DenL (stInterp ℝ) (compileB B d gs).1 (compileB B d gs).2 (fun x => compVal B (D x)) := by
  obtain ⟨hp, hlen, hsort⟩ := isortB_spec hd
  have hs : DenL (stInterp ℝ) (isortB d gs).1 (isortB d gs).2 (fun x => sortedVals (D x)) :=
    hsort.congr fun x => isortV_eq_insertionSort _
  have hacc : DenL (stInterp ℝ) (isortB d gs).1 (List.replicate B.outs.length .const)
      (fun _ => List.replicate B.outs.length 0) := by
    refine ⟨by simp [Arg.Valid], fun x => ?_⟩
    simp only [List.map_replicate]; rfl
  obtain ⟨hq, hlen', hden⟩ := gapsB_spec (B := B) (Q := D) (Λ := D) (List.range m) (hd.mono hp)
    hs hacc (by simp)
  refine ⟨hp.trans hq, ?_, hden⟩
  have hd_len : d.length = m := by rw [← hd.length_eq (fun _ => 0)]; simp
  simp only [compileB, hlen', hlen, compileCost, hd_len, List.length_range]
  ring

/-! ### What the compiled circuit computes on `D ≥ 0` -/

theorem sum_range_eq_list {M : Type} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ((List.range m).map g).sum = ∑ k ∈ range m, g k := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The sorting network has `m (m - 1) / 2` comparators. -/
theorem sum_range_mul_two (m : ℕ) : (List.range m).sum * 2 = m * (m - 1) := by
  have := Finset.sum_range_id_mul_two m
  rw [← List.map_id (List.range m), sum_range_eq_list]
  simpa using this

theorem foldl_zipWith_ofFn {N : ℕ} (g : ℕ → Fin N → ℝ) :
    ∀ (ks : List ℕ) (h : Fin N → ℝ),
      ks.foldl (fun a k => List.zipWith (· + ·) a (List.ofFn (g k))) (List.ofFn h)
        = List.ofFn fun u => h u + (ks.map fun k => g k u).sum
  | [], h => by simp
  | k :: ks, h => by
    rw [List.foldl_cons, show List.zipWith (· + ·) (List.ofFn h) (List.ofFn (g k))
        = List.ofFn (fun u => h u + g k u) by
        apply List.ext_getElem <;> simp,
      foldl_zipWith_ofFn g ks]
    simp only [List.map_cons, List.sum_cons, add_assoc]

/-- The lifted outputs at gap `k < m` are `Δ_k · F_u(G_k)`. -/
theorem gapOut_eq {N : ℕ} {F : Fin N → Finset (Fin m) → Bool} {B : Circuit BoolOp m}
    (hB : ∀ S, B.eval boolInterp (indicator S) = List.ofFn fun u => F u S)
    {D : Fin m → ℝ} (hD : ∀ e, 0 ≤ D e) {k : ℕ} (hk : k < m) :
    gapOut B D k = List.ofFn fun u => (sortedVal D (k + 1) - sortedVal D k)
      * if F u (threshSet D k) then 1 else 0 := by
  have hΔ : 0 ≤ sortedVal D (k + 1) - sortedVal D k :=
    sub_nonneg.2 (sortedVal_mono hD (Nat.le_succ k) hk)
  have hbit : bitV D k = fun e => ampl (sortedVal D (k + 1) - sortedVal D k)
      (indicator (threshSet D k) e) := by
    funext e
    rw [bitV, ← sub_min_eq_max, bit_identity hD e hk]
    by_cases h : e ∈ threshSet D k <;> simp [ampl, indicator, h]
  rw [gapOut, hbit, eval_liftInterp hΔ, hB, List.map_ofFn]
  congr 1
  funext u
  simp only [Function.comp, ampl]
  split_ifs <;> simp

/-- **The compiled circuit computes the gap sums on `D ≥ 0`.** -/
theorem compVal_eq {N : ℕ} {F : Fin N → Finset (Fin m) → Bool} {B : Circuit BoolOp m}
    (hB : ∀ S, B.eval boolInterp (indicator S) = List.ofFn fun u => F u S)
    {D : Fin m → ℝ} (hD : ∀ e, 0 ≤ D e) :
    compVal B D = List.ofFn fun u => gapSum (fun S => if F u S then 1 else 0) D := by
  have hN : B.outs.length = N := by
    have := congrArg List.length (hB ∅); simpa [Circuit.eval] using this
  have hfold : ∀ ks : List ℕ, (∀ k ∈ ks, k < m) →
      ks.foldl (fun a k => List.zipWith (· + ·) a (gapOut B D k))
          (List.replicate B.outs.length 0)
        = ks.foldl (fun a k => List.zipWith (· + ·) a (List.ofFn fun u =>
            (sortedVal D (k + 1) - sortedVal D k) * if F u (threshSet D k) then 1 else 0))
          (List.ofFn fun _ : Fin N => (0 : ℝ)) := by
    intro ks hks
    rw [List.ofFn_const, hN]
    suffices ∀ (ks : List ℕ) (a : List ℝ), (∀ k ∈ ks, k < m) →
        ks.foldl (fun a k => List.zipWith (· + ·) a (gapOut B D k)) a
          = ks.foldl (fun a k => List.zipWith (· + ·) a (List.ofFn fun u =>
            (sortedVal D (k + 1) - sortedVal D k) * if F u (threshSet D k) then 1 else 0)) a
      from this ks _ hks
    intro ks
    induction ks with
    | nil => intro _ _; rfl
    | cons k ks ih =>
      intro a hks
      simp only [List.foldl_cons]
      rw [gapOut_eq hB hD (hks k (by simp))]
      exact ih _ fun j hj => hks j (by simp [hj])
  rw [compVal, hfold _ (fun k hk => List.mem_range.1 hk), foldl_zipWith_ofFn]
  congr 1
  funext u
  rw [zero_add, sum_range_eq_list]
  rfl

/-! ### Theorem `thm:compiler` -/

theorem denL_ofFn_input {Op α : Type} (I : Interp Op α) (gs : List (Gate Op m)) :
    DenL I gs (List.ofFn fun e : Fin m => Arg.input e) (fun x => List.ofFn x) :=
  ⟨by simp [Arg.Valid], fun x => by simp [List.map_ofFn, Function.comp_def, Arg.read]⟩

/-- The compiled circuit, reading `D` from its inputs. -/
def compiler (B : Circuit BoolOp m) : Circuit STOp m :=
  let p := compileB B (List.ofFn fun e => .input e) []
  ⟨p.1, p.2⟩

theorem compileCost_le (B : Circuit BoolOp m) :
    compileCost B ≤ 3 * m * B.size + m * B.outs.length + 6 * m ^ 2 := by
  have hs := sum_range_mul_two m
  have hL := liftCost_sum_le B
  have hmL := Nat.mul_le_mul_left m hL
  simp only [compileCost, gapCost]
  generalize (B.gates.map fun g => liftCost g.op).sum = L at *
  generalize (List.range m).sum = s at *
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at hs; simp [hs]
  · have : m * (m - 1) + m = m * m := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    have hsq : m ^ 2 = m * m := sq m
    rw [hsq]
    nlinarith

/-- **Size of the compiled circuit**: at most `3 m s + m N + 6 m²`. -/
theorem compiler_size (B : Circuit BoolOp m) :
    (compiler B).size ≤ 3 * m * B.size + m * B.outs.length + 6 * m ^ 2 := by
  have h := (compileB_spec (B := B) (denL_ofFn_input (stInterp ℝ) [])).2.1
  simp only [Circuit.size, compiler, h, List.length_nil, zero_add]
  exact compileCost_le B

/-- **Theorem `thm:compiler`.**  Let one Boolean circuit `B` compute
`F = (F₁, …, F_N)` from the indicator vector of its argument.  Then the vector
`(C_{F₁}(D), …, C_{F_N}(D))` is computed at every `D ≥ 0` by a signed tropical circuit of
size at most `3 m s + m N + 6 m²`, where `s` is the size of `B`. -/
theorem thm_compiler {N : ℕ} (F : Fin N → Finset (Fin m) → Bool) (B : Circuit BoolOp m)
    (hB : ∀ S, B.eval boolInterp (indicator S) = List.ofFn fun u => F u S) :
    ∃ C : Circuit STOp m, C.size ≤ 3 * m * B.size + m * N + 6 * m ^ 2 ∧
      ∀ D : Fin m → ℝ, (∀ e, 0 ≤ D e) →
        C.eval (stInterp ℝ) D = List.ofFn fun u => gapSum (fun S => if F u S then 1 else 0) D := by
  have hN : B.outs.length = N := by
    have := congrArg List.length (hB ∅); simpa [Circuit.eval] using this
  refine ⟨compiler B, hN ▸ compiler_size B, fun D hD => ?_⟩
  have h := (compileB_spec (B := B) (denL_ofFn_input (stInterp ℝ) [])).2.2.eval D
  exact h.trans (compVal_eq hB hD)

/-! ### Corollary `cor:integer-observable` -/

/-- Horner's rule `c₀ + 2 (c₁ + 2 (⋯))`, two gates per entry. -/
def hornerB : List (Arg n) → Bld STOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | c :: cs => fun gs =>
    let p := hornerB cs gs
    let q := emit .add p.2 p.2 p.1
    emit .add c q.2 q.1

/-- The value computed by Horner's rule. -/
def hornerV : List ℝ → ℝ
  | [] => 0
  | c :: cs => c + (hornerV cs + hornerV cs)

theorem hornerB_spec :
    ∀ {cs : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs cs F →
      gs <+: (hornerB cs gs).1 ∧ (hornerB cs gs).1.length = gs.length + 2 * cs.length ∧
        Den (stInterp ℝ) (hornerB cs gs).1 (hornerB cs gs).2 (fun x => hornerV (F x))
  | [], F, gs, h => by
    refine ⟨List.prefix_refl _, by simp [hornerB], (den_const gs).congr fun x => ?_⟩
    rw [show F x = [] by rw [← h.2 x]; rfl]; rfl
  | c :: cs, F, gs, h => by
    obtain ⟨hc, hcs, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hv⟩ := hornerB_spec hcs
    have hq := den_emit STOp.add hv hv
    have hr := den_emit STOp.add (hc.mono (hp.trans (isPrefix_emit _ _ _ _))) hq
    refine ⟨(hp.trans (isPrefix_emit _ _ _ _)).trans (isPrefix_emit _ _ _ _),
      by simp [hornerB, length_emit, hlen]; ring, hr.congr fun x => ?_⟩
    rw [hF x]; rfl

theorem hornerV_bits : ∀ l : List Bool, hornerV (l.map fun b => if b then 1 else 0) = bitsVal l
  | [] => by simp [hornerV]
  | b :: l => by
    rw [List.map_cons, hornerV, hornerV_bits l]; cases b <;> simp <;> ring

theorem gapSum_zero (D : Fin m → ℝ) : gapSum (fun _ => 0) D = 0 := by simp [gapSum]

/-- Horner's rule commutes with the gap sum, by linearity. -/
theorem hornerV_gapSum {ι : Type} (D : Fin m → ℝ) (G : ι → Finset (Fin m) → ℝ) :
    ∀ l : List ι,
      hornerV (l.map fun i => gapSum (G i) D) = gapSum (fun S => hornerV (l.map fun i => G i S)) D
  | [] => by simp [hornerV, gapSum_zero]
  | i :: l => by
    simp only [List.map_cons, hornerV]
    rw [hornerV_gapSum D G l, gapSum_add, gapSum_add]

/-- The integer observable as a builder: the compiler followed by Horner's rule. -/
def intObsB (B : Circuit BoolOp m) (d : List (Arg n)) : Bld STOp n (Arg n) := fun gs =>
  let p := compileB B d gs
  hornerB p.2 p.1

theorem length_compVal (B : Circuit BoolOp m) (D : Fin m → ℝ) :
    (compVal B D).length = B.outs.length := by
  rw [compVal]
  suffices ∀ (ks : List ℕ) (a : List ℝ), a.length = B.outs.length →
      (ks.foldl (fun a k => List.zipWith (· + ·) a (gapOut B D k)) a).length
        = B.outs.length from this _ _ (by simp)
  intro ks
  induction ks with
  | nil => intro a h; exact h
  | cons k ks ih => intro a h; exact ih _ (by simp [h, length_gapOut])

theorem intObsB_spec {B : Circuit BoolOp m} {d : List (Arg n)}
    {D : (Fin n → ℝ) → Fin m → ℝ} {gs : List (Gate STOp n)}
    (hd : DenL (stInterp ℝ) gs d (fun x => List.ofFn (D x))) :
    gs <+: (intObsB B d gs).1 ∧
      (intObsB B d gs).1.length = gs.length + compileCost B + 2 * B.outs.length ∧
      Den (stInterp ℝ) (intObsB B d gs).1 (intObsB B d gs).2
        (fun x => hornerV (compVal B (D x))) := by
  obtain ⟨hp, hlen, hden⟩ := compileB_spec (B := B) hd
  obtain ⟨hq, hlen', hv⟩ := hornerB_spec hden
  have hl : (compileB B d gs).2.length = B.outs.length := by
    rw [← hden.length_eq (fun _ => 0), length_compVal]
  exact ⟨hp.trans hq, by simp only [intObsB, hlen', hlen, hl], hv⟩

/-- A list of bits is the list of its `getD`s. -/
theorem eq_ofFn_getD (l : List Bool) : l = List.ofFn fun u : Fin l.length => l.getD u false := by
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h₁]

/-- What the integer-observable circuit computes on `D ≥ 0`. -/
theorem hornerV_compVal {f : Finset (Fin m) → ℕ} {B : Circuit BoolOp m}
    (hB : ∀ S, bitsVal (B.eval boolInterp (indicator S)) = f S) {D : Fin m → ℝ}
    (hD : ∀ e, 0 ≤ D e) :
    hornerV (compVal B D) = gapSum (fun S => (f S : ℝ)) D := by
  set N := B.outs.length
  have hlen : ∀ S, (B.eval boolInterp (indicator S)).length = N := fun S => by
    simp [Circuit.eval, N]
  have hB' : ∀ S, B.eval boolInterp (indicator S)
      = List.ofFn fun u : Fin N => (B.eval boolInterp (indicator S)).getD u false := by
    intro S
    conv_lhs => rw [eq_ofFn_getD (B.eval boolInterp (indicator S))]
    rw [hlen S]
  rw [compVal_eq hB' hD, List.ofFn_eq_map, hornerV_gapSum]
  congr 1
  funext S
  rw [← hB S, ← hornerV_bits]
  congr 1
  conv_rhs => rw [hB' S, List.ofFn_eq_map, List.map_map]
  rfl

/-- The integer-observable circuit, reading `D` from its inputs. -/
def intObsCircuit (B : Circuit BoolOp m) : Circuit STOp m :=
  let p := intObsB B (List.ofFn fun e => .input e) []
  ⟨p.1, [p.2]⟩

/-- **Corollary `cor:integer-observable`.**  Let `f : 2^E → ℕ` and let one Boolean circuit
`B` of size `s` output the `L` bits of `f`, least significant first.  Then
`C_f(D) = ∑_k (s_{k+1} - s_k) f(G_k)` is computed at every `D ≥ 0` by a signed tropical
circuit of size at most `3 m s + m L + 6 m² + 2 L`. -/
theorem integer_observable (f : Finset (Fin m) → ℕ) (B : Circuit BoolOp m)
    (hB : ∀ S, bitsVal (B.eval boolInterp (indicator S)) = f S) :
    (intObsCircuit B).size
        ≤ 3 * m * B.size + m * B.outs.length + 6 * m ^ 2 + 2 * B.outs.length ∧
      ∀ D : Fin m → ℝ, (∀ e, 0 ≤ D e) →
        (intObsCircuit B).eval (stInterp ℝ) D = [gapSum (fun S => (f S : ℝ)) D] := by
  obtain ⟨-, hlen, hden⟩ := intObsB_spec (B := B) (denL_ofFn_input (stInterp ℝ) [])
  refine ⟨?_, fun D hD => ?_⟩
  · have h1 : (intObsCircuit B).size = compileCost B + 2 * B.outs.length := by
      simp [Circuit.size, intObsCircuit, hlen]
    have := compileCost_le B
    omega
  · have h := hden.2 D
    simp only at h
    simp only [Circuit.eval, intObsCircuit, List.map_cons, List.map_nil, h,
      hornerV_compVal hB hD]

end SignedTropical
