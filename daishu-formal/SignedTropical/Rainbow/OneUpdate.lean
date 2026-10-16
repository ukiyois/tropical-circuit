import SignedTropical.Rainbow.GapUpdate
import SignedTropical.Rainbow.ObserverOracle
import SignedTropical.LevelCompiler

/-!
# Lemma `lem:oneupdate`: one PO-SL update as a signed tropical circuit

`greedy_intersection.tex`, Section 4.7, Lemma `lem:oneupdate`.  `M : Matroid (Fin m)` has ground
set `univ`, rank `k` and a rainbow base, the blocks are the fibres of `blk : Fin m → Fin k`, and a
Boolean circuit `C` of size `s` outputs the binary digits of the rank of `M`.

* `IsObserver M blk r O`: the Boolean circuit `O` on the `qn m` event bits of
  `Rainbow/Events.lean` outputs at the event bits of every `t ≥ 0` the `k` bits
  `F_b = [ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]` of Lemma `lem:observer`.
* `updCircuit M C blk O`, a signed tropical circuit on the `m + k` inputs `(w, p)`
  (`Fin.append w p`), in the steps of the proof of the lemma:
  1. `v = w - p_blk` (`m` gates);
  2. the levels and the query values: the entry times (`entryB`), at a nonloop `x` from
     `D^x_g = max(v_x - v_g, 0)` (`2m` gates) and the compiler of Theorem `thm:compiler` with the
     Boolean circuit `closCircuit C x` of `[x ∈ cl(E - S)]` (two rank queries, `closCost m s`
     gates), `0` at a loop; the weights `W` (`wB`, five gates per pair), the merge times `T` by
     the Floyd–Warshall algorithm over `(min, max)` (`fwB`, four gates per entry and pivot), the
     values `ρ_x = min_{y < x} T_xy` (`rhoB`, three gates per `min`) and the order values `U_xy`
     (`uB`, six gates per pair);
  3. the update as a sum over the levels (`GapUpdate.update_eq_levSum`, no gate);
  4. the compiler at the `2m` levels `t_x, ρ_x` (`levB` of `LevelCompiler.lean`) with `O` on the
     query values `t_x, T_xy, U_xy`;
  5. `p + a` (`k` gates).
  Its size is `m + evCost M C + levCost O (m + m) + k` (`updCircuit_spec`).
* The computed values are the levels and the query values of `Rainbow/Events.lean`
  (`entry_eq_compVal`, `fw_eq_bq`, `rho_eq`, `u_eq`), so by `levVal_eq` and
  `GapUpdate.update_eq_levSum` the outputs are `p + a` at every state of stage `r`
  (`updV_eq_update`, `updCircuit_eval`, `oneUpdate`).
* The size is at most `6 m s_O + updOver m k s`, with
  `updOver m k s = 6 m² s + 29 m³ + 15 m² ⌈log₂(m+1)⌉ + 43 m² + 3 m + 2 m k + k`
  (`updCircuit_size_le`): `2m` lifted copies of the observer, against `m²` for the compiler on all
  ordered pairs.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremC

open SignedTropical.Rainbow SignedTropical.Rainbow.Events SignedTropical.BoolAlg

variable {m k n : ℕ}

/-! ### Observers -/

/-- `O` is an observer for stage `r` (Lemma `lem:observer`): a Boolean circuit on the `qn m` event
bits whose outputs at the event bits `[Q_j ≤ t]` of every `t ≥ 0` are the `k` bits
`F_b = [ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]`, `b = 0, …, k - 1`. -/
def IsObserver (M : Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (O : Circuit BoolOp (qn m)) :
    Prop :=
  ∀ (v : Fin m → ℝ) (t : ℝ), 0 ≤ t →
    O.eval boolInterp (fun j => decide (Qv M v j ≤ t)) =
      List.ofFn fun b : Fin k =>
        decide (nu (POSL.N M v t) blk ≤ r ∧ b ∈ Av (POSL.N M v t) blk)

/-- An observer of stage `r` has `k` outputs. -/
theorem IsObserver.length_outs {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (qn m)} (hO : IsObserver M blk r O) : O.outs.length = k := by
  simpa [Circuit.eval] using congrArg List.length (hO 0 0 le_rfl)

/-- Entry `i` of `List.ofFn f` is `f i`. -/
theorem getD_ofFn {α : Type} {r : ℕ} (f : Fin r → α) (d : α) (i : Fin r) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-! ### Gadgets over `max`, `+`, `-` -/

/-- One real number, carried by one operand. -/
abbrev argR : Rep STOp ℝ n (Arg n) ℝ := Rep.arg (stInterp ℝ)

/-- A vector of reals, carried by a family of operands. -/
abbrev realsR (r : ℕ) : Rep STOp ℝ n (Fin r → Arg n) (Fin r → ℝ) := Rep.pi (Fin r) argR

/-- A square matrix of reals. -/
abbrev matsR (r : ℕ) : Rep STOp ℝ n (Fin r → Fin r → Arg n) (Fin r → Fin r → ℝ) :=
  Rep.pi (Fin r) (realsR r)

/-- One gate. -/
theorem emitST_impl (o : STOp) :
    Impl (argR.prod argR) (argR (n := n)) (fun p => emit o p.1 p.2) 1
      (fun P => (stInterp ℝ).op o P.1 P.2) :=
  fun _ _ _ hs => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, den_emit o hs.1 hs.2⟩

/-- `min(a, b) = (a + b) - max(a, b)`, three gates (the comparator of `Sorting.lean`). -/
def minB (p : Arg n × Arg n) : Bld STOp n (Arg n) := fun gs =>
  ((cmpB p.1 p.2 gs).1, (cmpB p.1 p.2 gs).2.1)

/-- `min(a, b)`, three gates. -/
theorem minB_impl : Impl (argR.prod argR) (argR (n := n)) minB 3 (fun P => min P.1 P.2) :=
  fun _ _ _ hs => let h := cmpB_spec hs.1 hs.2; ⟨h.1, h.2.1, h.2.2.1⟩

/-! ### Step 1, `v = w - p_blk` -/

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

/-! ### Step 2, the entry times -/

section Entry

variable {M : Matroid (Fin m)} {C : Circuit BoolOp m}

/-- `x ∉ cl(U)` iff adding `x` raises the rank. -/
theorem notMem_closure_iff_rk_lt (hE : M.E = Set.univ) (U : Finset (Fin m)) (x : Fin m) :
    x ∉ M.closure (U : Set (Fin m)) ↔ rk M U < rk M (insert x U) := by
  constructor
  · intro hx
    have h := M.eRk_insert_eq_add_one (e := x) (X := (U : Set (Fin m))) ⟨by simp [hE], hx⟩
    rw [← coe_insert, ← coe_rk, ← coe_rk] at h
    have h' : rk M (insert x U) = rk M U + 1 := by exact_mod_cast h
    omega
  · intro hlt hcl
    have h : rk M (U ∪ {x}) = rk M U :=
      POSL.rk_union_of_subset_closure (by rw [coe_singleton, Set.singleton_subset_iff]; exact hcl)
    rw [union_comm, ← insert_eq] at h
    omega

/-- `D^x_g = max(v_x - v_g, 0)`: two gates per `g`. -/
def dxB (x : Fin m) (v : Fin m → Arg n) : Bld STOp n (Fin m → Arg n) :=
  tabB fun g gs =>
    let q := emit .sub (v x) (v g) gs
    emit .max q.2 .const q.1

/-- `dxB x` implements `v ↦ D^x` with `2m` gates. -/
theorem dxB_impl (x : Fin m) :
    Impl (realsR m) (realsR (n := n) m) (dxB x) (m * 2) (fun v => dx v x) := by
  refine Impl.tab fun g => ?_
  intro gs s T hs
  have h₁ := den_emit STOp.sub (hs x) (hs g)
  have h₂ := den_emit STOp.max h₁ (den_const _)
  exact ⟨(isPrefix_emit _ _ _ _).trans (isPrefix_emit _ _ _ _), by simp [length_emit], h₂⟩

/-- `[x ∈ cl(E - S)]` from the bits of `S`: the complement (`m` gates), the constant `true`, two
rank queries (without and with `x`), a comparison and a negation. -/
def closB (C : Circuit BoolOp m) (x : Fin m) : (Fin m → Arg n) → Bld BoolOp n (Fin 1 → Arg n) :=
  seqB (seqB (pairB vecNotB fun _ => emit .not .const .const)
    (seqB (pairB (fun q => Observer.rankB C q.1)
      fun q => Observer.rankB C fun g => if g = x then q.2 else q.1 g)
      (seqB numLtB fun a => emit .not a .const))) (pureB fun b _ => b)

/-- The gates of `closB`: `m + 2s + 5⌈log₂(m+1)⌉ + 4`. -/
def closCost (m s : ℕ) : ℕ := m + 2 * s + 5 * Nat.size m + 4

/-- `closB C x` computes `¬[r(U) < r(U + x)]`, `U = E - S`, with `closCost m s` gates. -/
theorem closB_impl
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (x : Fin m) :
    Impl (vecR m) (vecR (n := n) 1) (closB C x) (closCost m C.size)
      (fun S _ => !decide (rk M (univ.filter fun g => (!S g) = true) <
        rk M (univ.filter fun g => (if g = x then true else !S g) = true))) := by
  have hA := (vecNotB_impl (n := n) (r := m)).pair (true_impl (vecR m))
  have hB₁ := (Observer.rankB_impl (n := n) hB).pre (R := (vecR m).prod bitR) (g := Prod.fst)
    (G := Prod.fst) fun _ _ _ hs => hs.1
  have hB₂ := (Observer.rankB_impl (n := n) hB).pre (R := (vecR m).prod bitR)
    (g := fun q g => if g = x then q.2 else q.1 g)
    (G := fun Q g => if g = x then Q.2 else Q.1 g) fun _ _ _ hs g => by
      dsimp only
      split_ifs
      exacts [hs.2, hs.1 g]
  have hD := Impl.free (n := n) (R₁ := bitR) (R₂ := vecR 1) (g := fun b _ => b)
    (F := fun B _ => B) fun _ _ _ hs _ => hs
  exact ((hA.comp ((hB₁.pair hB₂).comp ((numLtB_impl _ _).comp emitNot_impl))).comp hD).cost
    (by rw [closCost, max_self]; ring)

/-- The Boolean circuit of `[x ∈ cl(E - S)]`. -/
def closCircuit (C : Circuit BoolOp m) (x : Fin m) : Circuit BoolOp m :=
  vecCircuit (closB C x)

open Classical in
/-- **The closure circuit**: `closCost m s` gates, and at the indicator vector of `S` its output is
`[x ∈ cl(E - S)]`. -/
theorem closCircuit_spec (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (x : Fin m) :
    (closCircuit C x).size = closCost m C.size ∧ (closCircuit C x).outs.length = 1 ∧
      ∀ S : Finset (Fin m), (closCircuit C x).eval boolInterp (indicator S) =
        List.ofFn fun _ : Fin 1 =>
          decide (x ∈ M.closure ((univ \ S : Finset (Fin m)) : Set (Fin m))) := by
  obtain ⟨hs, hl, he⟩ := vecCircuit_spec (closB_impl (n := m) hB x)
  refine ⟨hs, hl, fun S => ?_⟩
  rw [closCircuit, he]
  congr 1
  funext _
  have h₁ : (univ.filter fun g => (!indicator S g) = true) = univ \ S := by
    ext g; simp [indicator]
  have h₂ : (univ.filter fun g => (if g = x then true else !indicator S g) = true) =
      insert x (univ \ S) := by
    ext g; by_cases hg : g = x <;> simp [indicator, hg]
  rw [h₁, h₂]
  have hiff := notMem_closure_iff_rk_lt hE (univ \ S) x
  by_cases h : x ∈ M.closure ((univ \ S : Finset (Fin m)) : Set (Fin m))
  · have hn : ¬rk M (univ \ S) < rk M (insert x (univ \ S)) := fun hlt => hiff.2 hlt h
    rw [decide_eq_false hn, Bool.not_false, eq_comm, decide_eq_true_iff]
    exact h
  · rw [decide_eq_true (hiff.1 h), Bool.not_true, eq_comm, decide_eq_false_iff_not]
    exact h

/-- The compiler of Theorem `thm:compiler` as an implementation. -/
theorem compileB_impl {r : ℕ} (B : Circuit BoolOp r) :
    Impl (realsR r) (Rep.list (stInterp ℝ) B.outs.length)
      (fun d => compileB (n := n) B (List.ofFn d)) (compileCost B) (compVal B) := by
  intro gs d D hd
  obtain ⟨hp, hl, hden⟩ := compileB_spec (B := B) (denL_ofFn hd)
  exact ⟨hp, hl, by rw [← hden.length_eq fun _ => 0, length_compVal], hden⟩

open Classical in
/-- **The entry time from the compiler**: for a nonloop `x`, the compiled gap sum of the closure
circuit at `D^x` is `t_x`. -/
theorem entry_eq_compVal (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (v : Fin m → ℝ) (x : Fin m) :
    (compVal (closCircuit C x) (dx v x)).getD 0 0 = entry M v x := by
  classical
  rw [compVal_eq (closCircuit_spec hE hB x).2.2 (dx_nonneg v x),
    show (0 : ℕ) = ((0 : Fin 1) : ℕ) from rfl, getD_ofFn, entry]
  simp only [decide_eq_true_eq]

open Classical in
/-- The entry time of `x` from `v`: `0` at a loop (no gate); otherwise `D^x` and the compiler with
`closCircuit C x`. -/
noncomputable def entryB (M : Matroid (Fin m)) (C : Circuit BoolOp m) (x : Fin m) :
    (Fin m → Arg n) → Bld STOp n (Arg n) := fun v =>
  if x ∈ M.closure ∅ then pureB (fun _ => .const) v
  else seqB (dxB x) (seqB (fun d => compileB (closCircuit C x) (List.ofFn d))
    (pureB fun as => as.getD 0 .const)) v

open Classical in
/-- The gates of `entryB`. -/
noncomputable def entryCost (M : Matroid (Fin m)) (C : Circuit BoolOp m) (x : Fin m) : ℕ :=
  if x ∈ M.closure ∅ then 0 else m * 2 + compileCost (closCircuit C x)

open Classical in
/-- **The entry times**: `entryB` computes `t_x` (`0` at a loop) with `entryCost` gates. -/
theorem entryB_impl (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (x : Fin m) :
    Impl (realsR m) (argR (n := n)) (entryB M C x) (entryCost M C x) (fun v => tz M v x) := by
  have h := MI.impl_ite (x ∈ M.closure ∅)
    (Impl.free (R₁ := realsR m) (R₂ := argR (n := n)) (g := fun _ => .const) (F := fun _ => 0)
      fun gs _ _ _ => den_const gs)
    (((dxB_impl x).comp ((compileB_impl (closCircuit C x)).comp
      (Impl.free (R₁ := Rep.list (stInterp ℝ) _) (R₂ := argR) (g := fun as => as.getD 0 .const)
        (F := fun A => A.getD 0 0) fun _ _ _ hs => hs.2.getD 0))).cost
      (c' := m * 2 + compileCost (closCircuit C x)) (by ring))
  refine h.congr fun v => ?_
  by_cases hx : x ∈ M.closure ∅
  · simp [tz, hx]
  · simp only [if_neg hx, tz]
    exact entry_eq_compVal hE hB v x

end Entry

/-! ### Step 2, the merge times, the values `ρ` and the order values -/

section Merge

variable {M : Matroid (Fin m)}

/-- One off-diagonal weight, five gates: `max(max(t_a, t_b), max(v_a - v_b, v_b - v_a))`, from
`(v, t)`. -/
def wOneB (a b : Fin m) : (Fin m → Arg n) × (Fin m → Arg n) → Bld STOp n (Arg n) :=
  seqB (pairB (fun p => emit .max (p.2 a) (p.2 b))
    (seqB (pairB (fun p => emit .sub (p.1 a) (p.1 b)) fun p => emit .sub (p.1 b) (p.1 a))
      fun q => emit .max q.1 q.2)) fun q => emit .max q.1 q.2

/-- One weight, five gates. -/
theorem wOneB_impl (a b : Fin m) :
    Impl ((realsR m).prod (realsR m)) (argR (n := n)) (wOneB a b) 5
      (fun P => max (max (P.2 a) (P.2 b)) |P.1 a - P.1 b|) :=
  (((((emitST_impl STOp.max).pre (R := (realsR m).prod (realsR m))
    (g := fun p => (p.2 a, p.2 b)) (G := fun P => (P.2 a, P.2 b))
    fun _ _ _ hs => ⟨hs.2 a, hs.2 b⟩).pair
    ((((emitST_impl STOp.sub).pre (R := (realsR m).prod (realsR m))
      (g := fun p => (p.1 a, p.1 b)) (G := fun P => (P.1 a, P.1 b))
      fun _ _ _ hs => ⟨hs.1 a, hs.1 b⟩).pair
      ((emitST_impl STOp.sub).pre (R := (realsR m).prod (realsR m))
        (g := fun p => (p.1 b, p.1 a)) (G := fun P => (P.1 b, P.1 a))
        fun _ _ _ hs => ⟨hs.1 b, hs.1 a⟩)).comp (emitST_impl STOp.max))).comp
    (emitST_impl STOp.max)).cost (by norm_num)).congr fun P => by
      simp only [stInterp]
      rw [abs_eq_max_neg, neg_sub]

open Classical in
/-- The weights from `(v, t)`: `t_a` on the diagonal (no gate), five gates for every other pair,
kept within components (`0` elsewhere). -/
noncomputable def wB (M : Matroid (Fin m)) (p : (Fin m → Arg n) × (Fin m → Arg n)) :
    Bld STOp n (Fin m → Fin m → Arg n) := fun gs =>
  let q := (tabB fun a => tabB fun b =>
    if a = b then pureB (fun p : (Fin m → Arg n) × (Fin m → Arg n) => p.2 a) p
    else wOneB a b p) gs
  (q.1, fun a b => if a = b then q.2 a b else if Kr M a b then q.2 a b else .const)

open Classical in
/-- The value of `wB`. -/
noncomputable def wV (M : Matroid (Fin m)) (v t : Fin m → ℝ) (a b : Fin m) : ℝ :=
  if a = b then t a else if Kr M a b then max (max (t a) (t b)) |v a - v b| else 0

/-- **The weights**, `5 m (m - 1)` gates. -/
theorem wB_impl :
    Impl ((realsR m).prod (realsR m)) (matsR (n := n) m) (wB M) (m * (m - 1) * 5)
      (fun P => wV M P.1 P.2) := by
  classical
  have h := (Impl.tabSum (R := (realsR m).prod (realsR m)) fun a => Impl.tabSum fun b =>
    MI.impl_ite (a = b)
      (Impl.free (R₁ := (realsR m).prod (realsR m)) (R₂ := argR (n := n)) (g := fun p => p.2 a)
        (F := fun P => P.2 a) fun _ _ _ hs => hs.2 a) (wOneB_impl a b)).post
    (R₃ := matsR m)
    (g := fun q a b => if a = b then q a b else if Kr M a b then q a b else .const)
    (G := fun Q a b => if a = b then Q a b else if Kr M a b then Q a b else 0)
    fun gs _ _ hs a b => by
      dsimp only
      split_ifs
      exacts [hs a b, hs a b, den_const gs]
  refine (h.cost (MI.sum_offDiag 5)).congr fun P => ?_
  funext a b
  simp only [wV]
  split_ifs <;> simp_all

/-- One entry of a round of Floyd–Warshall: `min(T_ab, max(T_ac, T_cb))`, four gates. -/
def fwOneB : Arg n × Arg n × Arg n → Bld STOp n (Arg n) :=
  seqB (pairB (pureB fun p => p.1) fun p => emit .max p.2.1 p.2.2) minB

theorem fwOneB_impl :
    Impl (argR.prod (argR.prod argR)) (argR (n := n)) fwOneB 4
      (fun P => min P.1 (max P.2.1 P.2.2)) :=
  ((((Impl.free (R₁ := argR.prod (argR.prod argR)) (R₂ := argR) (g := fun p => p.1)
    (F := fun P => P.1) fun _ _ _ hs => hs.1).pair
    ((emitST_impl STOp.max).pre (R := argR.prod (argR.prod argR))
      (g := fun p => (p.2.1, p.2.2)) (G := fun P => (P.2.1, P.2.2))
      fun _ _ _ hs => ⟨hs.2.1, hs.2.2⟩)).comp minB_impl).cost (by norm_num))

open Classical in
/-- One round of the Floyd–Warshall algorithm over `(min, max)` with pivot `c`: four gates per
entry; the new value is kept on the entries `(a, b)` with `Kr M a c` and `Kr M c b`. -/
noncomputable def fwStepB (M : Matroid (Fin m)) (c : Fin m) (T : Fin m → Fin m → Arg n) :
    Bld STOp n (Fin m → Fin m → Arg n) := fun gs =>
  let q := (tabB fun a => tabB fun b => fwOneB (T a b, T a c, T c b)) gs
  (q.1, fun a b => if Kr M a c ∧ Kr M c b then q.2 a b else T a b)

/-- One round, `4m²` gates. -/
theorem fwStepB_impl (c : Fin m) :
    Impl (matsR m) (matsR (n := n) m) (fwStepB M c) (m * (m * 4)) (fwStep (Kr M) c) := by
  classical
  intro gs T V hT
  obtain ⟨hp, hl, hr⟩ := (Impl.tab (R := matsR m) fun a => Impl.tab fun b =>
    fwOneB_impl.pre (R := matsR m) (g := fun T => (T a b, T a c, T c b))
      (G := fun V => (V a b, V a c, V c b)) fun _ _ _ hs => ⟨hs a b, hs a c, hs c b⟩) hT
  refine ⟨hp, hl, fun a b => ?_⟩
  show Den (stInterp ℝ) _ (if Kr M a c ∧ Kr M c b then _ else T a b) _
  by_cases h : Kr M a c ∧ Kr M c b
  · rw [if_pos h]
    exact Rep.congr argR (hr a b) fun z => by simp [fwStep, h]
  · rw [if_neg h]
    exact Rep.congr argR ((hT a b).mono hp) fun z => by simp [fwStep, h]

/-- The Floyd–Warshall algorithm over `(min, max)`: one round per pivot. -/
noncomputable def fwB (M : Matroid (Fin m)) :
    (Fin m → Fin m → Arg n) → Bld STOp n (Fin m → Fin m → Arg n) :=
  foldB (fwStepB M) (List.finRange m)

/-- **The merge times**, `4m³` gates. -/
theorem fwB_impl :
    Impl (matsR m) (matsR (n := n) m) (fwB M) (m * (m * (m * 4))) (fwV (Kr M)) :=
  ((Impl.fold (l := List.finRange m) fun c _ => fwStepB_impl c).cost
    (by rw [List.length_finRange])).congr fun _ => rfl

/-- A chain of `min` gates from `a` over `l`. -/
def minChainB : List (Arg n) → Arg n → Bld STOp n (Arg n)
  | [], a => fun gs => (gs, a)
  | b :: l, a => fun gs =>
    let q := minB (a, b) gs
    minChainB l q.2 q.1

theorem minChainB_spec : ∀ (l : List (Arg n)) {a : Arg n} {f : (Fin n → ℝ) → ℝ}
    {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
    Den (stInterp ℝ) gs a f → DenL (stInterp ℝ) gs l F →
    gs <+: (minChainB l a gs).1 ∧ (minChainB l a gs).1.length = gs.length + 3 * l.length ∧
      Den (stInterp ℝ) (minChainB l a gs).1 (minChainB l a gs).2
        (fun x => (F x).foldl min (f x))
  | [], a, f, F, gs, ha, hl => ⟨List.prefix_refl _, by simp [minChainB],
      ha.congr fun x => by rw [show F x = [] by rw [← hl.2 x]; rfl]; rfl⟩
  | b :: l, a, f, F, gs, ha, hbl => by
    obtain ⟨hb, hl, hF⟩ := hbl.uncons
    obtain ⟨hp, hlen, hmin⟩ := minB_impl (n := n) (s := (a, b))
      (T := fun x => (f x, (F x).headD 0)) ⟨ha, hb⟩
    obtain ⟨hq, hlen', hv⟩ := minChainB_spec l hmin (hl.mono hp)
    refine ⟨hp.trans hq, by simp only [minChainB, hlen', hlen, List.length_cons]; ring,
      hv.congr fun x => ?_⟩
    conv_rhs => rw [hF x]
    rfl

/-- The minimum of a list of operands: the constant `0` for the empty list, else a chain of
`min` gates. -/
def minListB : List (Arg n) → Bld STOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | a :: l => minChainB l a

theorem minListB_spec {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)}
    (hl : DenL (stInterp ℝ) gs l F) :
    gs <+: (minListB l gs).1 ∧ (minListB l gs).1.length = gs.length + 3 * (l.length - 1) ∧
      Den (stInterp ℝ) (minListB l gs).1 (minListB l gs).2 (fun x => listMin (F x)) := by
  cases l with
  | nil =>
    refine ⟨List.prefix_refl _, by simp [minListB], (den_const gs).congr fun x => ?_⟩
    rw [show F x = [] by rw [← hl.2 x]; rfl]
    rfl
  | cons a l =>
    obtain ⟨ha, hl', hF⟩ := hl.uncons
    obtain ⟨hp, hlen, hv⟩ := minChainB_spec l ha hl'
    refine ⟨hp, by simp only [minListB, hlen, List.length_cons, Nat.add_sub_cancel], hv.congr
      fun x => ?_⟩
    conv_rhs => rw [hF x]
    rfl

/-- The values `ρ_x = min_{y < x, Kr M x y} T_xy`, `0` if there is no such `y`. -/
noncomputable def rhoB (M : Matroid (Fin m)) (T : Fin m → Fin m → Arg n) :
    Bld STOp n (Fin m → Arg n) :=
  tabB fun x => minListB ((lower M x).map (T x))

/-- **The values `ρ`**: `3 (|lower x| - 1)` gates for each `x`. -/
theorem rhoB_impl :
    Impl (matsR m) (realsR (n := n) m) (rhoB M) (∑ x, 3 * ((lower M x).length - 1))
      (fun V x => listMin ((lower M x).map (V x))) := by
  refine Impl.tabSum (R := matsR m) fun x => ?_
  intro gs T V hT
  obtain ⟨hp, hl, hv⟩ := minListB_spec (DenL.map (G := fun y z => V z x y) (lower M x)
    fun y _ => hT x y)
  exact ⟨hp, by rw [hl, List.length_map], hv⟩

/-- One order value, six gates: `max(max(t_x, t_y), min(T_xy, v_y - v_x))`, from `(v, t, T)`. -/
def uOneB (x y : Fin m) :
    (Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n) → Bld STOp n (Arg n) :=
  seqB (pairB (fun p => emit .max (p.2.1 x) (p.2.1 y))
    (seqB (pairB (pureB fun p => p.2.2 x y) fun p => emit .sub (p.1 y) (p.1 x)) minB))
    fun q => emit .max q.1 q.2

theorem uOneB_impl (x y : Fin m) :
    Impl ((realsR m).prod ((realsR m).prod (matsR m))) (argR (n := n)) (uOneB x y) 6
      (fun P => max (max (P.2.1 x) (P.2.1 y)) (min (P.2.2 x y) (P.1 y - P.1 x))) :=
  (((((emitST_impl STOp.max).pre (R := (realsR m).prod ((realsR m).prod (matsR m)))
    (g := fun p => (p.2.1 x, p.2.1 y)) (G := fun P => (P.2.1 x, P.2.1 y))
    fun _ _ _ hs => ⟨hs.2.1 x, hs.2.1 y⟩).pair
    (((Impl.free (R₁ := (realsR m).prod ((realsR m).prod (matsR m))) (R₂ := argR)
      (g := fun p => p.2.2 x y) (F := fun P => P.2.2 x y) fun _ _ _ hs => hs.2.2 x y).pair
      ((emitST_impl STOp.sub).pre (R := (realsR m).prod ((realsR m).prod (matsR m)))
        (g := fun p => (p.1 y, p.1 x)) (G := fun P => (P.1 y, P.1 x))
        fun _ _ _ hs => ⟨hs.1 y, hs.1 x⟩)).comp minB_impl)).comp
    (emitST_impl STOp.max)).cost (by norm_num))

open Classical in
/-- The order values from `(v, t, T)`: six gates per pair, kept within components. -/
noncomputable def uB (M : Matroid (Fin m))
    (p : (Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n)) :
    Bld STOp n (Fin m → Fin m → Arg n) := fun gs =>
  let q := (tabB fun x => tabB fun y => uOneB x y p) gs
  (q.1, fun x y => if Kr M x y then q.2 x y else .const)

open Classical in
/-- The value of `uB`. -/
noncomputable def uV (M : Matroid (Fin m)) (v t : Fin m → ℝ) (T : Fin m → Fin m → ℝ)
    (x y : Fin m) : ℝ :=
  if Kr M x y then max (max (t x) (t y)) (min (T x y) (v y - v x)) else 0

/-- **The order values**, `6m²` gates. -/
theorem uB_impl :
    Impl ((realsR m).prod ((realsR m).prod (matsR m))) (matsR (n := n) m) (uB M) (m * (m * 6))
      (fun P => uV M P.1 P.2.1 P.2.2) := by
  classical
  have h := (Impl.tab (R := (realsR m).prod ((realsR m).prod (matsR m))) fun x => Impl.tab
    fun y => uOneB_impl (n := n) x y).post (R₃ := matsR m)
    (g := fun q x y => if Kr M x y then q x y else .const)
    (G := fun Q x y => if Kr M x y then Q x y else 0)
    fun gs _ _ hs x y => by
      dsimp only
      split_ifs
      exacts [hs x y, den_const gs]
  exact h.congr fun P => rfl

/-! #### The computed values are the levels and the query values -/

/-- The weights read at the entry times agree with `W` within components. -/
theorem wV_eq_wgt (v : Fin m → ℝ) {a b : Fin m} (hab : Kr M a b) :
    wV M v (tz M v) a b = wgt M v a b := by
  unfold wV wgt tz
  by_cases he : a = b
  · subst he
    simp [hab.2.1]
  · simp [he, hab, hab.2.1, hab.2.2]

/-- **The merge values**: the computed `T` is `T_xy` within components and `0` elsewhere. -/
theorem fw_eq_bq (v : Fin m → ℝ) : fwV (Kr M) (wV M v (tz M v)) = bq M v := by
  classical
  funext a b
  by_cases hK : Kr M a b
  · rw [bq, if_pos hK, bott]
    exact fwV_congr kr_trans (fun a b hab => wV_eq_wgt v hab) hK
  · rw [fwV_of_not kr_trans _ hK, bq, if_neg hK, wV]
    by_cases he : a = b
    · subst he
      have hl : a ∈ M.closure ∅ := by
        by_contra h
        exact hK (Kr.refl h)
      simp [tz, hl]
    · simp [he, hK]

/-- **The values `ρ`** computed from the merge values. -/
theorem rho_eq (v : Fin m → ℝ) : (fun x => listMin ((lower M x).map (bq M v x))) = rho M v := by
  classical
  funext x
  rw [rho]
  congr 1
  refine List.map_congr_left fun y hy => ?_
  rw [bq, if_pos (mem_lower.1 hy).2]

/-- **The order values** computed from the merge values. -/
theorem u_eq (v : Fin m → ℝ) : uV M v (tz M v) (bq M v) = uq M v := by
  classical
  funext x y
  rw [uV, uq]
  by_cases hK : Kr M x y
  · rw [if_pos hK, if_pos hK, uval, bq, if_pos hK, tz, tz, if_neg hK.2.1, if_neg hK.2.2]
  · rw [if_neg hK, if_neg hK]

end Merge

/-! ### All event values from `v` -/

section Events

variable {M : Matroid (Fin m)} {C : Circuit BoolOp m}

/-- The representation of the event values: the entry times, the merge values, the values `ρ`
and the order values. -/
abbrev evR (m : ℕ) : Rep STOp ℝ n
    ((Fin m → Arg n) × (Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n))
    ((Fin m → ℝ) × (Fin m → Fin m → ℝ) × (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :=
  (realsR m).prod ((matsR m).prod ((realsR m).prod (matsR m)))

/-- **The event values from `v`** (Step 2): the entry times, then the weights and the merge
values, then `ρ`, then the order values. -/
noncomputable def eventsB (M : Matroid (Fin m)) (C : Circuit BoolOp m) :
    (Fin m → Arg n) → Bld STOp n
      ((Fin m → Arg n) × (Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Fin m → Arg n)) :=
  seqB (pairB (pureB fun v => v) fun v => tabB fun x => entryB M C x v)
    (seqB (pairB (pureB fun p => p) (seqB (wB M) (fwB M)))
      (seqB (pairB (pureB fun q => q) fun q => rhoB M q.2)
        (seqB (pairB (pureB fun r => r) fun r => uB M (r.1.1.1, r.1.1.2, r.1.2))
          (pureB fun s => (s.1.1.1.2, s.1.1.2, s.1.2, s.2)))))

/-- The gates of `eventsB`. -/
noncomputable def evCost (M : Matroid (Fin m)) (C : Circuit BoolOp m) : ℕ :=
  ∑ x, entryCost M C x + m * (m - 1) * 5 + m * (m * (m * 4)) +
    ∑ x, 3 * ((lower M x).length - 1) + m * (m * 6)

/-- **The event values**: `eventsB` computes the entry times, the merge values, the values `ρ` and
the order values with `evCost M C` gates. -/
theorem eventsB_impl (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    Impl (realsR m) (evR (n := n) m) (eventsB M C) (evCost M C)
      (fun v => (tz M v, bq M v, rho M v, uq M v)) := by
  have h₁ := (Impl.self (R := realsR (n := n) m)).pair
    (Impl.tabSum (R := realsR m) fun x => entryB_impl (n := n) hE hB x)
  have h₂ := (Impl.self (R := (realsR (n := n) m).prod (realsR m))).pair
    ((wB_impl (M := M)).comp (fwB_impl (M := M)))
  have h₃ := (Impl.self (R := ((realsR (n := n) m).prod (realsR m)).prod (matsR m))).pair
    ((rhoB_impl (M := M)).pre (R := ((realsR m).prod (realsR m)).prod (matsR m))
      (g := fun q => q.2) (G := fun Q => Q.2) fun _ _ _ hs => hs.2)
  have h₄ := (Impl.self (R := (((realsR (n := n) m).prod (realsR m)).prod (matsR m)).prod
    (realsR m))).pair ((uB_impl (M := M)).pre
      (R := (((realsR m).prod (realsR m)).prod (matsR m)).prod (realsR m))
      (g := fun r => (r.1.1.1, r.1.1.2, r.1.2)) (G := fun R => (R.1.1.1, R.1.1.2, R.1.2))
      fun _ _ _ hs => ⟨hs.1.1.1, hs.1.1.2, hs.1.2⟩)
  have h₅ := Impl.free (R₁ := ((((realsR (n := n) m).prod (realsR m)).prod (matsR m)).prod
      (realsR m)).prod (matsR m)) (R₂ := evR m)
    (g := fun s => (s.1.1.1.2, s.1.1.2, s.1.2, s.2))
    (F := fun S => (S.1.1.1.2, S.1.1.2, S.1.2, S.2))
    fun _ _ _ hs => ⟨hs.1.1.1.2, hs.1.1.2, hs.1.2, hs.2⟩
  refine ((h₁.comp (h₂.comp (h₃.comp (h₄.comp h₅)))).cost (by rw [evCost]; ring)).congr
    fun v => ?_
  simp only [fw_eq_bq, rho_eq, u_eq]

end Events

/-! ### The circuit -/

/-- The query values `t_x, T_xy, U_xy` as a family of operands. -/
def qOps (e : (Fin m → Arg n) × (Fin m → Fin m → Arg n) × (Fin m → Arg n) ×
    (Fin m → Fin m → Arg n)) : Fin (qn m) → Arg n :=
  Fin.append e.1 (Fin.append (fun i => e.2.1 (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2) fun i => e.2.2.2 (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm i).2)

/-- The levels `t_x, ρ_x` as a family of operands. -/
def levOps (e : (Fin m → Arg n) × (Fin m → Fin m → Arg n) × (Fin m → Arg n) ×
    (Fin m → Fin m → Arg n)) : Fin (m + m) → Arg n :=
  Fin.append e.1 e.2.2.1

/-- The compiler at given levels as an implementation. -/
theorem levB_impl {q L : ℕ} (B : Circuit BoolOp q) :
    Impl ((realsR q).prod (realsR L)) (Rep.list (stInterp ℝ) B.outs.length)
      (fun p => levB (n := n) B (List.ofFn p.1) (List.ofFn p.2)) (levCost B L)
      (fun t => levVal B t.1 t.2) := by
  intro gs p P hp
  obtain ⟨hpre, hl, hden⟩ := levB_spec (B := B) (denL_ofFn hp.1) (denL_ofFn hp.2)
  exact ⟨hpre, hl, by rw [← hden.length_eq fun _ => 0, length_levVal], hden⟩

/-- The query values and the levels from the event values: no gate. -/
theorem qlev_impl :
    Impl (evR (n := n) m) ((realsR (qn m)).prod (realsR (m + m)))
      (pureB fun e => (qOps e, levOps e)) 0 (fun E => (Fin.append E.1 (Fin.append (fun i => E.2.1 (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2) fun i => E.2.2.2 (finProdFinEquiv.symm i).1
          (finProdFinEquiv.symm i).2), Fin.append E.1 E.2.2.1)) := by
  refine Impl.free fun gs e E he => ⟨fun j => ?_, fun j => ?_⟩
  · refine Fin.addCases (fun x => ?_) (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) j
    · simp only [qOps, Fin.append_left]
      exact he.1 x
    · simp only [qOps, Fin.append_left, Fin.append_right]
      exact he.2.1 _ _
    · simp only [qOps, Fin.append_right]
      exact he.2.2.2 _ _
  · refine Fin.addCases (fun x => ?_) (fun x => ?_) j
    · simp only [levOps, Fin.append_left]
      exact he.1 x
    · simp only [levOps, Fin.append_right]
      exact he.2.2.1 x

/-- Step 5, `p + a`: one gate per block. -/
theorem addB_impl :
    Impl ((realsR k).prod (realsR k)) (realsR (n := n) k)
      (fun s => tabB fun b => emit .add (s.1 b) (s.2 b)) k (fun t => t.1 + t.2) := by
  refine (Impl.tab fun b => ?_).cost (mul_one k)
  intro gs s T hs
  exact ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _, den_emit STOp.add (hs.1 b) (hs.2 b)⟩

/-- The one-update builder: from operands carrying `(w, p)`, operands carrying `p + a`, where `a_b`
is the `b`-th output of the compiler at the levels of `v = w - p_blk`. -/
noncomputable def updB (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (O : Circuit BoolOp (qn m)) :
    (Fin m → Arg n) × (Fin k → Arg n) → Bld STOp n (List (Arg n)) :=
  seqB (pairB (pureB Prod.snd) (seqB (shiftB blk) (seqB (eventsB M C)
      (seqB (pureB fun e => (qOps e, levOps e))
        (seqB (fun p => levB O (List.ofFn p.1) (List.ofFn p.2))
          (pureB fun as b => as.getD b .const))))))
    (seqB (fun s => tabB fun b => emit .add (s.1 b) (s.2 b)) (pureB List.ofFn))

/-- The compiled update at `v`: entry `b` of the compiler at the levels. -/
noncomputable def updV (M : Matroid (Fin m)) (O : Circuit BoolOp (qn m)) (v : Fin m → ℝ)
    (b : Fin k) : ℝ :=
  (levVal O (Qv M v) (lev M v)).getD b 0

/-- `updB` implements `(w, p) ↦ p + a` with `m + evCost M C + levCost O (m + m) + k` gates. -/
theorem updB_impl {M : Matroid (Fin m)} {C : Circuit BoolOp m} (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (O : Circuit BoolOp (qn m)) :
    Impl ((realsR m).prod (realsR k)) (Rep.list (stInterp ℝ) k) (updB (n := n) M C blk O)
      (m + evCost M C + levCost O (m + m) + k)
      (fun t => List.ofFn (t.2 + updV (k := k) M O (shift blk t.1 t.2))) :=
  ((Impl.snd.pair ((shiftB_impl blk).comp ((eventsB_impl hE hB).comp (qlev_impl.comp
    ((levB_impl O).comp (Impl.free (R₂ := realsR k)
      (g := fun (as : List (Arg n)) (b : Fin k) => as.getD b .const)
      (F := fun (A : List ℝ) (b : Fin k) => A.getD b 0) fun _ _ _ hs b => hs.2.getD b)))))).comp
    (addB_impl.comp (ofFn_impl _ k))).cost (by ring) |>.congr fun _ => rfl

/-- The circuit of Lemma `lem:oneupdate`, on the `m + k` inputs `(w, p)`. -/
noncomputable def updCircuit (M : Matroid (Fin m)) (C : Circuit BoolOp m) (blk : Fin m → Fin k)
    (O : Circuit BoolOp (qn m)) : Circuit STOp (m + k) :=
  circuitOf fun x => updB M C blk O (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b))

/-- The size of the one-update circuit, and what it computes at every `(w, p)`. -/
theorem updCircuit_spec {M : Matroid (Fin m)} {C : Circuit BoolOp m} (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) (O : Circuit BoolOp (qn m)) :
    (updCircuit M C blk O).size = m + evCost M C + levCost O (m + m) + k ∧
      ∀ w p, (updCircuit M C blk O).eval (stInterp ℝ) (Fin.append w p) =
        List.ofFn (p + updV M O (shift blk w p)) := by
  have h := circuitOf_spec ((updB_impl hE hB blk O).pre (R := realsR (m + k))
    (g := fun x => (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b)))
    (G := fun x => (fun e => x (Fin.castAdd k e), fun b => x (Fin.natAdd m b)))
    fun _ _ _ hs => ⟨fun e => hs _, fun b => hs _⟩)
  refine ⟨h.1, fun w p => ?_⟩
  rw [updCircuit, h.2.2]
  simp only [Fin.append_left, Fin.append_right]

/-! ### Correctness and size -/

/-- **The compiled update is the PO-SL update.**  For an observer of stage `r < k`, at every `v`
with `ν(M^v) ≥ r`, entry `b` of the compiler at the levels is `a_b`. -/
theorem updV_eq_update {M : Matroid (Fin m)} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (qn m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hO : IsObserver M blk r O)
    {v : Fin m → ℝ} (hr : r ≤ nu (minBases M v) blk) :
    updV M O v = Validity.update (POSL.N M v) blk r := by
  set F : Fin k → (Fin (qn m) → Bool) → Bool := fun b X => (O.eval boolInterp X).getD b false
  have hB : ∀ X, O.eval boolInterp X = List.ofFn fun b => F b X := by
    intro X
    refine List.ext_getElem (by simp [Circuit.eval, hO.length_outs]) fun i h₁ h₂ => ?_
    simp only [List.getElem_ofFn, F]
    rw [List.getD_eq_getElem _ _ h₁]
  have hF : ∀ t, 0 ≤ t → ∀ b, F b (fun j => decide (Qv M v j ≤ t)) =
      decide (nu (POSL.N M v t) blk ≤ r ∧ b ∈ Av (POSL.N M v t) blk) := fun t ht b => by
    simp only [F, hO v t ht, getD_ofFn]
  funext b
  rw [updV, levVal_eq hB lev_nonneg (fun j => (Qv_inLev j).exists_sortedVal), getD_ofFn,
    GapUpdate.update_eq_levSum hE hk hM hr hrk hF b]

/-- The one-update circuit of an observer of stage `r < k` outputs `p + a` at every state with
`ν₀ ≥ r`. -/
theorem updCircuit_eval {M : Matroid (Fin m)} {C : Circuit BoolOp m} {blk : Fin m → Fin k}
    {r : ℕ} {O : Circuit BoolOp (qn m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (hrk : r < k) (hO : IsObserver M blk r O) {w : Fin m → ℝ} {p : Fin k → ℝ}
    (hr : r ≤ nu (minBases M (shift blk w p)) blk) :
    (updCircuit M C blk O).eval (stInterp ℝ) (Fin.append w p) =
      List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r) := by
  rw [(updCircuit_spec hE hB blk O).2, updV_eq_update hE hk hM hrk hO hr]

/-- An entry time costs at most `9m² + 6ms + 15m⌈log₂(m+1)⌉ + 15m` gates. -/
theorem entryCost_le {M : Matroid (Fin m)} {C : Circuit BoolOp m}
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (x : Fin m) :
    entryCost M C x ≤ 9 * m ^ 2 + 6 * m * C.size + 15 * m * Nat.size m + 15 * m := by
  classical
  unfold entryCost
  split_ifs
  · exact Nat.zero_le _
  · have h := compileCost_le (closCircuit C x)
    have hs := (vecCircuit_spec (closB_impl (n := m) hB x)).1
    have ho := (vecCircuit_spec (closB_impl (n := m) hB x)).2.1
    rw [← closCircuit] at hs ho
    rw [hs, ho, closCost] at h
    have e : 3 * m * (m + 2 * C.size + 5 * Nat.size m + 4) + m * 1 + 6 * m ^ 2 =
        9 * m ^ 2 + 6 * m * C.size + 15 * m * Nat.size m + 13 * m := by ring
    omega

/-- **The event values cost** at most `13m³ + 6m²s + 15m²⌈log₂(m+1)⌉ + 29m²` gates. -/
theorem evCost_le {M : Matroid (Fin m)} {C : Circuit BoolOp m}
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m))) :
    evCost M C ≤ 13 * m ^ 3 + 6 * m ^ 2 * C.size + 15 * m ^ 2 * Nat.size m + 29 * m ^ 2 := by
  have h₁ : ∑ x, entryCost M C x ≤
      m * (9 * m ^ 2 + 6 * m * C.size + 15 * m * Nat.size m + 15 * m) := by
    have := sum_le_sum fun x (_ : x ∈ (univ : Finset (Fin m))) => entryCost_le hB x
    simpa using this
  have h₂ : ∑ x, 3 * ((lower M x).length - 1) ≤ m * (3 * m) := by
    have := sum_le_sum fun x (_ : x ∈ (univ : Finset (Fin m))) =>
      show 3 * ((lower M x).length - 1) ≤ 3 * m from Nat.mul_le_mul_left 3
        ((Nat.sub_le _ 1).trans ((List.length_filter_le _ _).trans (by simp)))
    simpa using this
  have h₃ : m * (m - 1) * 5 ≤ 5 * m ^ 2 := by
    have := Nat.mul_le_mul_left m (Nat.sub_le m 1)
    nlinarith
  unfold evCost
  have e : m * (9 * m ^ 2 + 6 * m * C.size + 15 * m * Nat.size m + 15 * m) =
      9 * m ^ 3 + 6 * m ^ 2 * C.size + 15 * m ^ 2 * Nat.size m + 15 * m ^ 2 := by ring
  have e' : m * (m * (m * 4)) = 4 * m ^ 3 := by ring
  have e'' : m * (m * 6) = 6 * m ^ 2 := by ring
  have e''' : m * (3 * m) = 3 * m ^ 2 := by ring
  omega

/-- The gates of the one-update circuit outside the `2m` copies of the lifted observer:
`6 m² s + 29 m³ + 15 m² ⌈log₂(m+1)⌉ + 43 m² + 3 m + 2 m k + k`. -/
def updOver (m k s : ℕ) : ℕ :=
  6 * m ^ 2 * s + 29 * m ^ 3 + 15 * m ^ 2 * Nat.size m + 43 * m ^ 2 + 3 * m + 2 * m * k + k

/-- `updOver m k s ≤ 93 m² (s + m)` for `1 ≤ m` and `k ≤ m`. -/
theorem updOver_le {m k s : ℕ} (hm : 1 ≤ m) (hkm : k ≤ m) :
    updOver m k s ≤ 93 * (m ^ 2 * (s + m)) := by
  have h₁ : Nat.size m ≤ m := size_le_self m
  have h₂ : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right hm (by norm_num)
  have h₃ : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
  have h₄ : m ^ 2 * Nat.size m ≤ m ^ 3 := by
    calc m ^ 2 * Nat.size m ≤ m ^ 2 * m := Nat.mul_le_mul_left _ h₁
      _ = m ^ 3 := by ring
  have h₅ : m * k ≤ m ^ 3 := by
    calc m * k ≤ m * m := Nat.mul_le_mul_left _ hkm
      _ = m ^ 2 := by ring
      _ ≤ m ^ 3 := h₂
  have e : 93 * (m ^ 2 * (s + m)) = 93 * (m ^ 2 * s) + 93 * m ^ 3 := by ring
  unfold updOver
  have e' : 6 * m ^ 2 * s = 6 * (m ^ 2 * s) := by ring
  have e'' : 15 * m ^ 2 * Nat.size m = 15 * (m ^ 2 * Nat.size m) := by ring
  have e''' : 2 * m * k = 2 * (m * k) := by ring
  omega

/-- **The size of the one-update circuit**: at most `6 m s_O + updOver m k s`, for an observer `O`
with `k` outputs. -/
theorem updCircuit_size_le {M : Matroid (Fin m)} {C : Circuit BoolOp m} (hE : M.E = Set.univ)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (blk : Fin m → Fin k) {O : Circuit BoolOp (qn m)} (hO : O.outs.length = k) :
    (updCircuit M C blk O).size ≤ 6 * m * O.size + updOver m k C.size := by
  rw [(updCircuit_spec hE hB blk O).1, updOver]
  have h₁ := evCost_le (M := M) hB
  have h₂ : 2 * levCost O (m + m) ≤ 3 * (m + m) ^ 2 +
      2 * (m + m) * (1 + 4 * (m + (m * m + m * m)) + 3 * O.size + k) := by
    have := levCost_le O (m + m)
    rwa [hO] at this
  have e : 3 * (m + m) ^ 2 + 2 * (m + m) * (1 + 4 * (m + (m * m + m * m)) + 3 * O.size + k) =
      2 * (6 * m * O.size + 16 * m ^ 3 + 14 * m ^ 2 + 2 * m + 2 * m * k) := by ring
  rw [e] at h₂
  linarith

/-- **Lemma `lem:oneupdate`.**  Let `M` have ground set `E`, rank `k` and a rainbow base, let the
Boolean circuit `C` of size `s` output the binary digits of the rank of `M`, let `r < k`, and let
`O` be an observer for stage `r` (Lemma `lem:observer`) of size `s_O`.  A signed tropical circuit
of size at most `6 m s_O + updOver m k s` on the `m + k` inputs `(w, p)` outputs `p + a`, `a` the
PO-SL update at `v = w - p_blk`, at every state of stage `r`, that is with `ν₀ = ν(M^v) ≥ r`. -/
theorem oneUpdate {M : Matroid (Fin m)} {C : Circuit BoolOp m} {blk : Fin m → Fin k} {r : ℕ}
    {O : Circuit BoolOp (qn m)} (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (hrk : r < k) (hO : IsObserver M blk r O) :
    ∃ U : Circuit STOp (m + k), U.size ≤ 6 * m * O.size + updOver m k C.size ∧
        ∀ w p, r ≤ nu (minBases M (shift blk w p)) blk →
          U.eval (stInterp ℝ) (Fin.append w p) =
            List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r) :=
  ⟨updCircuit M C blk O, updCircuit_size_le hE hB blk hO.length_outs,
    fun _ _ hr => updCircuit_eval hE hk hM hB hrk hO hr⟩

end SignedTropical.Rainbow.TheoremC
