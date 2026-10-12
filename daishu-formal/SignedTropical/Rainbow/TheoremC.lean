import SignedTropical.Rainbow.OneUpdate
import SignedTropical.Rainbow.Schedule
import SignedTropical.TheoremA

/-!
# Theorem C: the circuit

`greedy_intersection.tex`, Theorem `thm:C` and its proof, Steps 1 to 4, with the observers of
Lemma `lem:observer` as hypotheses.  `M : Matroid (Fin m)` has ground set `univ`, rank `k` and a
rainbow base; the blocks are the fibres of `blk : Fin m → Fin k`.

The circuit (`theoremCCircuit L blk U CA`), for stage lengths `L : ℕ → ℕ`, on the input `w`:

1. the schedule (`schedB`): start at `p = 0` and, for `r = 1, …, k - 1`, run `L r` rounds of
   stage `r`; a round (`roundB`) runs a circuit `U r` on the `m + k` operands `(w, p)` (`runB`)
   and reads the new `p` from its first `k` outputs;
2. the output (`psiB`): `-v = p_blk - w` (`m` gates), a circuit `CA` at `-v`, the sum of the
   `p_b` (`k` gates, `sumB`) and one subtraction, `Σ_b p_b - CA(-v)`.

Its size is `Σ_{r<k} L r · |U r| + m + |CA| + k + 1`, exactly (`schedCost`,
`theoremCCircuit_spec`).

Correctness (`theoremC_of_validLength`).  For valid stage lengths (`Schedule.ValidLength`: at
every weight, stage `r` ends within `L r` updates) and with `U r` the one-update circuit of an
observer of stage `r` (`updCircuit`, Lemma `lem:oneupdate`), a round is the stage map at every
state of stage `r` (`roundV_updCircuit`), so the rounds follow `Schedule.schedule L`
(`schedV_eq`, using that `ν₀` does not decrease, `Potential.nu_le_nu_stageMap`, and the
invariant `Schedule.le_nu_schedule`).  With `CA` the circuit of Theorem A, the output is
`Σ_b p_b - h_M(-v) = Σ_b p_b + β_M(v) = Ψ(p)` (`psiV_eq`), and `Ψ(p) = Opt(w)` after the schedule
(`Schedule.psi_schedule`).  Two instances: `theoremC`, with `L = stageLength k m` and
`R = Schedule.rounds k m` rounds, at most `(⌊m²/4⌋ + 1) · k(k-1)/2`
(`Schedule.rounds_le_potential`) and at most `k³ m` (`Schedule.rounds_le`); and
`theoremC_rankOne`, with `L r = r` and `k(k-1)/2` rounds when every component of `M` has rank at
most one (Corollary `cor:rankone`).

The size: the theorems state `R · (3 m² s_O + k m² + 6 m⁴ + 2 m² + m + k)` plus the output part
`3 m s + m L' + 9 m² + 5 m + 4 L' + k + 2`, `L' = ⌈log₂(k+1)⌉`, for observers of size at most
`s_O`; `size_le_of_observer_le` turns `s_O ≤ c k m³ (s + m)` (the order of Lemma `lem:observer`)
and `R ≤ k^a m^b` into `(3 c + 36) k^(a+1) m^(b+5) (s + m) + 2`: `theoremC_bigO` obtains
`(3 c + 36) k⁴ m⁶ (s + m) + 2`, the paper's `O(k⁴ m⁶ (s + m))`, and `theoremC_bigO_rankOne`
obtains `(3 c + 36) k³ m⁵ (s + m) + 2`.  Uniformity is not formalized.
-/

open Finset

namespace SignedTropical.Rainbow.TheoremC

open SignedTropical.Rainbow SignedTropical.BoolAlg

variable {m k n : ℕ}

/-! ### One round -/

/-- One round: run the circuit `U` on the operands `(w, p)` and read the new `p` from its first
`k` outputs. -/
def roundB (U : Circuit STOp (m + k)) (s : (Fin m → Arg n) × (Fin k → Arg n)) :
    Bld STOp n (Fin k → Arg n) := fun gs =>
  ((runB U (Fin.append s.1 s.2) gs).1, fun b => (runB U (Fin.append s.1 s.2) gs).2.getD b .const)

/-- What a round computes: the first `k` outputs of `U` at `(w, p)`. -/
noncomputable def roundV (U : Circuit STOp (m + k)) (w : Fin m → ℝ) (p : Fin k → ℝ) :
    Fin k → ℝ :=
  fun b => (U.eval (stInterp ℝ) (Fin.append w p)).getD b 0

/-- A round implements `roundV U` with `|U|` gates. -/
theorem roundB_impl (U : Circuit STOp (m + k)) :
    Impl ((realsR m).prod (realsR k)) (realsR (n := n) k) (roundB U) U.size
      (fun t => roundV U t.1 t.2) := by
  intro gs s T hs
  have hin : (realsR (m + k)).rep gs (Fin.append s.1 s.2) fun x => Fin.append (T x).1 (T x).2 := by
    intro i
    refine Fin.addCases (fun e => ?_) (fun b => ?_) i
    · simpa only [Fin.append_left] using hs.1 e
    · simpa only [Fin.append_right] using hs.2 b
  obtain ⟨hp, hl, -, hden⟩ := runB_impl (stInterp ℝ) U hin
  exact ⟨hp, hl, fun b => hden.getD b⟩

/-! ### The schedule -/

/-- Stages `1, …, j` of the schedule: stage `r` runs `L r` rounds with the circuit `U r`. -/
def schedB (L : ℕ → ℕ) (U : ℕ → Circuit STOp (m + k)) :
    ℕ → (Fin m → Arg n) × (Fin k → Arg n) → Bld STOp n (Fin k → Arg n)
  | 0 => pureB Prod.snd
  | j + 1 => fun s gs =>
    let q := schedB L U j s gs
    iterCtxB (roundB (U (j + 1))) (L (j + 1)) (s.1, q.2) q.1

/-- The state after stages `1, …, j` of rounds. -/
noncomputable def schedV (L : ℕ → ℕ) (U : ℕ → Circuit STOp (m + k)) (w : Fin m → ℝ) :
    ℕ → (Fin k → ℝ) → Fin k → ℝ
  | 0, p => p
  | j + 1, p => (roundV (U (j + 1)) w)^[L (j + 1)] (schedV L U w j p)

/-- The gates of stages `1, …, j`: `Σ_{r=1}^{j} L r · |U r|`. -/
def schedCost (L : ℕ → ℕ) (U : ℕ → Circuit STOp (m + k)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => schedCost L U j + L (j + 1) * (U (j + 1)).size

/-- `schedB L U j` implements the state after stages `1, …, j` with `schedCost L U j`
gates. -/
theorem schedB_impl (L : ℕ → ℕ) (U : ℕ → Circuit STOp (m + k)) :
    ∀ j, Impl ((realsR m).prod (realsR k)) (realsR (n := n) k) (schedB L U j) (schedCost L U j)
      (fun t => schedV L U t.1 j t.2)
  | 0 => Impl.snd
  | j + 1 => by
    intro gs s T hs
    obtain ⟨hp₁, hl₁, hr₁⟩ := schedB_impl L U j hs
    have h₁ : ((realsR m).prod (realsR k)).rep (schedB L U j s gs).1 (s.1, (schedB L U j s gs).2)
        (fun x => ((T x).1, schedV L U (T x).1 j (T x).2)) := ⟨(realsR m).mono hp₁ hs.1, hr₁⟩
    obtain ⟨hp₂, hl₂, hr₂⟩ :=
      Impl.iterateCtx (roundB_impl (U (j + 1))) (L (j + 1)) h₁
    refine ⟨hp₁.trans hp₂, ?_, hr₂⟩
    simp only [schedB, schedCost] at hl₂ ⊢
    rw [hl₂, hl₁]
    ring

/-! ### The output -/

/-- `a₀ + (a₁ + (⋯ + (a_{L-1} + 0)))`, one gate per entry. -/
def sumB : List (Arg n) → Bld STOp n (Arg n)
  | [] => fun gs => (gs, .const)
  | a :: l => fun gs =>
    let q := sumB l gs
    emit .add a q.2 q.1

/-- `sumB` computes the sum of a list with one gate per entry. -/
theorem sumB_spec :
    ∀ {l : List (Arg n)} {F : (Fin n → ℝ) → List ℝ} {gs : List (Gate STOp n)},
      DenL (stInterp ℝ) gs l F →
      gs <+: (sumB l gs).1 ∧ (sumB l gs).1.length = gs.length + l.length ∧
        Den (stInterp ℝ) (sumB l gs).1 (sumB l gs).2 (fun x => (F x).sum)
  | [], F, gs, h => ⟨List.prefix_refl _, by simp [sumB], (den_const gs).congr fun x => by
      rw [show F x = [] by rw [← h.2 x]; rfl]; rfl⟩
  | a :: l, F, gs, h => by
    obtain ⟨ha, hl, hF⟩ := h.uncons
    obtain ⟨hp, hlen, hv⟩ := sumB_spec hl
    have hr := den_emit STOp.add (ha.mono hp) hv
    refine ⟨hp.trans (isPrefix_emit _ _ _ _), by simp [sumB, length_emit, hlen]; ring,
      hr.congr fun x => ?_⟩
    conv_rhs => rw [hF x]
    rfl

/-- The output `Ψ(p) = Σ_b p_b - h_M(-v)`: `-v = p_blk - w` (`m` gates), the circuit `CA` at
`-v`, the sum of the `p_b` (`k` gates) and one subtraction. -/
def psiB (blk : Fin m → Fin k) (CA : Circuit STOp m) (s : (Fin m → Arg n) × (Fin k → Arg n)) :
    Bld STOp n (Arg n) := fun gs =>
  let q₁ := tabB (fun e => emit .sub (s.2 (blk e)) (s.1 e)) gs
  let q₂ := runB CA q₁.2 q₁.1
  let q₃ := sumB (List.ofFn s.2) q₂.1
  emit .sub q₃.2 (q₂.2.getD 0 .const) q₃.1

/-- What the output part computes: `Σ_b p_b - CA(p_blk - w)`. -/
noncomputable def psiV (blk : Fin m → Fin k) (CA : Circuit STOp m) (w : Fin m → ℝ)
    (p : Fin k → ℝ) : ℝ :=
  ∑ b, p b - (CA.eval (stInterp ℝ) fun e => p (blk e) - w e).getD 0 0

/-- The output part implements `psiV blk CA` with `m + |CA| + k + 1` gates. -/
theorem psiB_impl (blk : Fin m → Fin k) (CA : Circuit STOp m) :
    Impl ((realsR m).prod (realsR k)) (Rep.arg (stInterp ℝ)) (psiB (n := n) blk CA)
      (m + CA.size + k + 1) (fun t => psiV blk CA t.1 t.2) := by
  intro gs s T hs
  obtain ⟨hp₁, hl₁, hr₁⟩ := tabB_spec (R₂ := Rep.arg (stInterp ℝ)) (c := 1)
    (b := fun e => emit .sub (s.2 (blk e)) (s.1 e)) (F := fun e x => (T x).2 (blk e) - (T x).1 e)
    (gs₀ := gs) fun e gs' h => ⟨isPrefix_emit _ _ _ _, length_emit _ _ _ _,
      den_emit STOp.sub ((hs.2 (blk e)).mono h) ((hs.1 e).mono h)⟩
  obtain ⟨hp₂, hl₂, -, hr₂⟩ := runB_impl (stInterp ℝ) CA hr₁
  obtain ⟨hp₃, hl₃, hr₃⟩ := sumB_spec (denL_ofFn ((realsR k).mono (hp₁.trans hp₂) hs.2))
  have h₄ := den_emit STOp.sub hr₃ ((hr₂.getD 0).mono hp₃)
  refine ⟨((hp₁.trans hp₂).trans hp₃).trans (isPrefix_emit _ _ _ _), ?_, h₄.congr fun x => ?_⟩
  · simp only [psiB, length_emit, hl₃, hl₂, hl₁, List.length_ofFn]
    ring
  · simp [psiV, stInterp, List.sum_ofFn]

/-! ### The circuit of Theorem C -/

/-- The circuit of Theorem `thm:C` as a builder on the operands `w`: the schedule from `p = 0`
with stage lengths `L`, then the output `Ψ(p)`. -/
def thmCB (L : ℕ → ℕ) (blk : Fin m → Fin k) (U : ℕ → Circuit STOp (m + k))
    (CA : Circuit STOp m) (w : Fin m → Arg n) : Bld STOp n (List (Arg n)) := fun gs =>
  let q := schedB L U (k - 1) (w, fun _ => .const) gs
  let o := psiB blk CA (w, q.2) q.1
  (o.1, [o.2])

/-- The circuit of Theorem `thm:C`, assembled from stage lengths `L`, the round circuits `U r`
(`r = 1, …, k - 1`) and a circuit `CA` read as `h_M`. -/
def theoremCCircuit (L : ℕ → ℕ) (blk : Fin m → Fin k) (U : ℕ → Circuit STOp (m + k))
    (CA : Circuit STOp m) : Circuit STOp m :=
  circuitOf (thmCB L blk U CA)

/-- The size of the circuit of Theorem C, and what it computes at every `w`. -/
theorem theoremCCircuit_spec (L : ℕ → ℕ) (blk : Fin m → Fin k) (U : ℕ → Circuit STOp (m + k))
    (CA : Circuit STOp m) :
    (theoremCCircuit L blk U CA).size = schedCost L U (k - 1) + (m + CA.size + k + 1) ∧
      ∀ w, (theoremCCircuit L blk U CA).eval (stInterp ℝ) w =
        [psiV blk CA w (schedV L U w (k - 1) 0)] := by
  have h : Impl (realsR m) (Rep.list (stInterp ℝ) 1) (thmCB (n := m) L blk U CA)
      (schedCost L U (k - 1) + (m + CA.size + k + 1))
      (fun w => [psiV blk CA w (schedV L U w (k - 1) 0)]) := by
    intro gs w W hw
    have h₀ : ((realsR m).prod (realsR k)).rep gs (w, fun _ => .const) (fun x => (W x, 0)) :=
      ⟨hw, fun _ => den_const gs⟩
    obtain ⟨hp₁, hl₁, hr₁⟩ := schedB_impl L U (k - 1) h₀
    have h₁ : ((realsR m).prod (realsR k)).rep (schedB L U (k - 1) (w, fun _ => .const) gs).1
        (w, (schedB L U (k - 1) (w, fun _ => .const) gs).2)
        (fun x => (W x, schedV L U (W x) (k - 1) 0)) := ⟨(realsR m).mono hp₁ hw, hr₁⟩
    obtain ⟨hp₂, hl₂, hr₂⟩ := psiB_impl blk CA h₁
    exact ⟨hp₁.trans hp₂, by simp only [thmCB]; rw [hl₂, hl₁]; ring, rfl,
      DenL.cons hr₂ (denL_nil _)⟩
  exact ⟨(circuitOf_spec h).1, (circuitOf_spec h).2.2⟩

/-! ### Correctness -/

section Correct

variable {M : Matroid (Fin m)} {blk : Fin m → Fin k}

/-- Iterates of two maps that agree on a set invariant under the second agree on it. -/
theorem iterate_eq_iterate {α : Type*} {f g : α → α} {P : α → Prop} (hP : ∀ x, P x → P (g x))
    (h : ∀ x, P x → f x = g x) : ∀ j x, P x → f^[j] x = g^[j] x
  | 0, _, _ => rfl
  | j + 1, x, hx => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h x hx]
    exact iterate_eq_iterate hP h j _ (hP x hx)

/-- A round with the one-update circuit of an observer of stage `r < k` is the stage map at
every state of stage `r`. -/
theorem roundV_updCircuit (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) {r : ℕ} (hrk : r < k) {O : Circuit BoolOp (m * m)}
    (hO : IsObserver M blk r O) {w : Fin m → ℝ} {p : Fin k → ℝ}
    (hr : r ≤ nu (minBases M (shift blk w p)) blk) :
    roundV (updCircuit blk O) w p = Potential.stageMap M blk w r p := by
  funext b
  rw [roundV, updCircuit_eval hE hk hM hrk hO hr, getD_ofFn]
  rfl

/-- **The rounds follow the schedule.**  If the stage lengths `L` are valid and for every stage
`r ∈ {1, …, k - 1}` a round with `U r` is the stage map at every state of stage `r` (`ν₀ ≥ r`),
then after stages `1, …, j`, `j ≤ k - 1`, the state is `Schedule.schedule L M blk w j 0`. -/
theorem schedV_eq (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    {L : ℕ → ℕ} (hL : Schedule.ValidLength M blk L) (w : Fin m → ℝ)
    {U : ℕ → Circuit STOp (m + k)}
    (hU : ∀ r, 1 ≤ r → r < k → ∀ p, r ≤ nu (minBases M (shift blk w p)) blk →
      roundV (U r) w p = Potential.stageMap M blk w r p) :
    ∀ j, j ≤ k - 1 → schedV L U w j 0 = Schedule.schedule L M blk w j 0
  | 0, _ => rfl
  | j + 1, hj => by
    have hq := Schedule.le_nu_schedule hL w 0 (Schedule.one_le_nu hE hk (by omega) _) j
      (by omega)
    simp only [schedV, Schedule.schedule]
    rw [schedV_eq hE hk hM hL w hU j (by omega)]
    exact iterate_eq_iterate (P := fun q => j + 1 ≤ nu (minBases M (shift blk w q)) blk)
      (fun q hq => hq.trans (Potential.nu_le_nu_stageMap hE hM hq))
      (fun q hq => hU (j + 1) (by omega) (by omega) q hq) _ _ hq

/-- With a circuit `CA` for `h_M`, the output part computes the Lagrangian:
`Σ_b p_b - h_M(-v) = Σ_b p_b + β_M(v) = Ψ(p)`. -/
theorem psiV_eq {CA : Circuit STOp m}
    (hCA : ∀ u, CA.eval (stInterp ℝ) u = [maxBasisWeight M u]) (w : Fin m → ℝ)
    (p : Fin k → ℝ) : psiV blk CA w p = Psi M blk w p := by
  have h : -shift blk w p = fun e => p (blk e) - w e := funext fun e => by simp [shift]
  rw [psiV, hCA, Psi, minBaseWeight_eq_neg_maxBasisWeight, h]
  simp [sub_eq_add_neg]

/-- The gates of stages `1, …, j`, `j ≤ k - 1`, when every round circuit `U r`,
`r ∈ {1, …, k - 1}`, has at most `S` gates. -/
theorem schedCost_le {L : ℕ → ℕ} {U : ℕ → Circuit STOp (m + k)} {S : ℕ}
    (hU : ∀ r, 1 ≤ r → r < k → (U r).size ≤ S) :
    ∀ j, j ≤ k - 1 → schedCost L U j ≤ (∑ r ∈ range (j + 1), L r) * S
  | 0, _ => Nat.zero_le _
  | j + 1, hj => by
    have ih := schedCost_le (L := L) hU j (by omega)
    rw [schedCost, sum_range_succ, add_mul]
    exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (hU (j + 1) (by omega) (by omega)))

/-- For stage lengths with `L 0 = 0`, the rounds of stages `1, …, k - 1` number
`Σ_{r<k} L r`. -/
theorem sum_range_sub_one (L : ℕ → ℕ) (hL0 : L 0 = 0) (k : ℕ) :
    ∑ r ∈ range (k - 1 + 1), L r = ∑ r ∈ range k, L r := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hL0]
  · rw [Nat.sub_add_cancel hk]

/-- **Theorem `thm:C`, for valid stage lengths**, with the observers of Lemma `lem:observer` as
hypotheses.  Let `M` be a matroid on `E = Fin m` with rank `k` and a rainbow base, its elements
partitioned into the `k` blocks `blk`, and `L` valid stage lengths with `L 0 = 0`.  If a Boolean
circuit `B` of size `s` outputs the binary digits of the rank `r(S)` from the indicator vector of
`S`, and for every stage `r ∈ {1, …, k - 1}` an observer `O r` of stage `r` with at most `s_O`
gates is given, then a signed tropical circuit of size at most
`(Σ_{r<k} L r) · (3 m² s_O + k m² + 6 m⁴ + 2 m² + m + k) + 3 m s + m L' + 9 m² + 5 m + 4 L' + k + 2`,
`L' = ⌈log₂(k+1)⌉`, computes `Opt(w)` at every `w ∈ ℝ^E`. -/
theorem theoremC_of_validLength (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) {L : ℕ → ℕ} (hL : Schedule.ValidLength M blk L)
    (hL0 : L 0 = 0) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (O : ℕ → Circuit BoolOp (m * m)) (sO : ℕ)
    (hO : ∀ r, 1 ≤ r → r < k → IsObserver M blk r (O r) ∧ (O r).size ≤ sO) :
    ∃ C : Circuit STOp m,
      C.size ≤ (∑ r ∈ range k, L r) *
          (3 * m ^ 2 * sO + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) +
        (3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] := by
  obtain ⟨hsize, heval⟩ :=
    theoremCCircuit_spec L blk (fun r => updCircuit blk (O r)) (theoremACircuit B (rank M))
  refine ⟨theoremCCircuit L blk (fun r => updCircuit blk (O r)) (theoremACircuit B (rank M)), ?_,
    fun w => ?_⟩
  · have hCA := (theoremACircuit_spec B (rank M)).1
    rw [show Nat.size (rank M) = Nat.size k by rw [hk]] at hCA
    have hU : ∀ r, 1 ≤ r → r < k → (updCircuit blk (O r)).size ≤
        3 * m ^ 2 * sO + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k := fun r h1 h2 =>
      (updCircuit_size_le blk (hO r h1 h2).1.length_outs).trans (by
        have := Nat.mul_le_mul_left (3 * m ^ 2) (hO r h1 h2).2
        omega)
    have hS := schedCost_le (L := L) hU (k - 1) le_rfl
    rw [sum_range_sub_one L hL0] at hS
    rw [hsize]
    omega
  · rw [heval, psiV_eq (theoremACircuit_correct M hE B hB),
      schedV_eq hE hk hM hL w (fun r h1 h2 p hp => roundV_updCircuit hE hk hM h2 (hO r h1 h2).1 hp)
        (k - 1) le_rfl, Schedule.psi_schedule hE hk hL w]

/-- **Theorem `thm:C`**, with the observers of Lemma `lem:observer` as hypotheses: the case
`L = stageLength k m` of `theoremC_of_validLength`, with `R = Σ_{r<k} stageLength k m r`
rounds (`Schedule.rounds`), at most `(⌊m²/4⌋ + 1) k(k-1)/2` and at most `k³ m`. -/
theorem theoremC (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (O : ℕ → Circuit BoolOp (m * m)) (sO : ℕ)
    (hO : ∀ r, 1 ≤ r → r < k → IsObserver M blk r (O r) ∧ (O r).size ≤ sO) :
    ∃ C : Circuit STOp m,
      C.size ≤ Schedule.rounds k m *
          (3 * m ^ 2 * sO + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) +
        (3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  theoremC_of_validLength hE hk hM (Schedule.validLength_stageLength hE hk hM)
    (by simp [Schedule.stageLength]) B hB O sO hO

/-- **Theorem `thm:C` for components of rank one** (Corollary `cor:rankone`): when every circuit of
`M` has at most two elements, the stage lengths `L r = r` are valid, and the circuit has
`Σ_{r<k} r = k(k-1)/2` rounds. -/
theorem theoremC_rankOne (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B)
    (hpar : ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (O : ℕ → Circuit BoolOp (m * m)) (sO : ℕ)
    (hO : ∀ r, 1 ≤ r → r < k → IsObserver M blk r (O r) ∧ (O r).size ≤ sO) :
    ∃ C : Circuit STOp m,
      C.size ≤ (∑ r ∈ range k, r) *
          (3 * m ^ 2 * sO + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) +
        (3 * m * B.size + m * Nat.size k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] :=
  theoremC_of_validLength hE hk hM (Schedule.validLength_rankOne hE hk hM hpar) rfl B hB O sO hO

end Correct

/-! ### The order of the size -/

/-- The bound of `theoremC_of_validLength` with `R ≤ k^a m^b` rounds and observers of size at
most `c k m³ (s + m)` is at most `(3 c + 36) k^(a+1) m^(b+5) (s + m) + 2`, when `k ≤ m`, `m > 0`
forces `k > 0`, and `L ≤ k`. -/
theorem size_le_of_observer_le {m k s c L R a b : ℕ} (hkm : k ≤ m) (hmk : 0 < m → 0 < k)
    (hL : L ≤ k) (hR : R ≤ k ^ a * m ^ b) :
    R * (3 * m ^ 2 * (c * (k * m ^ 3 * (s + m))) + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) +
      (3 * m * s + m * L + 9 * m ^ 2 + 5 * m + 4 * L + k + 2) ≤
    (3 * c + 36) * (k ^ (a + 1) * m ^ (b + 5) * (s + m)) + 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : m = 0 := by by_contra h; exact absurd (hmk (Nat.pos_of_ne_zero h)) (by omega)
    obtain rfl : L = 0 := by omega
    simp
  have hm : 1 ≤ m := hk.trans_le hkm
  have ha : 1 ≤ s + m := by omega
  -- one round has at most `(3 c + 11) k m⁵ (s + m)` gates
  have hS := updSize_le (s := s) (c := c) hk hm
  -- the output part has at most `25 k^(a+1) m^(b+5) (s + m)` gates
  have hT : 3 * m * s + m * L + 9 * m ^ 2 + 5 * m + 4 * L + k + 2 ≤
      25 * (k ^ (a + 1) * m ^ (b + 5) * (s + m)) := by
    have e1 := pow_mul_pow_le (i := 0) (j := 1) (i' := a + 1) (j' := b + 5) hk hm ha (by omega)
      (by omega)
    have e2 := pow_mul_pow_le (i := 1) (j := 1) (i' := a + 1) (j' := b + 5) hk hm ha (by omega)
      (by omega)
    have e3 := pow_mul_pow_le (i := 0) (j := 2) (i' := a + 1) (j' := b + 5) hk hm ha (by omega)
      (by omega)
    have e4 := pow_mul_pow_le (i := 1) (j := 0) (i' := a + 1) (j' := b + 5) hk hm ha (by omega)
      (by omega)
    have e5 := pow_mul_pow_le (i := 0) (j := 0) (i' := a + 1) (j' := b + 5) hk hm ha (by omega)
      (by omega)
    have e6 : m * s ≤ k ^ (a + 1) * m ^ (b + 5) * (s + m) := by
      have h := Nat.mul_le_mul (pow_mul_pow_le (a := 1) (i := 0) (j := 1) (i' := a + 1)
        (j' := b + 5) hk hm le_rfl (by omega) (by omega)) (Nat.le_add_right s m)
      simpa using h
    simp only [pow_zero, pow_one, one_mul, mul_one] at e1 e2 e3 e4 e5
    have e7 : m * L ≤ k * m := by rw [mul_comm k]; exact Nat.mul_le_mul_left m hL
    nlinarith
  calc _ ≤ k ^ a * m ^ b * ((3 * c + 11) * (k * m ^ 5 * (s + m))) +
        25 * (k ^ (a + 1) * m ^ (b + 5) * (s + m)) := Nat.add_le_add (Nat.mul_le_mul hR hS) hT
    _ = (3 * c + 36) * (k ^ (a + 1) * m ^ (b + 5) * (s + m)) := by ring
    _ ≤ _ := Nat.le_add_right _ 2

/-- **Theorem `thm:C`, the order of the size.**  Under the hypotheses of `theoremC`, with
observers of size at most `c k m³ (s + m)` (the order `O(k m³ (s + m))` of Lemma
`lem:observer`), a signed tropical circuit of size at most `(3 c + 36) k⁴ m⁶ (s + m) + 2`
computes `Opt(w)` at every `w ∈ ℝ^E`: the paper's `O(k⁴ m⁶ (s + m))`.  The number of rounds is
at most `k³ m` (`Schedule.rounds_le`, by Theorem `thm:stagelength`). -/
theorem theoremC_bigO {M : Matroid (Fin m)} {blk : Fin m → Fin k} (hE : M.E = Set.univ)
    (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (O : ℕ → Circuit BoolOp (m * m)) (c : ℕ)
    (hO : ∀ r, 1 ≤ r → r < k →
      IsObserver M blk r (O r) ∧ (O r).size ≤ c * (k * m ^ 3 * (B.size + m))) :
    ∃ C : Circuit STOp m, C.size ≤ (3 * c + 36) * (k ^ 4 * m ^ 6 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] := by
  obtain ⟨C, hC, hCe⟩ := theoremC hE hk hM B hB O _ hO
  have hkm : k ≤ m := hk ▸ rank_le_card M
  exact ⟨C, hC.trans (size_le_of_observer_le (a := 3) (b := 1) hkm (fun hm => (blk ⟨0, hm⟩).pos)
    (Nat.size_le.2 Nat.lt_two_pow_self) (by simpa using Schedule.rounds_le hkm)), hCe⟩

/-- **Theorem `thm:C` for components of rank one, the order of the size** (Corollary
`cor:rankone`): when every circuit of `M` has at most two elements, with observers of size at
most `c k m³ (s + m)`, a signed tropical circuit of size at most `(3 c + 36) k³ m⁵ (s + m) + 2`
computes `Opt(w)`. -/
theorem theoremC_bigO_rankOne {M : Matroid (Fin m)} {blk : Fin m → Fin k} (hE : M.E = Set.univ)
    (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hpar : ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2) (B : Circuit BoolOp m)
    (hB : ∀ S : Finset (Fin m),
      (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) = M.eRk (S : Set (Fin m)))
    (O : ℕ → Circuit BoolOp (m * m)) (c : ℕ)
    (hO : ∀ r, 1 ≤ r → r < k →
      IsObserver M blk r (O r) ∧ (O r).size ≤ c * (k * m ^ 3 * (B.size + m))) :
    ∃ C : Circuit STOp m, C.size ≤ (3 * c + 36) * (k ^ 3 * m ^ 5 * (B.size + m)) + 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [Opt M blk w] := by
  obtain ⟨C, hC, hCe⟩ := theoremC_rankOne hE hk hM hpar B hB O _ hO
  have hkm : k ≤ m := hk ▸ rank_le_card M
  exact ⟨C, hC.trans (size_le_of_observer_le (a := 2) (b := 0) hkm (fun hm => (blk ⟨0, hm⟩).pos)
    (Nat.size_le.2 Nat.lt_two_pow_self) (by simpa using Schedule.sum_range_id_le k)), hCe⟩

end SignedTropical.Rainbow.TheoremC
