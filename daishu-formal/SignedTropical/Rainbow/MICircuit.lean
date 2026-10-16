import SignedTropical.BoolAlg.ExchangeBits
import SignedTropical.BoolAlg.Count

/-!
# The matroid intersection circuit

`greedy_intersection.tex`, Lemma `lem:augment` (used in Lemma `lem:observer`, Step 3, and in
Corollary `cor:transversal`): `j` rounds of the augmenting path algorithm (Lawler; Schrijver,
Theorem 41.2) on a matroid `N` on `Fin m` and the blocks of `blk : Fin m → Fin k`, then one more
exchange graph, its reachable set, the avoidable blocks `Av(N)` (Lemma `lem:avoidable`) and the
guard `[|I| ≤ r₀]`, as a Boolean circuit with an exact gate count.

The matroid may depend on the input of the circuit (in `lem:observer` it is `N_G`, determined
by the input relation `G`).  The construction is parametrized by a *context*, carried by a
representation `Rc` (the input bits, or data computed from them once), and by *exchange tests*:
for each `y`, a gadget `hO y : Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y)` that reads the
context and the bits of a set `A` and outputs a bit `Fo y (a, A)` with `cO` gates.  The circuit
uses the test of `y` only on sets `A ∋ y` whose part `A - y` is independent: `I - v + y` for the
arcs `y → v` and `I + y` for the sinks, with `I` independent; on the other sets the answer is
masked.  Nothing is assumed about `Fo` to build and count the circuit; its outputs are correct at
every context `a` at which the tests answer these questions in a matroid `N` (`ExchOracle Fo N a`:
`Fo y (a, 1_A) = [A independent in N]` whenever `y ∈ A` and `A - y` is independent in `N`).  An
independence oracle answers all of them (`ExchOracle.of_indep`).

* Values (`exchV`, `addV`, `arcV`, `srcV`, `sinkV`, `roundV`, `stateV`, `reachV`, `avV`, `miV`):
  what the circuit computes, as functions of the context.
* Correctness (`arcV_iff`, `srcV_iff`, `sinkV_iff`, `roundV_indicator`, `stateV_eq`,
  `reachV_iff`, `avV_eq`, `miV_spec`): where the tests answer the exchange questions of `N`, the
  bits at an independent `I` are the exchange graph of `Rainbow/Exchange.lean`, a round is
  `augStep`, `j` rounds from `∅` give `augStep^j(∅)`, a rainbow independent set with at least
  `min(j, ν(N))` elements (`iterate_augStep`), and for `j > r₀` the guard is `[ν(N) ≤ r₀]` and,
  when `ν(N) ≤ r₀`, the avoidable-block bits are `[b ∈ Av(N)]` (`av_eq`).
* Gadgets with exact gate counts (`Impl` of `BoolAlg/Impl.lean`): one round (`roundB_impl`,
  `m(m-1)` arc tests and `m` sink tests, one exchange test each, then the least-index shortest
  path and the exchange, `roundCost m cO = m²cO + 8m³ + 12m² + 12m + 4` gates), `j` rounds
  (`roundsB_impl`), the reachable set of one more exchange graph (`reachB_impl`), the avoidable
  blocks (`avB_impl`), the population count and the guard (`nuGuardB_impl`), and everything
  (`miB_impl`, `miCost m k j cO r₀` gates; with the `k` gates of the observer's bits at most
  `(j+1)(m+1)²(cO + 10(m+1)) + 3k(m+1) + 5⌈log₂(r₀+1)⌉` by `miCost_add_le`).
* For the observer, the bits `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]` from `j = r₀ + 1` rounds
  (`avGuardB_impl`, `avGuardV_eq`, `avGuardCircuit_spec`); for rank circuits obtained by matroid
  intersection, `ν(N)` alone from `k` rounds (`nuB_impl`, `card_stateV`, `nuCircuit_spec`).
-/

namespace SignedTropical.Rainbow.MI

open Finset SignedTropical.BoolAlg SignedTropical.Rainbow.Exchange

/-! ### The values computed by the circuit -/

section Values

variable {m k : ℕ} {τ : Type}

/-- The bits of `I - v + u`: `u` set, `v` cleared, the other entries of `I`. -/
def exchV (I : Fin m → Bool) (u v : Fin m) : Fin m → Bool :=
  fun i => if i = u then true else if i = v then false else I i

/-- The bits of `I + y`. -/
def addV (I : Fin m → Bool) (y : Fin m) : Fin m → Bool :=
  fun i => if i = y then true else I i

/-- The arc bits of the exchange graph of `I`, exchanges being answered by the tests `Fo` at the
context `a`: no arc `u → u`, and for `u ≠ v` an arc `u → v` iff `u ∉ I`, `v ∈ I` and
`Fo u (a, I - v + u)`, or `u ∈ I`, `v ∉ I` and `blk v = blk u`. -/
def arcV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ)
    (I : Fin m → Bool) (u v : Fin m) : Bool :=
  if u = v then false
  else (!I u && (I v && Fo u (a, exchV I u v))) || ((if blk v = blk u then I u else false) && !I v)

/-- The source bits: no element of `I` lies in the block of `y`. -/
def srcV (blk : Fin m → Fin k) (I : Fin m → Bool) (y : Fin m) : Bool :=
  !decide (∃ x, blk x = blk y ∧ I x = true)

/-- The sink bits: `y ∉ I` and `Fo y (a, I + y)`. -/
def sinkV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (a : τ) (I : Fin m → Bool) (y : Fin m) :
    Bool :=
  !I y && Fo y (a, addV I y)

/-- One round of the augmenting path algorithm at the context `a`: `I` exclusive-or the
least-index shortest path from the sources to the sinks (`pathV` of `BoolAlg/Path.lean`). -/
def roundV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ)
    (I : Fin m → Bool) : Fin m → Bool :=
  fun u => I u ^^ pathV (arcV Fo blk a I) (srcV blk I) (sinkV Fo a I) u

/-- The state after `j` rounds from `∅`. -/
def stateV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (j : ℕ) (a : τ) :
    Fin m → Bool :=
  (roundV Fo blk a)^[j] fun _ => false

/-- The elements reachable from a source in the exchange graph of `I`: layer `m` of the
breadth-first search. -/
def reachV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ)
    (I : Fin m → Bool) : Fin m → Bool :=
  layerV (arcV Fo blk a I) (srcV blk I) m

/-- The avoidable-block bits from `I` and a set `R`: block `b` is missed by `I`, or contains an
element of `I ∩ R`. -/
def avV (blk : Fin m → Fin k) (I R : Fin m → Bool) (b : Fin k) : Bool :=
  !decide (∃ x, blk x = b ∧ I x = true) || decide (∃ x, blk x = b ∧ I x = true ∧ R x = true)

/-- The outputs at the context `a`: the state `I` after `j` rounds, its size, the guard
`[|I| ≤ r₀]`, and the avoidable-block bits from `I` and its reachable set. -/
def miV (Fo : Fin m → τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (j r₀ : ℕ) (a : τ) :
    (Fin m → Bool) × ℕ × Bool × (Fin k → Bool) :=
  (stateV Fo blk j a, (univ.filter fun i => stateV Fo blk j a i = true).card,
    decide ((univ.filter fun i => stateV Fo blk j a i = true).card ≤ r₀),
    avV blk (stateV Fo blk j a) (reachV Fo blk a (stateV Fo blk j a)))

end Values

/-! ### Correctness at a context where the tests answer the exchange questions -/

section Correct

variable {m k : ℕ} {τ : Type} {Fo : Fin m → τ × (Fin m → Bool) → Bool} {N : Matroid (Fin m)}
  {blk : Fin m → Fin k} {a : τ}

open Classical in
/-- **Exchange tests for `N` at the context `a`**: for every `y` and every set `A ∋ y` such that
`A - y` is independent in `N`, the test of `y` answers `[A independent in N]`.  These are the
only answers the circuit uses. -/
def ExchOracle (Fo : Fin m → τ × (Fin m → Bool) → Bool) (N : Matroid (Fin m)) (a : τ) : Prop :=
  ∀ (y : Fin m) (A : Finset (Fin m)), y ∈ A → N.Indep (A.erase y : Set (Fin m)) →
    Fo y (a, indicator A) = decide (N.Indep (A : Set (Fin m)))

open Classical in
/-- An independence oracle answers every exchange question. -/
theorem ExchOracle.of_indep {Fo : τ × (Fin m → Bool) → Bool}
    (h : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) :
    ExchOracle (fun _ => Fo) N a := fun _ A _ _ => by dsimp only; rw [h, filter_indicator]

/-- `1_J - v + u = 1_{J - v + u}`. -/
theorem exchV_indicator {J : Finset (Fin m)} {u v : Fin m} (huv : u ≠ v) :
    exchV (indicator J) u v = indicator (insert u (J.erase v)) := by
  funext i
  by_cases hiu : i = u
  · subst hiu; simp [exchV, indicator]
  · by_cases hiv : i = v
    · subst hiv; simp [exchV, indicator, hiu]
    · simp [exchV, indicator, hiu, hiv]

/-- `1_J + y = 1_{J + y}`. -/
theorem addV_indicator (J : Finset (Fin m)) (y : Fin m) :
    addV (indicator J) y = indicator (insert y J) := by
  funext i
  by_cases h : i = y
  · subst h; simp [addV, indicator]
  · simp [addV, indicator, h]

open Classical in
/-- **The arcs**: where `Fo` answers the exchange questions of `N`, `arcV` at `1_J`, `J`
independent, marks the arcs of the exchange graph of `J` (`Arc` of `Rainbow/Exchange.lean`). -/
theorem arcV_iff (hFo : ExchOracle Fo N a) {J : Finset (Fin m)} (hJ : N.Indep (J : Set (Fin m)))
    (u v : Fin m) : arcV Fo blk a (indicator J) u v = true ↔ Arc N blk J u v := by
  unfold arcV Arc
  by_cases huv : u = v
  · subst huv; by_cases hu : u ∈ J <;> simp [hu]
  · rw [if_neg huv]
    by_cases hu : u ∈ J
    · by_cases hb : blk v = blk u <;> by_cases hv : v ∈ J <;> simp [indicator, hu, hv, hb]
    · have hq : Fo u (a, exchV (indicator J) u v) =
          decide (N.Indep (insert u ((J : Set (Fin m)) \ {v}))) := by
        have hA : (insert u (J.erase v)).erase u = J.erase v :=
          erase_insert fun h => hu (mem_of_mem_erase h)
        rw [exchV_indicator huv, hFo u _ (mem_insert_self u _)
          (by rw [hA]; exact hJ.subset (coe_subset.2 (erase_subset v J)))]
        simp [coe_insert, coe_erase]
      by_cases hb : blk v = blk u <;> by_cases hv : v ∈ J <;> simp [indicator, hu, hv, hb, hq]

/-- **The sources**: `srcV` at `1_J` marks the sources of the exchange graph of `J`. -/
theorem srcV_iff (J : Finset (Fin m)) (y : Fin m) :
    srcV blk (indicator J) y = true ↔ IsSource blk J y := by
  simp [srcV, IsSource, blocksMet, indicator, and_comm]

open Classical in
/-- **The sinks**: where `Fo` answers the exchange questions of `N`, `sinkV` at `1_J`, `J`
independent, marks the sinks of the exchange graph of `J`. -/
theorem sinkV_iff (hFo : ExchOracle Fo N a) {J : Finset (Fin m)} (hJ : N.Indep (J : Set (Fin m)))
    (y : Fin m) : sinkV Fo a (indicator J) y = true ↔ IsSink N J y := by
  unfold sinkV IsSink
  by_cases hy : y ∈ J
  · simp [indicator, hy]
  · have hq : Fo y (a, addV (indicator J) y) = decide (N.Indep (insert y (J : Set (Fin m)))) := by
      rw [addV_indicator, hFo y _ (mem_insert_self y J) (by rw [erase_insert hy]; exact hJ)]
      simp [coe_insert]
    simp [indicator, hy, hq]

open Classical in
/-- **A round is `augStep`**: where `Fo` answers the exchange questions of `N`, a round maps
`1_J`, `J` independent, to the indicator vector of `augStep N blk J`, one round of the augmenting
path algorithm. -/
theorem roundV_indicator (hFo : ExchOracle Fo N a) {J : Finset (Fin m)}
    (hJ : N.Indep (J : Set (Fin m))) :
    roundV Fo blk a (indicator J) = indicator (augStep N blk J) :=
  funext fun u => (augStep_bits (srcV_iff J) (arcV_iff hFo hJ) (sinkV_iff hFo hJ) u).symm

open Classical in
/-- **`j` rounds from `∅`**: where `Fo` answers the exchange questions of `N`, the state after
`j` rounds is the indicator vector of `augStep^j(∅)`; every state is independent
(`iterate_augStep`), so every round asks only exchange questions. -/
theorem stateV_eq (hFo : ExchOracle Fo N a) (j : ℕ) :
    stateV Fo blk j a = indicator ((augStep N blk)^[j] ∅) := by
  induction j with
  | zero => funext i; simp [stateV, indicator]
  | succ j ih =>
    have h : stateV Fo blk (j + 1) a = roundV Fo blk a (stateV Fo blk j a) :=
      Function.iterate_succ_apply' _ _ _
    rw [h, ih, roundV_indicator hFo (iterate_augStep N blk j).1.1, Function.iterate_succ_apply']

open Classical in
/-- **The reachable set**: where `Fo` answers the exchange questions of `N`, `reachV` at `1_J`,
`J` independent, marks the elements reachable from a source in the exchange graph of `J`. -/
theorem reachV_iff (hFo : ExchOracle Fo N a) {J : Finset (Fin m)}
    (hJ : N.Indep (J : Set (Fin m))) (v : Fin m) :
    reachV Fo blk a (indicator J) v = true ↔ v ∈ reachSet N blk J :=
  layerV_iff_mem_reachSet (srcV_iff J) (arcV_iff hFo hJ) v

open Classical in
/-- **The avoidable blocks** (Lemma `lem:avoidable`, via `av_eq`): where `Fo` answers the
exchange questions of `N`, for a rainbow independent `J` of size `ν(N)` the bits computed from
`J` and its reachable set are `[b ∈ Av(N)]`. -/
theorem avV_eq (hFo : ExchOracle Fo N a) {J : Finset (Fin m)} (hJ : IsRainbowIndep N blk J)
    (hmax : J.card = nu N blk) (b : Fin k) :
    avV blk (indicator J) (reachV Fo blk a (indicator J)) b = decide (b ∈ Av N blk) := by
  rw [av_eq hJ hmax, Bool.eq_iff_iff]
  simp [avV, blocksMet, indicator, reachV_iff hFo hJ.1, and_comm]

open Classical in
/-- **The guard and the avoidable blocks after `j > r₀` rounds** (`lem:augment`, Steps 2 and 3).
Where `Fo` answers the exchange questions of `N`, the state `I` after `j` rounds has
`min(j, ν(N)) ≤ |I| ≤ ν(N)`, so the guard `[|I| ≤ r₀]` is `[ν(N) ≤ r₀]`, and when `ν(N) ≤ r₀`,
`|I| = ν(N)` and the avoidable-block bits are `[b ∈ Av(N)]`. -/
theorem miV_spec (hFo : ExchOracle Fo N a) {j r₀ : ℕ} (hj : r₀ < j) :
    (miV Fo blk j r₀ a).2.2.1 = decide (nu N blk ≤ r₀) ∧
      (nu N blk ≤ r₀ → ∀ b, (miV Fo blk j r₀ a).2.2.2 b = decide (b ∈ Av N blk)) := by
  obtain ⟨h1, h2⟩ := iterate_augStep N blk j
  have h3 := h1.card_le_nu
  have hs := stateV_eq (blk := blk) hFo j
  refine ⟨?_, fun hν b => ?_⟩
  · simp only [miV, hs, filter_indicator]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  · simp only [miV, hs]
    exact avV_eq hFo h1 (by omega) b

end Correct


/-! ### The gadgets -/

section Gadgets

variable {n m k : ℕ} {σ τ : Type} {Rc : Rep BoolOp Bool n σ τ}
  {bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)} {cO : ℕ}
  {Fo : Fin m → τ × (Fin m → Bool) → Bool}

/-- A static choice between two implementations, for any gate set. -/
theorem impl_ite {Op α σ₁ σ₂ τ₁ τ₂ : Type} {R₁ : Rep Op α n σ₁ τ₁} {R₂ : Rep Op α n σ₂ τ₂}
    (p : Prop) [Decidable p] {b₁ b₂ : σ₁ → Bld Op n σ₂} {c₁ c₂ : ℕ} {F₁ F₂ : τ₁ → τ₂}
    (h₁ : Impl R₁ R₂ b₁ c₁ F₁) (h₂ : Impl R₁ R₂ b₂ c₂ F₂) :
    Impl R₁ R₂ (fun s => if p then b₁ s else b₂ s) (if p then c₁ else c₂)
      (fun t => if p then F₁ t else F₂ t) := by
  by_cases hp : p
  · simp only [if_pos hp]; exact h₁
  · simp only [if_neg hp]; exact h₂

/-- Some entry of a statically masked vector is set. -/
theorem exists_ite_eq_true {p : Fin m → Prop} [DecidablePred p] (V : Fin m → Bool) :
    (∃ x, (if p x then V x else false) = true) ↔ ∃ x, p x ∧ V x = true :=
  exists_congr fun x => by by_cases h : p x <;> simp [h]

/-- `m (m - 1)` ordered pairs of distinct elements. -/
theorem sum_offDiag (c : ℕ) :
    ∑ u : Fin m, ∑ v : Fin m, (if u = v then 0 else c) = m * (m - 1) * c := by
  have h : ∀ u : Fin m, ∑ v : Fin m, (if u = v then 0 else c) = (m - 1) * c := fun u => by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
      Finset.filter_ne, Finset.card_erase_of_mem (mem_univ u), card_univ, Fintype.card_fin]
  simp only [h, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

/-- The working representation of a round: the context, the state `I`, its complement `¬I` and
the constant `true`. -/
abbrev workR (Rc : Rep BoolOp Bool n σ τ) (m : ℕ) :
    Rep BoolOp Bool n (σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n)
      (τ × (Fin m → Bool) × (Fin m → Bool) × Bool) :=
  Rc.prod ((vecR m).prod ((vecR m).prod bitR))

/-- `(a, I) ↦ (a, I, ¬I, true)`. -/
def prepB : σ × (Fin m → Arg n) → Bld BoolOp n (σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) :=
  pairB (pureB Prod.fst)
    (pairB (pureB Prod.snd) (pairB (fun s => vecNotB s.2) fun _ => emit .not .const .const))

/-- `(a, I) ↦ (a, I, ¬I, true)`: `m + 1` gates. -/
theorem prepB_impl : Impl (Rc.prod (vecR m)) (workR Rc m) prepB (m + 1)
    fun t => (t.1, t.2, fun i => !t.2 i, true) :=
  (Impl.fst.pair (Impl.snd.pair ((vecNotB_impl.pre (R := Rc.prod (vecR m)) (g := Prod.snd)
    (G := Prod.snd) fun _ _ _ hs => hs.2).pair (true_impl _)))).cost (by ring)

/-- `(p₁ ∧ (p₂ ∧ p₃)) ∨ (p₄ ∧ p₅)`. -/
def arcGateB : Arg n × Arg n × Arg n × Arg n × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (seqB (pairB (pureB fun p => p.1) fun p => emit .and p.2.1 p.2.2.1)
    fun p => emit .and p.1 p.2) fun p => emit .and p.2.2.2.1 p.2.2.2.2) fun p => emit .or p.1 p.2

/-- `(p₁ ∧ (p₂ ∧ p₃)) ∨ (p₄ ∧ p₅)`: four gates. -/
theorem arcGateB_impl :
    Impl (bitR.prod (bitR.prod (bitR.prod (bitR.prod bitR)))) (bitR (n := n)) arcGateB 4
      fun P => (P.1 && (P.2.1 && P.2.2.1)) || (P.2.2.2.1 && P.2.2.2.2) := by
  have h : Impl (bitR.prod (bitR.prod (bitR.prod (bitR.prod bitR)))) (bitR (n := n)) _ _ _ :=
    ((((Impl.free (R₁ := bitR.prod (bitR.prod (bitR.prod (bitR.prod bitR)))) (R₂ := bitR)
    (g := fun p => p.1) (F := fun P => P.1) fun _ _ _ hs => hs.1).pair
    (emitAnd_impl.pre (R := bitR.prod (bitR.prod (bitR.prod (bitR.prod bitR))))
      (g := fun p => (p.2.1, p.2.2.1)) (G := fun P => (P.2.1, P.2.2.1))
      fun _ _ _ hs => ⟨hs.2.1, hs.2.2.1⟩)).comp emitAnd_impl).pair
    (emitAnd_impl.pre (R := bitR.prod (bitR.prod (bitR.prod (bitR.prod bitR))))
      (g := fun p => (p.2.2.2.1, p.2.2.2.2)) (G := fun P => (P.2.2.2.1, P.2.2.2.2))
      fun _ _ _ hs => ⟨hs.2.2.2.1, hs.2.2.2.2⟩)).comp emitOr_impl
  exact h

/-- The arc test for `u → v`: the exchange test of `u` on `I - v + u`, then
`(¬I u ∧ (I v ∧ q)) ∨ (I u ∧ ¬I v)`, the second term only when `blk v = blk u`. -/
def arcB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (u v : Fin m) : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun s => s)
      fun s => bO u (s.1, fun i => if i = u then s.2.2.2 else if i = v then .const else s.2.1 i))
    fun p => arcGateB (p.1.2.2.1 u, p.1.2.1 v, p.2, if blk v = blk u then p.1.2.1 u else .const,
      p.1.2.2.1 v)

/-- The arc test for `u → v`: one exchange test and four gates. -/
theorem arcB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y)) (blk : Fin m → Fin k)
    (u v : Fin m) :
    Impl (workR Rc m) bitR (arcB bO blk u v) (cO + 4) fun t =>
      (t.2.2.1 u && (t.2.1 v &&
        Fo u (t.1, fun i => if i = u then t.2.2.2 else if i = v then false else t.2.1 i))) ||
        ((if blk v = blk u then t.2.1 u else false) && t.2.2.1 v) :=
  ((hO u).pre (R := workR Rc m)
    (g := fun s => (s.1, fun i => if i = u then s.2.2.2 else if i = v then .const else s.2.1 i))
    (G := fun t => (t.1, fun i => if i = u then t.2.2.2 else if i = v then false else t.2.1 i))
    fun gs _ _ hs => ⟨hs.1, fun i => by
      dsimp only; split_ifs; exacts [hs.2.2.2, den_const gs, hs.2.1 i]⟩).extend.comp
    (arcGateB_impl.pre (R := (workR Rc m).prod bitR)
      (g := fun p => (p.1.2.2.1 u, p.1.2.1 v, p.2, if blk v = blk u then p.1.2.1 u else .const,
        p.1.2.2.1 v))
      (G := fun P => (P.1.2.2.1 u, P.1.2.1 v, P.2, if blk v = blk u then P.1.2.1 u else false,
        P.1.2.2.1 v))
      fun gs _ _ hs => ⟨hs.1.2.2.1 u, hs.1.2.1 v, hs.2, by
        dsimp only; split_ifs; exacts [hs.1.2.1 u, den_const gs], hs.1.2.2.1 v⟩)

/-- The arcs of the exchange graph: no gate on the diagonal, one arc test per ordered pair of
distinct elements. -/
def arcsB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (s : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) : Bld BoolOp n (Fin m → Fin m → Arg n) :=
  tabB fun u => tabB fun v => if u = v then pureB (fun _ => .const) s else arcB bO blk u v s

/-- The arcs of the exchange graph: `m (m - 1)` exchange tests, `m (m - 1) (cO + 4)` gates. -/
theorem arcsB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) :
    Impl (workR Rc m) (relR m) (arcsB bO blk) (m * (m - 1) * (cO + 4)) fun t u v =>
      if u = v then false else
        (t.2.2.1 u && (t.2.1 v &&
          Fo u (t.1, fun i => if i = u then t.2.2.2 else if i = v then false else t.2.1 i))) ||
          ((if blk v = blk u then t.2.1 u else false) && t.2.2.1 v) :=
  (Impl.tabSum fun u => Impl.tabSum fun v =>
    impl_ite (u = v) (false_impl _) (arcB_impl hO blk u v)).cost (sum_offDiag _)

/-- The source test for `y`: no entry of `I` in the block of `y`. -/
def srcB (blk : Fin m → Fin k) (y : Fin m) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (fun s => vecAnyB fun x => if blk x = blk y then s.2.1 x else .const)
    fun a => emit .not a .const

/-- The sources of the exchange graph. -/
def srcsB (blk : Fin m → Fin k) (s : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) :
    Bld BoolOp n (Fin m → Arg n) :=
  tabB fun y => srcB blk y s

/-- The sources of the exchange graph: `m (m + 1)` gates. -/
theorem srcsB_impl (blk : Fin m → Fin k) :
    Impl (workR Rc m) (vecR m) (srcsB blk) (m * (m + 1)) fun t => srcV blk t.2.1 :=
  Impl.tab fun y => ((vecAnyB_impl.pre (R := workR Rc m)
    (g := fun s x => if blk x = blk y then s.2.1 x else .const)
    (G := fun t x => if blk x = blk y then t.2.1 x else false)
    fun gs _ _ hs x => by dsimp only; split_ifs; exacts [hs.2.1 x, den_const gs]).comp
    emitNot_impl).congr fun t => by simp only [srcV, exists_ite_eq_true]

/-- The sink test for `y`: `¬I y` and the exchange test of `y` on `I + y`. -/
def sinkB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (y : Fin m) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun s => s.2.2.1 y)
    fun s => bO y (s.1, fun i => if i = y then s.2.2.2 else s.2.1 i)) fun p => emit .and p.1 p.2

/-- The sinks of the exchange graph. -/
def sinksB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (s : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) : Bld BoolOp n (Fin m → Arg n) :=
  tabB fun y => sinkB bO y s

/-- The sinks of the exchange graph: `m` exchange tests, `m (cO + 1)` gates. -/
theorem sinksB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y)) :
    Impl (workR Rc m) (vecR m) (sinksB bO) (m * (cO + 1)) fun t y =>
      t.2.2.1 y && Fo y (t.1, fun i => if i = y then t.2.2.2 else t.2.1 i) :=
  Impl.tab fun y => (((Impl.free (R₁ := workR Rc m) (R₂ := bitR) (g := fun s => s.2.2.1 y)
    (F := fun t => t.2.2.1 y) fun _ _ _ hs => hs.2.2.1 y).pair ((hO y).pre (R := workR Rc m)
    (g := fun s => (s.1, fun i => if i = y then s.2.2.2 else s.2.1 i))
    (G := fun t => (t.1, fun i => if i = y then t.2.2.2 else t.2.1 i))
    fun gs _ _ hs => ⟨hs.1, fun i => by
      dsimp only; split_ifs; exacts [hs.2.2.2, hs.2.1 i]⟩)).comp emitAnd_impl).cost (by ring)

/-- The exchange graph of `I`: arcs, sources and sinks, from `(a, I, ¬I, true)`. -/
def graphB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n →
      Bld BoolOp n ((Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Arg n)) :=
  pairB (arcsB bO blk) (pairB (srcsB blk) (sinksB bO))

/-- **One round of the augmenting path algorithm**, from `(a, I)`: `(a, I, ¬I, true)`, the
exchange graph, and the exchange along the least-index shortest path (`exchangeB`). -/
def roundB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ × (Fin m → Arg n) → Bld BoolOp n (Fin m → Arg n) :=
  seqB prepB (seqB (pairB (pureB fun w => w.2.1) (graphB bO blk)) exchangeB)

/-- The gates of one round, `m² cO + 8m³ + 12m² + 12m + 4`. -/
def roundCost (m cO : ℕ) : ℕ := m ^ 2 * cO + 8 * m ^ 3 + 12 * m ^ 2 + 12 * m + 4

/-- The gates of the stages of a round add to `roundCost m cO`
(`m (m - 1) + m = m²`). -/
theorem roundCost_eq (m cO : ℕ) :
    m + 1 + (0 + (m * (m - 1) * (cO + 4) + (m * (m + 1) + m * (cO + 1))) + (pathCost m + 4 * m))
      = roundCost m cO := by
  cases m with
  | zero => simp [roundCost, pathCost]
  | succ m => simp only [Nat.add_sub_cancel, roundCost, pathCost]; ring

/-- **One round** (`lem:augment`, Step 1): `m (m - 1)` arc tests and `m` sink tests, one exchange
test each, then the least-index shortest path and the exchange; `roundCost m cO` gates. -/
theorem roundB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) :
    Impl (Rc.prod (vecR m)) (vecR m) (roundB bO blk) (roundCost m cO)
      fun t => roundV Fo blk t.1 t.2 := by
  have h := prepB_impl.comp (((Impl.free (R₁ := workR Rc m) (R₂ := vecR m) (g := fun w => w.2.1)
    (F := fun t => t.2.1) fun _ _ _ hs => hs.2.1).pair ((arcsB_impl hO blk).pair
    ((srcsB_impl blk).pair (sinksB_impl hO)))).comp exchangeB_impl)
  exact h.cost (roundCost_eq m cO)

/-- `j` rounds from `∅`, keeping the context: `a ↦ (a, I)`. -/
def roundsB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (j : ℕ) : σ → Bld BoolOp n (σ × (Fin m → Arg n)) :=
  pairB (pureB fun s => s)
    (seqB (pairB (pureB fun s => s) (pureB fun _ _ => .const)) (iterCtxB (roundB bO blk) j))

/-- **`j` rounds from `∅`** (`lem:augment`, Step 2): `j · roundCost m cO` gates. -/
theorem roundsB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) (j : ℕ) :
    Impl Rc (Rc.prod (vecR m)) (roundsB bO blk j) (j * roundCost m cO)
      fun a => (a, stateV Fo blk j a) := by
  have h := ((Impl.self (R := Rc)).pair (Impl.free (R₁ := Rc) (R₂ := vecR m)
    (g := fun _ _ => .const) (F := fun _ _ => false) fun gs _ _ _ _ => den_const gs)).comp
    ((roundB_impl hO blk).iterateCtx j)
  exact (h.cost (zero_add _)).extend

/-- The reachable set of the exchange graph of `I`, from `(a, I)`: the arcs and the sources,
then `m` breadth-first steps. -/
def reachB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ × (Fin m → Arg n) → Bld BoolOp n (Fin m → Arg n) :=
  seqB prepB (seqB (pairB (arcsB bO blk) (srcsB blk)) (iterCtxB bfsStepB m))

/-- **The reachable set of one more exchange graph**: `m (m - 1)` exchange tests,
`m (m - 1) (cO + 4) + 2m³ + m² + 2m + 1` gates. -/
theorem reachB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) :
    Impl (Rc.prod (vecR m)) (vecR m) (reachB bO blk)
      (m * (m - 1) * (cO + 4) + 2 * m ^ 3 + m ^ 2 + 2 * m + 1)
      fun t => reachV Fo blk t.1 t.2 := by
  have h := prepB_impl.comp (((arcsB_impl hO blk).pair (srcsB_impl blk)).comp
    (bfsStepB_impl.iterateCtx m))
  exact h.cost (by ring)

/-- The bit of block `b`, from `(I, I ∧ R)`: no entry of `I` in block `b`, or some entry of
`I ∧ R` in block `b`. -/
def avBlockB (blk : Fin m → Fin k) (b : Fin k) :
    (Fin m → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (seqB (fun s => vecAnyB fun x => if blk x = b then s.1 x else .const)
      fun a => emit .not a .const)
    fun s => vecAnyB fun x => if blk x = b then s.2 x else .const) fun p => emit .or p.1 p.2

/-- The avoidable-block bits, from `(I, R)`. -/
def avB (blk : Fin m → Fin k) : (Fin m → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Fin k → Arg n) :=
  seqB (pairB (pureB Prod.fst) vecAndB) fun s => tabB fun b => avBlockB blk b s

/-- **The avoidable-block bits** `avV blk I R`: `m + k (2m + 2)` gates. -/
theorem avB_impl (blk : Fin m → Fin k) :
    Impl ((vecR m).prod (vecR m)) (vecR (n := n) k) (avB blk) (m + k * (2 * m + 2))
      fun P => avV blk P.1 P.2 := by
  have hb : ∀ b, Impl ((vecR m).prod (vecR m)) (bitR (n := n)) (avBlockB blk b) (2 * m + 2)
      fun P => !decide (∃ x, blk x = b ∧ P.1 x = true) ||
        decide (∃ x, blk x = b ∧ P.2 x = true) := fun b => by
    have h := (((vecAnyB_impl.pre (R := (vecR m).prod (vecR m))
      (g := fun s x => if blk x = b then s.1 x else .const)
      (G := fun t x => if blk x = b then t.1 x else false)
      fun gs _ _ hs x => by dsimp only; split_ifs; exacts [hs.1 x, den_const gs]).comp
      emitNot_impl).pair (vecAnyB_impl.pre (R := (vecR m).prod (vecR m))
      (g := fun s x => if blk x = b then s.2 x else .const)
      (G := fun t x => if blk x = b then t.2 x else false)
      fun gs _ _ hs x => by dsimp only; split_ifs; exacts [hs.2 x, den_const gs])).comp
      (emitOr_impl (n := n))
    exact (h.cost (by ring)).congr fun P => by simp only [exists_ite_eq_true]
  have h := ((Impl.fst (R₁ := vecR m) (R₂ := vecR m)).pair vecAndB_impl).comp (Impl.tab hb)
  exact (h.cost (by ring)).congr fun P => by
    funext b; simp only [avV, Bool.and_eq_true]

/-- The size of `I` and the guard `[|I| ≤ r₀]`, from `I`. -/
def nuGuardB (r₀ : ℕ) : (Fin m → Arg n) → Bld BoolOp n (List (Arg n) × Arg n) :=
  seqB vecPopcountB (pairB (pureB fun s => s) (numLeConstB r₀))

/-- **The size of `I` in binary and the guard** (`lem:augment`, Step 3, "a comparison with
`r₀`"): `popCost m + 5 max(⌈log₂(m+1)⌉, ⌈log₂(r₀+1)⌉) + 2` gates. -/
theorem nuGuardB_impl (r₀ : ℕ) :
    Impl (vecR m) ((numR (Nat.size m)).prod bitR) (nuGuardB (n := n) r₀)
      (popCost m + (5 * max (Nat.size m) (Nat.size r₀) + 2)) fun V =>
        ((univ.filter fun i => V i = true).card,
          decide ((univ.filter fun i => V i = true).card ≤ r₀)) := by
  have h := (vecPopcountB_impl (n := n)).comp (Impl.self.pair (numLeConstB_impl r₀ (Nat.size m)))
  exact h.cost (by ring)

/-- The representation of the outputs: `I` (`m` bits), `|I|` (`⌈log₂(m+1)⌉` bits), the guard
(one bit) and the avoidable-block bits (`k` bits). -/
abbrev outR (m k : ℕ) : Rep BoolOp Bool n ((Fin m → Arg n) × List (Arg n) × Arg n × (Fin k → Arg n))
    ((Fin m → Bool) × ℕ × Bool × (Fin k → Bool)) :=
  (vecR m).prod ((numR (Nat.size m)).prod (bitR.prod (vecR k)))

/-- **The matroid intersection circuit**, from the context: `j` rounds from `∅`, then the size of
`I`, the guard, and the avoidable-block bits from one more exchange graph. -/
def miB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (j r₀ : ℕ) : σ → Bld BoolOp n ((Fin m → Arg n) × List (Arg n) × Arg n × (Fin k → Arg n)) :=
  seqB (roundsB bO blk j) fun s gs =>
    let q := pairB (pureB Prod.snd) (pairB (fun s => nuGuardB r₀ s.2)
      (seqB (pairB (pureB Prod.snd) (reachB bO blk)) (avB blk))) s gs
    (q.1, q.2.1, q.2.2.1.1, q.2.2.1.2, q.2.2.2)

/-- The gates of the matroid intersection circuit with `j` rounds: the rounds, the arcs, sources
and reachable set of one more exchange graph, the avoidable blocks, the population count and the
guard. -/
def miCost (m k j cO r₀ : ℕ) : ℕ :=
  j * roundCost m cO + m * (m - 1) * (cO + 4) + 2 * m ^ 3 + m ^ 2 + 3 * m + 2 * k * (m + 1) +
    popCost m + 5 * max (Nat.size m) (Nat.size r₀) + 3

/-- **The matroid intersection circuit** (`lem:augment`): from the context `a` it computes
`miV Fo blk j r₀ a` with `miCost m k j cO r₀` gates. -/
theorem miB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y)) (blk : Fin m → Fin k)
    (j r₀ : ℕ) :
    Impl Rc (outR m k) (miB bO blk j r₀) (miCost m k j cO r₀) (miV Fo blk j r₀) := by
  have hfin := ((Impl.snd (R₁ := Rc) (R₂ := vecR m)).pair (((nuGuardB_impl r₀).pre
    (R := Rc.prod (vecR m)) (g := Prod.snd) (G := Prod.snd) fun _ _ _ hs => hs.2).pair
    ((Impl.snd.pair (reachB_impl hO blk)).comp (avB_impl blk)))).post (R₃ := outR m k)
    (g := fun o => (o.1, o.2.1.1, o.2.1.2, o.2.2)) (G := fun o => (o.1, o.2.1.1, o.2.1.2, o.2.2))
    fun _ _ _ hs => ⟨hs.1, hs.2.1.1, hs.2.1.2, hs.2.2⟩
  have h := (roundsB_impl hO blk j).comp hfin
  exact h.cost (by unfold miCost; ring)

/-- **The size of the matroid intersection circuit**, with the `k` gates of the observer's
bits (`avGuardB_impl`):
`miCost m k j cO r₀ + k ≤ (j + 1)(m + 1)²(cO + 10(m + 1)) + 3k(m + 1) + 5⌈log₂(r₀+1)⌉`, that is
`(j + 1)(O(m²) · cO + O(m³)) + O(km)` gates. -/
theorem miCost_add_le (m k j cO r₀ : ℕ) :
    miCost m k j cO r₀ + k ≤
      (j + 1) * (m + 1) ^ 2 * (cO + 10 * (m + 1)) + 3 * k * (m + 1) + 5 * Nat.size r₀ := by
  have h1 : m * (m - 1) * (cO + 4) ≤ m * m * (cO + 4) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have h2 := popCost_le m
  have h3 : max (Nat.size m) (Nat.size r₀) ≤ m + Nat.size r₀ :=
    max_le ((size_le_self m).trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  unfold miCost roundCost
  nlinarith [Nat.zero_le (j * m), Nat.zero_le (j * m ^ 2), Nat.zero_le (j * m ^ 3),
    Nat.zero_le (j * m * cO), Nat.zero_le (m * cO), Nat.zero_le (j * m ^ 2 * cO),
    Nat.zero_le (j * cO), Nat.zero_le (k * m)]

end Gadgets

/-! ### Outputs for the observer and for transversal matroids, and circuits -/

section Circuit

variable {n m k : ℕ} {σ τ : Type} {Rc : Rep BoolOp Bool n σ τ}
  {bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)} {cO : ℕ}
  {Fo : Fin m → τ × (Fin m → Bool) → Bool}

/-- The bits `[|I| ≤ r₀] ∧ [b ∈ Av]` of the observer, from the context, after `j` rounds. -/
def avGuardB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (j r₀ : ℕ) : σ → Bld BoolOp n (Fin k → Arg n) :=
  seqB (miB bO blk j r₀) fun o => vecMaskB (o.2.2.1, o.2.2.2)

/-- **The bits of the observer** `F_b = [|I| ≤ r₀] ∧ [b ∈ Av]`, from the context:
`miCost m k j cO r₀ + k` gates (`avGuardV_eq` for their values). -/
theorem avGuardB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) (j r₀ : ℕ) :
    Impl Rc (vecR k) (avGuardB bO blk j r₀) (miCost m k j cO r₀ + k)
      fun a b => (miV Fo blk j r₀ a).2.2.1 && (miV Fo blk j r₀ a).2.2.2 b :=
  (miB_impl hO blk j r₀).comp (vecMaskB_impl.pre (R := outR m k)
    (g := fun o => (o.2.2.1, o.2.2.2)) (G := fun O => (O.2.2.1, O.2.2.2))
    fun _ _ _ hs => ⟨hs.2.2.1, hs.2.2.2⟩)

open Classical in
/-- **The values of the observer's bits** after `j > r₀` rounds, at a context where the tests
answer the exchange questions of `N`: `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`. -/
theorem avGuardV_eq {N : Matroid (Fin m)} {blk : Fin m → Fin k} {a : τ}
    (hFo : ExchOracle Fo N a) {j r₀ : ℕ} (hj : r₀ < j) (b : Fin k) :
    ((miV Fo blk j r₀ a).2.2.1 && (miV Fo blk j r₀ a).2.2.2 b) =
      (decide (nu N blk ≤ r₀) && decide (b ∈ Av N blk)) := by
  obtain ⟨h1, h2⟩ := miV_spec (blk := blk) hFo hj
  rw [h1]
  by_cases hν : nu N blk ≤ r₀
  · rw [h2 hν b]
  · simp [hν]

/-- **The observer's circuit** on the input `x`, the context: `k` outputs. -/
def avGuardCircuit (bO : Fin m → (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (blk : Fin m → Fin k) (r₀ : ℕ) : Circuit BoolOp n :=
  vecCircuit (avGuardB bO blk (r₀ + 1) r₀)

open Classical in
/-- **Lemma `lem:augment`, the bits.**  With exchange tests of `cO` gates, the circuit of
`r₀ + 1` rounds and one more exchange graph has `miCost m k (r₀ + 1) cO r₀ + k` gates and `k`
outputs; at every input `x` at which the tests answer the exchange questions of a matroid `N`,
output `b` is `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`. -/
theorem avGuardCircuit_spec {bO : Fin m → (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : Fin m → (Fin n → Bool) × (Fin m → Bool) → Bool}
    (hO : ∀ y, Impl ((vecR n).prod (vecR m)) bitR (bO y) cO (Fo y)) (blk : Fin m → Fin k)
    (r₀ : ℕ) :
    (avGuardCircuit bO blk r₀).size = miCost m k (r₀ + 1) cO r₀ + k ∧
      (avGuardCircuit bO blk r₀).outs.length = k ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)), ExchOracle Fo N x →
        (avGuardCircuit bO blk r₀).eval boolInterp x =
          List.ofFn fun b => decide (nu N blk ≤ r₀) && decide (b ∈ Av N blk) := by
  obtain ⟨hs, hl, he⟩ := vecCircuit_spec (avGuardB_impl hO blk (r₀ + 1) r₀)
  exact ⟨hs, hl, fun x N hFo => by
    unfold avGuardCircuit; rw [he x, funext (avGuardV_eq hFo (Nat.lt_succ_self r₀))]⟩

/-- `ν` alone, from the context: `k` rounds and a population count. -/
def nuB (bO : Fin m → σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ → Bld BoolOp n (List (Arg n)) :=
  seqB (roundsB bO blk k) fun s => vecPopcountB s.2

/-- **`ν` alone** (for instance the rank of a transversal matroid): `k` rounds and a population
count, `k · roundCost m cO + popCost m` gates, on `⌈log₂(m+1)⌉` bits. -/
theorem nuB_impl (hO : ∀ y, Impl (Rc.prod (vecR m)) bitR (bO y) cO (Fo y))
    (blk : Fin m → Fin k) :
    Impl Rc (numR (Nat.size m)) (nuB bO blk) (k * roundCost m cO + popCost m)
      fun a => (univ.filter fun i => stateV Fo blk k a i = true).card :=
  (roundsB_impl hO blk k).comp (vecPopcountB_impl.pre (R := Rc.prod (vecR m)) (g := Prod.snd)
    (G := Prod.snd) fun _ _ _ hs => hs.2)

open Classical in
/-- **The value of `ν` alone** at a context where the tests answer the exchange questions of
`N`: `k ≥ ν(N)` rounds (`nu_le`). -/
theorem card_stateV {N : Matroid (Fin m)} {blk : Fin m → Fin k} {a : τ}
    (hFo : ExchOracle Fo N a) :
    (univ.filter fun i => stateV Fo blk k a i = true).card = nu N blk := by
  rw [stateV_eq hFo, filter_indicator, card_iterate_augStep N blk (nu_le N blk)]

/-- **`ν` alone, as a circuit** on the input `x`, the context. -/
def nuCircuit (bO : Fin m → (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (blk : Fin m → Fin k) : Circuit BoolOp n :=
  circuitOf (nuB bO blk)

open Classical in
/-- **Lemma `lem:augment`, `ν` alone, as a circuit**: `k · roundCost m cO + popCost m` gates and
`⌈log₂(m+1)⌉` outputs; at every input `x` at which the tests answer the exchange questions of a
matroid `N`, the outputs are the binary digits of `ν(N)`. -/
theorem nuCircuit_spec {bO : Fin m → (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : Fin m → (Fin n → Bool) × (Fin m → Bool) → Bool}
    (hO : ∀ y, Impl ((vecR n).prod (vecR m)) bitR (bO y) cO (Fo y)) (blk : Fin m → Fin k) :
    (nuCircuit bO blk).size = k * roundCost m cO + popCost m ∧
      (nuCircuit bO blk).outs.length = Nat.size m ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)), ExchOracle Fo N x →
        bitsVal ((nuCircuit bO blk).eval boolInterp x) = nu N blk := by
  obtain ⟨hs, hl, he⟩ := circuitOf_num (nuB_impl hO blk)
  exact ⟨hs, hl, fun x N hFo => (he x).trans (card_stateV hFo)⟩

end Circuit

end SignedTropical.Rainbow.MI
