import SignedTropical.BoolAlg.ExchangeBits
import SignedTropical.BoolAlg.Count

/-!
# The matroid intersection circuit

`greedy_intersection.tex`, Lemma `lem:augment` (used in Lemma `lem:observer`, Step 4, and in
Corollary `cor:transversal`): `k` rounds of the augmenting path algorithm (Lawler; Schrijver,
Theorem 41.2) on a matroid `N` on `Fin m` and the blocks of `blk : Fin m → Fin k`, then one more
exchange graph, its reachable set, the avoidable blocks `Av(N)` (Lemma `lem:avoidable`) and the
guard `[ν(N) ≤ r₀]`, as a Boolean circuit with an exact gate count.

The matroid may depend on the input of the circuit (in `lem:observer` it is `N_G`, determined
by the input relation `G`).  The construction is parametrized by a *context*, carried by a
representation `Rc` (the input bits, or data computed from them once), and an *independence
oracle*, a gadget `hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo` that reads the context and the
bits of a set `A` and outputs a bit `Fo (a, A)` with `cO` gates.  Nothing is assumed about `Fo`
to build and count the circuit; its outputs are correct at every context `a` at which `Fo (a, ·)`
answers independence in a matroid `N`, that is `Fo (a, A) = [A independent in N]` for every `A`.
The circuit queries the oracle only at its own context.

* Values (`exchV`, `addV`, `arcV`, `srcV`, `sinkV`, `roundV`, `stateV`, `reachV`, `avV`, `miV`):
  what the circuit computes, as functions of the context.
* Correctness (`arcV_iff`, `srcV_iff`, `sinkV_iff`, `roundV_indicator`, `stateV_eq`,
  `reachV_iff`, `avV_eq`, `miV_spec`): where the oracle answers independence in `N`, the bits are
  the exchange graph of `Rainbow/Exchange.lean`, a round is `augStep`, `k` rounds from `∅` give
  `augStep^k(∅)`, a rainbow independent set of size `ν(N)` (`iterate_augStep`), and the
  avoidable-block bits are `[b ∈ Av(N)]` (`av_eq`).
* Gadgets with exact gate counts (`Impl` of `BoolAlg/Impl.lean`): one round (`roundB_impl`,
  `m(m-1)` arc tests and `m` sink tests, one oracle query each, then the least-index shortest
  path and the exchange, `roundCost m cO = m²cO + 8m³ + 12m² + 12m + 4` gates), `k` rounds
  (`roundsB_impl`), the reachable set of one more exchange graph (`reachB_impl`), the avoidable
  blocks (`avB_impl`), the population count and the guard (`nuGuardB_impl`), and everything
  (`miB_impl`, `miCost m k cO r₀` gates, at most `(k+1)(m+1)²(cO + 10(m+1)) + 5⌈log₂(r₀+1)⌉`
  by `miCost_le`).  `lem_observer_step4` packages the circuit, its size and its outputs.
* For the observer, the bits `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]` (`avGuardB_impl`, `avGuardV_eq`); for
  rank circuits obtained by matroid intersection, `ν(N)` alone (`nuB_impl`, `card_stateV`).
  When the context is the input of the circuit: `miCircuit_spec`, `avGuardCircuit_spec`,
  `nuCircuit_spec`.
* Oracles from rank queries (value `indepOfRankV`; `indepOfRankB_impl`, `indepOfRank_correct`)
  and from one rank circuit reading (context bits, set bits) (value `rankQueryV`;
  `circuitOracleB_impl`, `circuitOracle_correct`), and the whole circuit with a rank circuit of
  size `s` (`rankMICircuit_spec`, at most `(k+1)(m+1)²(s + 37(m+1)) + 5⌈log₂(r₀+1)⌉` gates).
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

/-- The arc bits of the exchange graph of `I`, independence being answered by the oracle `Fo` at
the context `a`: no arc `u → u`, and for `u ≠ v` an arc `u → v` iff `u ∉ I`, `v ∈ I` and
`Fo(a, I - v + u)`, or `u ∈ I`, `v ∉ I` and `blk v = blk u`. -/
def arcV (Fo : τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ) (I : Fin m → Bool)
    (u v : Fin m) : Bool :=
  if u = v then false
  else (!I u && (I v && Fo (a, exchV I u v))) || ((if blk v = blk u then I u else false) && !I v)

/-- The source bits: no element of `I` lies in the block of `y`. -/
def srcV (blk : Fin m → Fin k) (I : Fin m → Bool) (y : Fin m) : Bool :=
  !decide (∃ x, blk x = blk y ∧ I x = true)

/-- The sink bits: `y ∉ I` and `Fo(a, I + y)`. -/
def sinkV (Fo : τ × (Fin m → Bool) → Bool) (a : τ) (I : Fin m → Bool) (y : Fin m) : Bool :=
  !I y && Fo (a, addV I y)

/-- One round of the augmenting path algorithm at the context `a`: `I` exclusive-or the
least-index shortest path from the sources to the sinks (`pathV` of `BoolAlg/Path.lean`). -/
def roundV (Fo : τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ) (I : Fin m → Bool) :
    Fin m → Bool :=
  fun u => I u ^^ pathV (arcV Fo blk a I) (srcV blk I) (sinkV Fo a I) u

/-- The state after `k` rounds from `∅`, `k` the number of blocks. -/
def stateV (Fo : τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ) : Fin m → Bool :=
  (roundV Fo blk a)^[k] fun _ => false

/-- The elements reachable from a source in the exchange graph of `I`: layer `m` of the
breadth-first search. -/
def reachV (Fo : τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (a : τ) (I : Fin m → Bool) :
    Fin m → Bool :=
  layerV (arcV Fo blk a I) (srcV blk I) m

/-- The avoidable-block bits from `I` and a set `R`: block `b` is missed by `I`, or contains an
element of `I ∩ R`. -/
def avV (blk : Fin m → Fin k) (I R : Fin m → Bool) (b : Fin k) : Bool :=
  !decide (∃ x, blk x = b ∧ I x = true) || decide (∃ x, blk x = b ∧ I x = true ∧ R x = true)

/-- The outputs at the context `a`: the state `I` after `k` rounds, its size, the guard
`[|I| ≤ r₀]`, and the avoidable-block bits from `I` and its reachable set. -/
def miV (Fo : τ × (Fin m → Bool) → Bool) (blk : Fin m → Fin k) (r₀ : ℕ) (a : τ) :
    (Fin m → Bool) × ℕ × Bool × (Fin k → Bool) :=
  (stateV Fo blk a, (univ.filter fun i => stateV Fo blk a i = true).card,
    decide ((univ.filter fun i => stateV Fo blk a i = true).card ≤ r₀),
    avV blk (stateV Fo blk a) (reachV Fo blk a (stateV Fo blk a)))

end Values

/-! ### Correctness at a context where the oracle answers independence -/

section Correct

variable {m k : ℕ} {τ : Type} {Fo : τ × (Fin m → Bool) → Bool} {N : Matroid (Fin m)}
  {blk : Fin m → Fin k} {a : τ}

open Classical in
/-- **The arcs**: where `Fo` answers independence in `N`, `arcV` at `1_J` marks the arcs of the
exchange graph of `J` (`Arc` of `Rainbow/Exchange.lean`). -/
theorem arcV_iff (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    (J : Finset (Fin m)) (u v : Fin m) :
    arcV Fo blk a (indicator J) u v = true ↔ Arc N blk J u v := by
  unfold arcV Arc
  by_cases huv : u = v
  · subst huv; by_cases hu : u ∈ J <;> simp [hu]
  · rw [if_neg huv]
    have hset : ((univ.filter fun i => exchV (indicator J) u v i = true : Finset (Fin m)) :
        Set (Fin m)) = insert u ((J : Set (Fin m)) \ {v}) := by
      ext i
      by_cases hiu : i = u
      · subst hiu; simp [exchV, huv]
      · by_cases hiv : i = v
        · subst hiv; simp [exchV, hiu]
        · simp [exchV, indicator, hiu, hiv]
    rw [hFo, hset]
    by_cases hb : blk v = blk u <;> by_cases hu : u ∈ J <;> by_cases hv : v ∈ J <;>
      simp [indicator, hu, hv, hb]

/-- **The sources**: `srcV` at `1_J` marks the sources of the exchange graph of `J`. -/
theorem srcV_iff (J : Finset (Fin m)) (y : Fin m) :
    srcV blk (indicator J) y = true ↔ IsSource blk J y := by
  simp [srcV, IsSource, blocksMet, indicator, and_comm]

open Classical in
/-- **The sinks**: where `Fo` answers independence in `N`, `sinkV` at `1_J` marks the sinks of
the exchange graph of `J`. -/
theorem sinkV_iff (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    (J : Finset (Fin m)) (y : Fin m) : sinkV Fo a (indicator J) y = true ↔ IsSink N J y := by
  have hset : ((univ.filter fun i => addV (indicator J) y i = true : Finset (Fin m)) :
      Set (Fin m)) = insert y (J : Set (Fin m)) := by
    ext i
    by_cases h : i = y
    · subst h; simp [addV]
    · simp [addV, indicator, h]
  simp [sinkV, IsSink, hFo, hset, indicator]

open Classical in
/-- **A round is `augStep`**: where `Fo` answers independence in `N`, a round maps `1_J` to the
indicator vector of `augStep N blk J`, one round of the augmenting path algorithm. -/
theorem roundV_indicator
    (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    (J : Finset (Fin m)) : roundV Fo blk a (indicator J) = indicator (augStep N blk J) :=
  funext fun u => (augStep_bits (srcV_iff J) (arcV_iff hFo J) (sinkV_iff hFo J) u).symm

open Classical in
/-- **`k` rounds from `∅`**: where `Fo` answers independence in `N`, the state after `k` rounds
is the indicator vector of `augStep^k(∅)`. -/
theorem stateV_eq (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) :
    stateV Fo blk a = indicator ((augStep N blk)^[k] ∅) := by
  have hsemi : Function.Semiconj indicator (augStep N blk) (roundV Fo blk a) := fun J =>
    (roundV_indicator hFo J).symm
  have h0 : indicator (∅ : Finset (Fin m)) = fun _ => false := funext fun _ => by simp [indicator]
  rw [stateV, ← h0]
  exact (hsemi.iterate_right k ∅).symm

open Classical in
/-- **The reachable set**: where `Fo` answers independence in `N`, `reachV` at `1_J` marks the
elements reachable from a source in the exchange graph of `J`. -/
theorem reachV_iff (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    (J : Finset (Fin m)) (v : Fin m) :
    reachV Fo blk a (indicator J) v = true ↔ v ∈ reachSet N blk J :=
  layerV_iff_mem_reachSet (srcV_iff J) (arcV_iff hFo J) v

open Classical in
/-- **The avoidable blocks** (Lemma `lem:avoidable`, via `av_eq`): where `Fo` answers
independence in `N`, for a rainbow independent `J` of size `ν(N)` the bits computed from `J` and
its reachable set are `[b ∈ Av(N)]`. -/
theorem avV_eq (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    {J : Finset (Fin m)} (hJ : IsRainbowIndep N blk J) (hmax : J.card = nu N blk) (b : Fin k) :
    avV blk (indicator J) (reachV Fo blk a (indicator J)) b = decide (b ∈ Av N blk) := by
  rw [av_eq hJ hmax, Bool.eq_iff_iff]
  simp [avV, blocksMet, indicator, reachV_iff hFo, and_comm]

open Classical in
/-- **The outputs at a context where the oracle answers independence in `N`**
(`lem:augment`, Steps 2 and 3).  If `Fo(a, A)` is the bit `[A independent in N]` for every `A`, then
at the context `a` the first output is the indicator vector of `J = augStep^k(∅)`, a rainbow
independent set of size `ν(N)` (`iterate_augStep`), the second is `ν(N)`, the third is the
guard `[ν(N) ≤ r₀]`, and the last ones are the bits `[b ∈ Av(N)]` (`av_eq`). -/
theorem miV_spec (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)))
    (r₀ : ℕ) :
    (miV Fo blk r₀ a).1 = indicator ((augStep N blk)^[k] ∅) ∧
      IsRainbowIndep N blk ((augStep N blk)^[k] ∅) ∧ ((augStep N blk)^[k] ∅).card = nu N blk ∧
      (miV Fo blk r₀ a).2.1 = nu N blk ∧ (miV Fo blk r₀ a).2.2.1 = decide (nu N blk ≤ r₀) ∧
      ∀ b, (miV Fo blk r₀ a).2.2.2 b = decide (b ∈ Av N blk) := by
  obtain ⟨h1, h2⟩ := iterate_augStep N blk
  have hs := stateV_eq (blk := blk) hFo
  refine ⟨hs, h1, h2, ?_, ?_, fun b => ?_⟩
  · simp only [miV, hs, filter_indicator, h2]
  · simp only [miV, hs, filter_indicator, h2]
  · simp only [miV, hs]
    exact avV_eq hFo h1 h2 b

end Correct


/-! ### The gadgets -/

section Gadgets

variable {n m k : ℕ} {σ τ : Type} {Rc : Rep BoolOp Bool n σ τ}
  {bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)} {cO : ℕ} {Fo : τ × (Fin m → Bool) → Bool}

/-- A static choice between two implementations. -/
theorem impl_ite {α σ₁ σ₂ τ₁ τ₂ : Type} {R₁ : Rep BoolOp α n σ₁ τ₁} {R₂ : Rep BoolOp α n σ₂ τ₂}
    (p : Prop) [Decidable p] {b₁ b₂ : σ₁ → Bld BoolOp n σ₂} {c₁ c₂ : ℕ} {F₁ F₂ : τ₁ → τ₂}
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

/-- The arc test for `u → v`: the oracle on `I - v + u`, then
`(¬I u ∧ (I v ∧ q)) ∨ (I u ∧ ¬I v)`, the second term only when `blk v = blk u`. -/
def arcB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) (u v : Fin m) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun s => s)
      fun s => bO (s.1, fun i => if i = u then s.2.2.2 else if i = v then .const else s.2.1 i))
    fun p => arcGateB (p.1.2.2.1 u, p.1.2.1 v, p.2, if blk v = blk u then p.1.2.1 u else .const,
      p.1.2.2.1 v)

/-- The arc test for `u → v`: one oracle query and four gates. -/
theorem arcB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k)
    (u v : Fin m) :
    Impl (workR Rc m) bitR (arcB bO blk u v) (cO + 4) fun t =>
      (t.2.2.1 u && (t.2.1 v &&
        Fo (t.1, fun i => if i = u then t.2.2.2 else if i = v then false else t.2.1 i))) ||
        ((if blk v = blk u then t.2.1 u else false) && t.2.2.1 v) :=
  (hO.pre (R := workR Rc m)
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
def arcsB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (s : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) : Bld BoolOp n (Fin m → Fin m → Arg n) :=
  tabB fun u => tabB fun v => if u = v then pureB (fun _ => .const) s else arcB bO blk u v s

/-- The arcs of the exchange graph: `m (m - 1)` oracle queries, `m (m - 1) (cO + 4)` gates. -/
theorem arcsB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) :
    Impl (workR Rc m) (relR m) (arcsB bO blk) (m * (m - 1) * (cO + 4)) fun t u v =>
      if u = v then false else
        (t.2.2.1 u && (t.2.1 v &&
          Fo (t.1, fun i => if i = u then t.2.2.2 else if i = v then false else t.2.1 i))) ||
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

/-- The sink test for `y`: `¬I y` and the oracle on `I + y`. -/
def sinkB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (y : Fin m) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n → Bld BoolOp n (Arg n) :=
  seqB (pairB (pureB fun s => s.2.2.1 y)
    fun s => bO (s.1, fun i => if i = y then s.2.2.2 else s.2.1 i)) fun p => emit .and p.1 p.2

/-- The sinks of the exchange graph. -/
def sinksB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (s : σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n) : Bld BoolOp n (Fin m → Arg n) :=
  tabB fun y => sinkB bO y s

/-- The sinks of the exchange graph: `m` oracle queries, `m (cO + 1)` gates. -/
theorem sinksB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) :
    Impl (workR Rc m) (vecR m) (sinksB bO) (m * (cO + 1)) fun t y =>
      t.2.2.1 y && Fo (t.1, fun i => if i = y then t.2.2.2 else t.2.1 i) :=
  Impl.tab fun y => (((Impl.free (R₁ := workR Rc m) (R₂ := bitR) (g := fun s => s.2.2.1 y)
    (F := fun t => t.2.2.1 y) fun _ _ _ hs => hs.2.2.1 y).pair (hO.pre (R := workR Rc m)
    (g := fun s => (s.1, fun i => if i = y then s.2.2.2 else s.2.1 i))
    (G := fun t => (t.1, fun i => if i = y then t.2.2.2 else t.2.1 i))
    fun gs _ _ hs => ⟨hs.1, fun i => by
      dsimp only; split_ifs; exacts [hs.2.2.2, hs.2.1 i]⟩)).comp emitAnd_impl).cost (by ring)

/-- The exchange graph of `I`: arcs, sources and sinks, from `(a, I, ¬I, true)`. -/
def graphB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ × (Fin m → Arg n) × (Fin m → Arg n) × Arg n →
      Bld BoolOp n ((Fin m → Fin m → Arg n) × (Fin m → Arg n) × (Fin m → Arg n)) :=
  pairB (arcsB bO blk) (pairB (srcsB blk) (sinksB bO))

/-- **One round of the augmenting path algorithm**, from `(a, I)`: `(a, I, ¬I, true)`, the
exchange graph, and the exchange along the least-index shortest path (`exchangeB`). -/
def roundB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
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

/-- **One round** (`lem:augment`, Step 1): `m (m - 1)` arc tests and `m` sink tests, one oracle
query each, then the least-index shortest path and the exchange; `roundCost m cO` gates. -/
theorem roundB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) :
    Impl (Rc.prod (vecR m)) (vecR m) (roundB bO blk) (roundCost m cO)
      fun t => roundV Fo blk t.1 t.2 := by
  have h := prepB_impl.comp (((Impl.free (R₁ := workR Rc m) (R₂ := vecR m) (g := fun w => w.2.1)
    (F := fun t => t.2.1) fun _ _ _ hs => hs.2.1).pair ((arcsB_impl hO blk).pair
    ((srcsB_impl blk).pair (sinksB_impl hO)))).comp exchangeB_impl)
  exact h.cost (roundCost_eq m cO)

/-- `k` rounds from `∅`, keeping the context: `a ↦ (a, I)`. -/
def roundsB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ → Bld BoolOp n (σ × (Fin m → Arg n)) :=
  pairB (pureB fun s => s)
    (seqB (pairB (pureB fun s => s) (pureB fun _ _ => .const)) (iterCtxB (roundB bO blk) k))

/-- **`k` rounds from `∅`**, `k` the number of blocks: `k · roundCost m cO` gates. -/
theorem roundsB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) :
    Impl Rc (Rc.prod (vecR m)) (roundsB bO blk) (k * roundCost m cO)
      fun a => (a, stateV Fo blk a) := by
  have h := ((Impl.self (R := Rc)).pair (Impl.free (R₁ := Rc) (R₂ := vecR m)
    (g := fun _ _ => .const) (F := fun _ _ => false) fun gs _ _ _ _ => den_const gs)).comp
    ((roundB_impl hO blk).iterateCtx k)
  exact (h.cost (zero_add _)).extend

/-- The reachable set of the exchange graph of `I`, from `(a, I)`: the arcs and the sources,
then `m` breadth-first steps. -/
def reachB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ × (Fin m → Arg n) → Bld BoolOp n (Fin m → Arg n) :=
  seqB prepB (seqB (pairB (arcsB bO blk) (srcsB blk)) (iterCtxB bfsStepB m))

/-- **The reachable set of one more exchange graph**: `m (m - 1)` oracle queries,
`m (m - 1) (cO + 4) + 2m³ + m² + 2m + 1` gates. -/
theorem reachB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) :
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

/-- **The matroid intersection circuit**, from the context: `k` rounds from `∅`, then the size of
`I`, the guard, and the avoidable-block bits from one more exchange graph. -/
def miB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) (r₀ : ℕ) :
    σ → Bld BoolOp n ((Fin m → Arg n) × List (Arg n) × Arg n × (Fin k → Arg n)) :=
  seqB (roundsB bO blk) fun s gs =>
    let q := pairB (pureB Prod.snd) (pairB (fun s => nuGuardB r₀ s.2)
      (seqB (pairB (pureB Prod.snd) (reachB bO blk)) (avB blk))) s gs
    (q.1, q.2.1, q.2.2.1.1, q.2.2.1.2, q.2.2.2)

/-- The gates of the matroid intersection circuit: `k` rounds, the arcs, sources and reachable
set of one more exchange graph, the avoidable blocks, the population count and the guard. -/
def miCost (m k cO r₀ : ℕ) : ℕ :=
  k * roundCost m cO + m * (m - 1) * (cO + 4) + 2 * m ^ 3 + m ^ 2 + 3 * m + 2 * k * (m + 1) +
    popCost m + 5 * max (Nat.size m) (Nat.size r₀) + 3

/-- **The matroid intersection circuit** (`lem:augment`): from the context `a` it
computes `miV Fo blk r₀ a` with `miCost m k cO r₀` gates. -/
theorem miB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) (r₀ : ℕ) :
    Impl Rc (outR m k) (miB bO blk r₀) (miCost m k cO r₀) (miV Fo blk r₀) := by
  have hfin := ((Impl.snd (R₁ := Rc) (R₂ := vecR m)).pair (((nuGuardB_impl r₀).pre
    (R := Rc.prod (vecR m)) (g := Prod.snd) (G := Prod.snd) fun _ _ _ hs => hs.2).pair
    ((Impl.snd.pair (reachB_impl hO blk)).comp (avB_impl blk)))).post (R₃ := outR m k)
    (g := fun o => (o.1, o.2.1.1, o.2.1.2, o.2.2)) (G := fun o => (o.1, o.2.1.1, o.2.1.2, o.2.2))
    fun _ _ _ hs => ⟨hs.1, hs.2.1.1, hs.2.1.2, hs.2.2⟩
  have h := (roundsB_impl hO blk).comp hfin
  exact h.cost (by unfold miCost; ring)

/-- **The size of the matroid intersection circuit**, with the `k` gates of the observer's
bits (`avGuardB_impl`): `miCost m k cO r₀ + k ≤ (k + 1)(m + 1)²(cO + 10(m + 1)) + 5⌈log₂(r₀+1)⌉`,
that is `(k + 1)(O(m²) · cO + O(m³))` gates. -/
theorem miCost_add_le (m k cO r₀ : ℕ) :
    miCost m k cO r₀ + k ≤ (k + 1) * (m + 1) ^ 2 * (cO + 10 * (m + 1)) + 5 * Nat.size r₀ := by
  have h1 : m * (m - 1) * (cO + 4) ≤ m * m * (cO + 4) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have h2 := popCost_le m
  have h3 : max (Nat.size m) (Nat.size r₀) ≤ m + Nat.size r₀ :=
    max_le ((size_le_self m).trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  unfold miCost roundCost
  nlinarith [Nat.zero_le (k * m), Nat.zero_le (k * m ^ 2), Nat.zero_le (k * m ^ 3),
    Nat.zero_le (k * m * cO), Nat.zero_le (m * cO), Nat.zero_le (k * m ^ 2 * cO),
    Nat.zero_le (k * cO)]

/-- **The size of the matroid intersection circuit**:
`miCost m k cO r₀ ≤ (k + 1)(m + 1)²(cO + 10(m + 1)) + 5⌈log₂(r₀+1)⌉`. -/
theorem miCost_le (m k cO r₀ : ℕ) :
    miCost m k cO r₀ ≤ (k + 1) * (m + 1) ^ 2 * (cO + 10 * (m + 1)) + 5 * Nat.size r₀ :=
  (Nat.le_add_right _ k).trans (miCost_add_le m k cO r₀)

/-- **The size with an oracle from a rank query** of `cR` gates (`indepOfRankB_impl`, whose
cost is `cR + popCost m + 5⌈log₂(m+1)⌉ + 1`): at most
`(k + 1)(m + 1)²(cR + 37(m + 1)) + 5⌈log₂(r₀+1)⌉`, with the observer's `k` gates. -/
theorem miCost_rank_le (m k cR r₀ : ℕ) :
    miCost m k (cR + popCost m + (5 * Nat.size m + 1)) r₀ + k ≤
      (k + 1) * (m + 1) ^ 2 * (cR + 37 * (m + 1)) + 5 * Nat.size r₀ := by
  refine (miCost_add_le _ _ _ _).trans ?_
  have h1 := popCost_le m
  have h2 := size_le_self m
  have h3 : cR + popCost m + (5 * Nat.size m + 1) + 10 * (m + 1) ≤ cR + 37 * (m + 1) := by
    omega
  have := Nat.mul_le_mul_left ((k + 1) * (m + 1) ^ 2) h3
  omega

open Classical in
/-- **Lemma `lem:augment`** (the generic circuit, used in Lemma `lem:observer`, Step 4).  Let `bO` implement an oracle `Fo`
from (context, set) with `cO` gates.  Then `miB bO blk r₀` computes `miV Fo blk r₀` from the
context with `miCost m k cO r₀` gates, `miCost m k cO r₀ + k ≤ (k + 1)(m + 1)²(cO + 10(m + 1)) +
5⌈log₂(r₀+1)⌉`, and at every context `a` at which `Fo (a, ·)` answers independence in a matroid
`N`, the outputs are the indicator vector of the rainbow independent set `augStep^k(∅)` of size
`ν(N)`, the number `ν(N)`, the guard `[ν(N) ≤ r₀]` and the bits `[b ∈ Av(N)]`. -/
theorem lem_observer_step4 (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k)
    (r₀ : ℕ) :
    Impl Rc (outR m k) (miB bO blk r₀) (miCost m k cO r₀) (miV Fo blk r₀) ∧
      miCost m k cO r₀ + k ≤ (k + 1) * (m + 1) ^ 2 * (cO + 10 * (m + 1)) + 5 * Nat.size r₀ ∧
      ∀ (a : τ) (N : Matroid (Fin m)),
        (∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) →
        (miV Fo blk r₀ a).1 = indicator ((augStep N blk)^[k] ∅) ∧
          IsRainbowIndep N blk ((augStep N blk)^[k] ∅) ∧
          ((augStep N blk)^[k] ∅).card = nu N blk ∧ (miV Fo blk r₀ a).2.1 = nu N blk ∧
          (miV Fo blk r₀ a).2.2.1 = decide (nu N blk ≤ r₀) ∧
          ∀ b, (miV Fo blk r₀ a).2.2.2 b = decide (b ∈ Av N blk) :=
  ⟨miB_impl hO blk r₀, miCost_add_le m k cO r₀, fun _ _ hFo => miV_spec hFo r₀⟩

end Gadgets

/-! ### Outputs for the observer and for transversal matroids, and circuits -/

section Circuit

variable {n m k : ℕ} {σ τ : Type} {Rc : Rep BoolOp Bool n σ τ}
  {bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)} {cO : ℕ} {Fo : τ × (Fin m → Bool) → Bool}

/-- A number carried on `w` bits is carried by its binary digits `N.testBit i`, `i < w`. -/
theorem numR_bitsR {w : ℕ} {gs : List (Gate BoolOp n)} {as : List (Arg n)}
    {N : (Fin n → Bool) → ℕ} (h : (numR w).rep gs as N) :
    (bitsR w).rep gs as fun x => (List.range w).map (N x).testBit := by
  obtain ⟨A, hA, hl, hv⟩ := numR_bits h
  refine ⟨h.1, hA.congr fun x => eq_of_bitsVal_eq (by simp [hl x]) ?_⟩
  rw [hv x, bitsVal_testBit, Nat.mod_eq_of_lt (numR_lt h x)]

/-- The outputs as one list of operands. -/
def flatB (o : (Fin m → Arg n) × List (Arg n) × Arg n × (Fin k → Arg n)) : List (Arg n) :=
  List.ofFn o.1 ++ o.2.1 ++ o.2.2.1 :: List.ofFn o.2.2.2

/-- The outputs as one list of bits: the bits of `I`, the `w` binary digits of the number
(least significant first), the guard, and the avoidable-block bits. -/
def flatV (w : ℕ) (o : (Fin m → Bool) × ℕ × Bool × (Fin k → Bool)) : List Bool :=
  List.ofFn o.1 ++ (List.range w).map o.2.1.testBit ++ o.2.2.1 :: List.ofFn o.2.2.2

/-- Flattening the outputs is free. -/
theorem flatB_impl :
    Impl (outR m k) (bitsR (m + Nat.size m + (k + 1))) (pureB (n := n) flatB) 0
      (flatV (Nat.size m)) :=
  Impl.free fun _ _ _ hs => by
    have hb := numR_bitsR hs.2.1
    refine ⟨by simp only [flatB, List.length_append, List.length_ofFn, List.length_cons, hb.1],
      ((denL_ofFn hs.1).append hb.2).append (DenL.cons hs.2.2.1 (denL_ofFn hs.2.2.2))⟩

/-- **The matroid intersection circuit** on the input `x`, the context: its outputs are the bits
of `I`, the binary digits of `|I|`, the guard and the avoidable-block bits. -/
def miCircuit (bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (blk : Fin m → Fin k) (r₀ : ℕ) : Circuit BoolOp n :=
  circuitOf (seqB (miB bO blk r₀) (pureB flatB))

open Classical in
/-- **The matroid intersection circuit** (`lem:augment`).  Let `bO` implement the
oracle `Fo` from (input, set) with `cO` gates.  The circuit has `miCost m k cO r₀` gates and
`m + ⌈log₂(m+1)⌉ + k + 1` outputs.  At every input `x` at which `Fo(x, ·)` answers independence
in a matroid `N`, it outputs the indicator vector of the rainbow independent set
`augStep^k(∅)` of size `ν(N)`, the binary digits of `ν(N)`, the guard `[ν(N) ≤ r₀]` and the
bits `[b ∈ Av(N)]`. -/
theorem miCircuit_spec {bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : (Fin n → Bool) × (Fin m → Bool) → Bool} (hO : Impl ((vecR n).prod (vecR m)) bitR bO cO Fo)
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    (miCircuit bO blk r₀).size = miCost m k cO r₀ ∧
      (miCircuit bO blk r₀).outs.length = m + Nat.size m + (k + 1) ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)),
        (∀ A, Fo (x, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) →
        (miCircuit bO blk r₀).eval boolInterp x =
          List.ofFn (indicator ((augStep N blk)^[k] ∅)) ++
            (List.range (Nat.size m)).map (nu N blk).testBit ++
            decide (nu N blk ≤ r₀) :: List.ofFn fun b => decide (b ∈ Av N blk) := by
  obtain ⟨hs, hl, he⟩ :=
    circuitOf_spec (((miB_impl hO blk r₀).comp flatB_impl).cost (Nat.add_zero _))
  refine ⟨hs, hl, fun x N hFo => ?_⟩
  obtain ⟨h1, -, -, h2, h3, h4⟩ := miV_spec (blk := blk) hFo r₀
  unfold miCircuit
  rw [he x, flatV, h1, h2, h3, funext h4]

/-- The bits `[|I| ≤ r₀] ∧ [b ∈ Av]` of the observer, from the context. -/
def avGuardB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k)
    (r₀ : ℕ) : σ → Bld BoolOp n (Fin k → Arg n) :=
  seqB (miB bO blk r₀) fun o => vecMaskB (o.2.2.1, o.2.2.2)

/-- **The bits of the observer** `F_b = [ν ≤ r₀] ∧ [b ∈ Av]`, from the context:
`miCost m k cO r₀ + k` gates (`avGuardV_eq` for their values). -/
theorem avGuardB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k)
    (r₀ : ℕ) :
    Impl Rc (vecR k) (avGuardB bO blk r₀) (miCost m k cO r₀ + k)
      fun a b => (miV Fo blk r₀ a).2.2.1 && (miV Fo blk r₀ a).2.2.2 b :=
  (miB_impl hO blk r₀).comp (vecMaskB_impl.pre (R := outR m k) (g := fun o => (o.2.2.1, o.2.2.2))
    (G := fun O => (O.2.2.1, O.2.2.2)) fun _ _ _ hs => ⟨hs.2.2.1, hs.2.2.2⟩)

open Classical in
/-- **The values of the observer's bits** at a context where the oracle answers independence
in `N`: `[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`. -/
theorem avGuardV_eq {N : Matroid (Fin m)} {blk : Fin m → Fin k} {a : τ}
    (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) (r₀ : ℕ)
    (b : Fin k) : ((miV Fo blk r₀ a).2.2.1 && (miV Fo blk r₀ a).2.2.2 b) =
      (decide (nu N blk ≤ r₀) && decide (b ∈ Av N blk)) := by
  obtain ⟨-, -, -, -, h3, h4⟩ := miV_spec (blk := blk) hFo r₀
  rw [h3, h4]

/-- **The observer's circuit** on the input `x`, the context: `k` outputs. -/
def avGuardCircuit (bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (blk : Fin m → Fin k) (r₀ : ℕ) : Circuit BoolOp n :=
  vecCircuit (avGuardB bO blk r₀)

open Classical in
/-- **The observer's circuit**: `miCost m k cO r₀ + k` gates and `k` outputs; at every input `x`
at which `Fo(x, ·)` answers independence in a matroid `N`, output `b` is
`[ν(N) ≤ r₀] ∧ [b ∈ Av(N)]`. -/
theorem avGuardCircuit_spec {bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : (Fin n → Bool) × (Fin m → Bool) → Bool} (hO : Impl ((vecR n).prod (vecR m)) bitR bO cO Fo)
    (blk : Fin m → Fin k) (r₀ : ℕ) :
    (avGuardCircuit bO blk r₀).size = miCost m k cO r₀ + k ∧
      (avGuardCircuit bO blk r₀).outs.length = k ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)),
        (∀ A, Fo (x, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) →
        (avGuardCircuit bO blk r₀).eval boolInterp x =
          List.ofFn fun b => decide (nu N blk ≤ r₀) && decide (b ∈ Av N blk) := by
  obtain ⟨hs, hl, he⟩ := vecCircuit_spec (avGuardB_impl hO blk r₀)
  exact ⟨hs, hl, fun x N hFo => by
    unfold avGuardCircuit; rw [he x, funext (avGuardV_eq hFo r₀)]⟩

/-- `ν` alone, from the context: `k` rounds and a population count. -/
def nuB (bO : σ × (Fin m → Arg n) → Bld BoolOp n (Arg n)) (blk : Fin m → Fin k) :
    σ → Bld BoolOp n (List (Arg n)) :=
  seqB (roundsB bO blk) fun s => vecPopcountB s.2

/-- **`ν` alone** (for instance the rank of a transversal matroid): `k` rounds and a population
count, `k · roundCost m cO + popCost m` gates, on `⌈log₂(m+1)⌉` bits. -/
theorem nuB_impl (hO : Impl (Rc.prod (vecR m)) bitR bO cO Fo) (blk : Fin m → Fin k) :
    Impl Rc (numR (Nat.size m)) (nuB bO blk) (k * roundCost m cO + popCost m)
      fun a => (univ.filter fun i => stateV Fo blk a i = true).card :=
  (roundsB_impl hO blk).comp (vecPopcountB_impl.pre (R := Rc.prod (vecR m)) (g := Prod.snd)
    (G := Prod.snd) fun _ _ _ hs => hs.2)

open Classical in
/-- **The value of `ν` alone** at a context where the oracle answers independence in `N`. -/
theorem card_stateV {N : Matroid (Fin m)} {blk : Fin m → Fin k} {a : τ}
    (hFo : ∀ A, Fo (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) :
    (univ.filter fun i => stateV Fo blk a i = true).card = nu N blk := by
  rw [stateV_eq hFo, filter_indicator, (iterate_augStep N blk).2]

/-- **`ν` alone, as a circuit** on the input `x`, the context. -/
def nuCircuit (bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n))
    (blk : Fin m → Fin k) : Circuit BoolOp n :=
  circuitOf (nuB bO blk)

open Classical in
/-- **`ν` alone, as a circuit**: `k · roundCost m cO + popCost m` gates and `⌈log₂(m+1)⌉`
outputs; at every input `x` at which `Fo(x, ·)` answers independence in a matroid `N`, the
outputs are the binary digits of `ν(N)`. -/
theorem nuCircuit_spec {bO : (Fin n → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n)}
    {Fo : (Fin n → Bool) × (Fin m → Bool) → Bool} (hO : Impl ((vecR n).prod (vecR m)) bitR bO cO Fo)
    (blk : Fin m → Fin k) :
    (nuCircuit bO blk).size = k * roundCost m cO + popCost m ∧
      (nuCircuit bO blk).outs.length = Nat.size m ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)),
        (∀ A, Fo (x, A) = decide (N.Indep ↑(univ.filter fun i => A i = true))) →
        bitsVal ((nuCircuit bO blk).eval boolInterp x) = nu N blk := by
  obtain ⟨hs, hl, he⟩ := circuitOf_num (nuB_impl hO blk)
  exact ⟨hs, hl, fun x N hFo => (he x).trans (card_stateV hFo)⟩

end Circuit

/-! ### Independence oracles from rank queries and rank circuits -/

section RankOracle

variable {n m : ℕ}

/-! The independence oracle from a rank query (`indepOfRankV`, `indepOfRankB`,
`indepOfRankB_impl`, `indepOfRank_correct`) is in `BoolAlg/Count.lean`. -/

/-- The number output by a circuit `C` on the context bits followed by the set bits. -/
def rankQueryV {p : ℕ} (C : Circuit BoolOp (p + m)) (t : (Fin p → Bool) × (Fin m → Bool)) : ℕ :=
  bitsVal (C.eval boolInterp (Fin.append t.1 t.2))

/-- A rank query by a circuit `C` reading the context bits and the set bits. -/
def rankQueryB {p : ℕ} (C : Circuit BoolOp (p + m)) (s : (Fin p → Arg n) × (Fin m → Arg n)) :
    Bld BoolOp n (List (Arg n)) :=
  runB C (Fin.append s.1 s.2)

/-- **A rank query by a circuit** reading (context bits, set bits): `C.size` gates. -/
theorem rankQueryB_impl {p : ℕ} (C : Circuit BoolOp (p + m)) :
    Impl ((vecR p).prod (vecR m)) (numR (n := n) C.outs.length) (rankQueryB C) C.size
      (rankQueryV C) :=
  (runB_num C).pre (R := (vecR p).prod (vecR m)) (g := fun s => Fin.append s.1 s.2)
    (G := fun t => Fin.append t.1 t.2)
    fun _ _ _ hs i => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hs.1 i
      · simpa only [Fin.append_right] using hs.2 i

/-- The independence oracle from a rank circuit `C` reading (context bits, set bits). -/
def circuitOracleB {p : ℕ} (C : Circuit BoolOp (p + m)) :
    (Fin p → Arg n) × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  indepOfRankB (rankQueryB C)

/-- **The independence oracle from a rank circuit** of size `s = C.size`:
`s + popCost m + 5⌈log₂(m+1)⌉ + 1 ≤ s + 27m + 1` gates. -/
theorem circuitOracleB_impl {p : ℕ} (C : Circuit BoolOp (p + m)) :
    Impl ((vecR p).prod (vecR m)) (bitR (n := n)) (circuitOracleB C)
      (C.size + popCost m + (5 * Nat.size m + 1)) (indepOfRankV (rankQueryV C)) :=
  indepOfRankB_impl (rankQueryB_impl C)

open Classical in
/-- **The oracle from a rank circuit answers independence** at every context `a` at which
`C(a, ·)` outputs the rank of `N` (the rank hypothesis of Phase 1, read at `a`). -/
theorem circuitOracle_correct {p : ℕ} {C : Circuit BoolOp (p + m)} {N : Matroid (Fin m)}
    {a : Fin p → Bool}
    (hC : ∀ S : Finset (Fin m),
      (bitsVal (C.eval boolInterp (Fin.append a (indicator S))) : ℕ∞) = N.eRk (S : Set (Fin m)))
    (A : Fin m → Bool) :
    indepOfRankV (rankQueryV C) (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)) :=
  indepOfRank_correct (fun S => Nat.cast_injective ((hC S).trans (coe_rk N S).symm)) A

/-- **The matroid intersection circuit with a rank circuit**: the context is the input
`x : Fin n → Bool`, and independence in `N_x` is tested by the circuit `C` reading `(x, A)`. -/
def rankMICircuit {k : ℕ} (C : Circuit BoolOp (n + m)) (blk : Fin m → Fin k) (r₀ : ℕ) :
    Circuit BoolOp n :=
  miCircuit (circuitOracleB C) blk r₀

open Classical in
/-- **The matroid intersection circuit with a rank circuit** (`lem:augment`, with the rank
queries of `lem:observer`, Step 3, given as one circuit `C` of size `s` reading (input, set)): it has
`miCost m k (s + popCost m + 5⌈log₂(m+1)⌉ + 1) r₀ ≤ (k + 1)(m + 1)²(s + 37(m + 1)) +
5⌈log₂(r₀+1)⌉` gates and `m + ⌈log₂(m+1)⌉ + k + 1` outputs; at every input `x` at which `C(x, ·)`
outputs the rank of a matroid `N`, its outputs are the indicator vector of the rainbow
independent set `augStep^k(∅)` of size `ν(N)`, the binary digits of `ν(N)`, the guard
`[ν(N) ≤ r₀]` and the bits `[b ∈ Av(N)]`. -/
theorem rankMICircuit_spec {k : ℕ} (C : Circuit BoolOp (n + m)) (blk : Fin m → Fin k) (r₀ : ℕ) :
    (rankMICircuit C blk r₀).size = miCost m k (C.size + popCost m + (5 * Nat.size m + 1)) r₀ ∧
      (rankMICircuit C blk r₀).size ≤
        (k + 1) * (m + 1) ^ 2 * (C.size + 37 * (m + 1)) + 5 * Nat.size r₀ ∧
      (rankMICircuit C blk r₀).outs.length = m + Nat.size m + (k + 1) ∧
      ∀ (x : Fin n → Bool) (N : Matroid (Fin m)),
        (∀ S : Finset (Fin m), (bitsVal (C.eval boolInterp (Fin.append x (indicator S))) : ℕ∞) =
          N.eRk (S : Set (Fin m))) →
        (rankMICircuit C blk r₀).eval boolInterp x =
          List.ofFn (indicator ((augStep N blk)^[k] ∅)) ++
            (List.range (Nat.size m)).map (nu N blk).testBit ++
            decide (nu N blk ≤ r₀) :: List.ofFn fun b => decide (b ∈ Av N blk) := by
  obtain ⟨hs, hl, he⟩ := miCircuit_spec (circuitOracleB_impl (n := n) C) blk r₀
  exact ⟨hs, hs.trans_le ((Nat.le_add_right _ k).trans (miCost_rank_le _ _ _ _)), hl,
    fun x N hC => he x N (circuitOracle_correct hC)⟩

end RankOracle

end SignedTropical.Rainbow.MI
