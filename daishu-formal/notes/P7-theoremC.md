# P7: the circuits of Lemma `lem:oneupdate` and Theorem C

Natural-language companion of `SignedTropical/Rainbow/OneUpdate.lean` and
`SignedTropical/Rainbow/TheoremC.lean`, namespace `SignedTropical.Rainbow.TheoremC`.  Source:
`daishu/paper/greedy_intersection.tex`, Section 4.7: Lemma `lem:oneupdate` and its proof, the
proof of Theorem `thm:C` (Steps 1 to 4) and the statement of Theorem `thm:C`.  The observer of
Lemma `lem:observer` enters as a hypothesis (`IsObserver`); `TheoremCFinal.lean` plugs in the
observer circuits of `Observer.lean` (notes/P6c-observer.md).

Build status: `lake build` succeeds with no error and no warning.  No `sorry`, `admit`, `axiom`,
`native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.  The main theorems
(`oneUpdate`, `updCircuit_spec`, `updCircuit_eval`, `updV_eq_update`, `updCircuit_size_le`,
`theoremCCircuit_spec`, `schedV_eq`, `psiV_eq`, `theoremC`, `theoremC_bigO`,
`theoremC_bigO_rankOne`) depend only on `propext`, `Classical.choice` and `Quot.sound` (checked
with `#print axioms`).

Imports: `Rainbow/Events.lean` (the event levels and the query values; notes/P6d-events.md),
`Rainbow/GapUpdate.lean` (`update_eq_levSum`; notes/GapUpdate.md), `LevelCompiler.lean` (`levB`,
`levB_spec`, `levCost_le`, `levVal_eq`), `Compiler.lean` (`compileB`, `compileB_spec`,
`compVal_eq`, `compileCost_le`), `Rainbow/ObserverOracle.lean` (`rankB`), `Rainbow/Schedule.lean`
(`stageLength`, `schedule`, `le_nu_schedule`, `one_le_nu`, `psi_schedule`, `rounds_le`,
`sum_stageLength_mul_le`, `sum_range_mul_le`, `sum_range_id_le`), `Rainbow/Potential.lean`
(`stageMap`, `nu_le_nu_stageMap`), `BoolAlg/Impl.lean` (`Rep`, `Impl`, `tabB`, `runB_impl`,
`circuitOf_spec`, `denL_ofFn`, `ofFn_impl`), `TheoremA.lean` (`theoremACircuit`,
`theoremACircuit_spec`, `theoremACircuit_correct`), `Rainbow/MinBases.lean`
(`minBaseWeight_eq_neg_maxBasisWeight`).


## Notation

`E = Fin m`; `M` a matroid with ground set `E` (`hE : M.E = Set.univ`), rank `k`
(`hk : rank M = k`) and a rainbow base (`hM`); the blocks are the fibres of
`blk : E → Fin k`.  For `w ∈ ℝ^m` and `p ∈ ℝ^k`, `v = w - p_blk` (`shift blk w p`),
`ν₀ = ν(M^v)`, and `a = update (POSL.N M v) blk r` is the PO-SL update of stage `r`
(Definitions `def:posl`, `def:update`).  The stage map is `stageMap M blk w r p = p + a` (P5).
`t_x` (`tz`), `T_xy` (`bq`), `ρ_x` (`rho`), `U_xy` (`uq`) are the entry times, merge values,
values `ρ` and order values of `Rainbow/Events.lean`; `Λ = lev M v` are the `2m` levels
`t_x, ρ_x`, `Q = Qv M v` the `qn m = m + 2m²` query values `t_x, T_xy, U_xy`, and
`0 = s_0 ≤ s_1 ≤ ⋯ ≤ s_{2m}` the sorted levels.  `s = |C|` is the size of a Boolean circuit `C`
for the rank function, `W = ⌈log₂(m + 1)⌉` (`Nat.size m`), `L' = ⌈log₂(k + 1)⌉`.  A signed
tropical circuit on `m + k` inputs reads `(w, p)` as `Fin.append w p` (first `w`, then `p`).

Circuits are assembled with the representations of `BoolAlg/Impl.lean`: `realsR r` is a vector
of `r` reals carried by `r` operands, and `Impl R₁ R₂ b c F` says that the builder `b` appends
exactly `c` gates and its result carries `F` of the carried input.  All gate counts below are
exact unless written as bounds.


## 1. Results

### 1.1 Observers

**Definition 1.**  `IsObserver M blk r O`, for a Boolean circuit `O` on the `qn m` event bits:
for every `v ∈ ℝ^E` and every `t ≥ 0`, at the bits `[Q_j ≤ t]` the outputs of `O` are the `k`
bits `F_b(t) = [ν(N(t)) ≤ r] ∧ [b ∈ Av(N(t))]`, `b = 0, …, k - 1`, in this order.

This is the conclusion of Lemma `lem:observer` for `r₀ = r`.  `IsObserver.length_outs`: an
observer has `k` outputs (evaluate at `v = 0`, `t = 0`).

### 1.2 The one-update circuit

**Proposition 2 (the event values).**  `eventsB_impl`.  The builder `eventsB M C` computes from
`v` the vectors `(t_x)`, `(T_xy)`, `(ρ_x)`, `(U_xy)` with exactly
`evCost M C = Σ_x entryCost M C x + 5m(m - 1) + 4m³ + Σ_x 3(|lower x| - 1) + 6m²` gates
(the paper's Step 2).

*Proof.*  Step 1, the entry times (`entryB_impl`): `0` at a loop, no gate; at a nonloop `x`,
`D^x_g = max(v_x - v_g, 0)` (`dxB_impl`, `2m` gates) and the compiler of Theorem `thm:compiler`
(`compileB_impl`) with the Boolean circuit `closCircuit C x` of `[x ∈ cl(E - S)]`
(`closCircuit_spec`: the complement of `S`, two rank queries `rankB`, a comparison and a
negation, `closCost m s = m + 2s + 5W + 4` gates); by `compVal_eq` at `D^x ≥ 0` the compiled
value is the gap sum `C_{φ_x}(D^x) = t_x` (`entry_eq_compVal`).  Step 2, the weights (`wB_impl`):
`t_a` on the diagonal, `max(t_a, t_b, |v_a - v_b|)` with five gates for the other pairs,
`5m(m - 1)` gates; within components they are `W_ab` (`wV_eq_wgt`).  Step 3, the merge values
(`fwB_impl`): the Floyd–Warshall algorithm over `(min, max)`, four gates per entry and pivot,
`4m³` gates; its result is `T_xy` within components and `0` elsewhere (`fw_eq_bq`, by
`fwV_congr` and `fwV_of_not`).  Step 4, `ρ_x = min_{y ∈ lower x} T_xy` (`rhoB_impl`, `rho_eq`),
a chain of `min` gates of three gates each.  Step 5, the order values (`uB_impl`, `u_eq`): six
gates per pair, `6m²` gates.

**Proposition 3 (the circuit and what it computes).**  `updCircuit_spec`.  For every `blk` and
every Boolean circuit `O` on `qn m` inputs, the signed tropical circuit `updCircuit M C blk O` on
`m + k` inputs has exactly `m + evCost M C + levCost O (2m) + k` gates, and at every `w`, `p`
it outputs `p + updV M O v`, `v = w - p_blk`, where `updV M O v b` is entry `b` of
`levVal O Q Λ`, the compiler at the levels `Λ` with the query values `Q` (Corollary
`cor:levels`).

*Proof.*  Step 1, `v` (`shiftB_impl`): one subtraction `w_e - p_{blk(e)}` per element, `m`
gates.  Step 2, the event values (Proposition 2), and the query values and the levels read from
them at no cost (`qlev_impl`).  Step 4, the compiler at the `2m` levels (`levB_impl`, from
`levB_spec`), `levCost O (2m)` gates; entry `b` is read from the list of outputs at no cost.
Step 5, `p + a` (`addB_impl`): one addition per block, `k` gates; the results are read as a list
at no cost (`ofFn_impl`).  The composition (`updB_impl`) keeps `p` beside the computation of `a`
(`Impl.snd.pair`), and the counts add.  The circuit (`circuitOf_spec`) reads `w` from the first
`m` inputs and `p` from the last `k`.

**Proposition 4 (the compiled update is the update).**  `updV_eq_update`, `updCircuit_eval`.  Let
`r < k` and let `O` be an observer of stage `r`.  For every `v` with `ν(M^v) ≥ r`,
`updV M O v = a`, the PO-SL update of stage `r` at `v`; so `updCircuit M C blk O` outputs `p + a`
at every state with `ν₀ ≥ r`.

*Proof.*  Step 1, `O` has `k` outputs, so its output list at `X` is `(F'_b(X))_{b<k}`, `F'_b(X)`
the `b`-th output bit.  Step 2, the levels are nonnegative (`lev_nonneg`) and every query value is
a sorted level (`Qv_inLev`, `InLev.exists_sortedVal`), so by `levVal_eq`,
`updV M O v b = Σ_{i<2m} (s_{i+1} - s_i) F'_b([Q ≤ s_i])`.  Step 3, the observer gives
`F'_b([Q ≤ t]) = F_b(t)` at every `t ≥ 0`, and `GapUpdate.update_eq_levSum` (the paper's Step 3)
gives `a_b` as the same sum.

**Proposition 5 (the size).**  `entryCost_le`, `evCost_le`, `updOver`, `updOver_le`,
`updCircuit_size_le`.  An entry time costs at most `9m² + 6ms + 15mW + 15m` gates; the event values
cost at most `13m³ + 6m²s + 15m²W + 29m²`; and if `O` has `k` outputs,
`|updCircuit M C blk O| ≤ 6m|O| + updOver m k s`, with
`updOver m k s = 6m²s + 29m³ + 15m²W + 43m² + 3m + 2mk + k ≤ 93 m²(s + m)` for `1 ≤ m`, `k ≤ m`.

*Proof.*  Step 1, `compileCost_le` for `closCircuit C x` (`m` coordinates, one output) gives at
most `3m · closCost m s + m + 6m² = 9m² + 6ms + 15mW + 13m`, plus `2m` for `D^x`.  Step 2, `m`
entry times, `5m(m - 1) ≤ 5m²`, `4m³`, `Σ_x 3(|lower x| - 1) ≤ 3m²` and `6m²` add to the bound on
`evCost`.  Step 3, `levCost_le` with `L = 2m` levels, `q = m + 2m²` query values and `k` outputs:
`2 levCost O (2m) ≤ 12m² + 4m(1 + 4(m + 2m²) + 3|O| + k)`, that is
`levCost O (2m) ≤ 6m|O| + 16m³ + 14m² + 2m + 2mk`.  Step 4, Proposition 3 adds `m + k`.
Step 5, for `updOver_le`: `W ≤ m`, `m² ≤ m³`, `m ≤ m³` and `mk ≤ m³` bound `updOver m k s` by
`6m²s + 87m³ ≤ 93 m²(s + m)`.

**Theorem 6 (Lemma `lem:oneupdate`).**  `oneUpdate`.  Let `M` have ground set `E`, rank `k` and
a rainbow base, let `C` of size `s` output the binary digits of the rank, let `r < k`, and let
`O` be an observer of stage `r` with `s_O` gates.  There is a signed tropical circuit `U` on the
`m + k` inputs `(w, p)` with `|U| ≤ 6m s_O + updOver m k s` such that for all `w`, `p` with
`ν(M^v) ≥ r`, `v = w - p_blk`, `U` outputs `p + a`.  The circuit is `updCircuit M C blk O`.

*Proof.*  Propositions 4 and 5 with `IsObserver.length_outs`.

**Theorem 7 (Lemma `lem:oneupdate`, the order of the size).**  `roundSize_le` (in
`TheoremC.lean`).  If `s_O ≤ c (r + 2) m² (s + m)` (the order of Lemma `lem:observer`, whose
observer of stage `r` has `r + 1` rounds), then for `1 ≤ m` and `k ≤ m` the bound of Theorem 6
is at most `6c (r + 2) m³ (s + m) + 93 m² (s + m)`: the paper's `O(r m³ (s + m))`.

*Proof.*  `6m · c (r + 2) m² (s + m) = 6c (r + 2) m³ (s + m)`, and `updOver_le`.

### 1.3 The circuit of Theorem C

**Definition 8.**  For stage lengths `L : ℕ → ℕ`, circuits `U r : Circuit STOp (m + k)`
(`r ∈ ℕ`) and `CA : Circuit STOp m`, `theoremCCircuit L blk U CA` on the input `w`: start at
`p = 0` (the constant operands); for `r = 1, …, k - 1`, run `L r` rounds, a round running `U r`
on the operands `(w, p)` and reading the new `p` from its first `k` outputs (`roundB`); then
output `Σ_b p_b - CA(p_blk - w)` (`psiB`).  What a round computes is
`roundV U w p = (U(w, p)_b)_{b<k}`, the state after stages `1, …, j` is `schedV L U w j p`, with
`schedV L U w 0 p = p` and
`schedV L U w (j + 1) p = (roundV (U (j + 1)) w)^[L (j + 1)] (schedV L U w j p)`, and the output
part computes `psiV blk CA w p = Σ_b p_b - CA(p_blk - w)`.  The instances are
`L = stageLength k m` (`min(r(⌊m²/4⌋ + 1), 1 + (r - 1) k m, 1 + k (2m - k - 1))`, Theorems
`thm:potential` and `thm:stagelength`) and, when every component of `M` has rank at most one,
`L r = r` (Corollary `cor:rankone`).

**Proposition 9 (size and value).**  `theoremCCircuit_spec`.  `theoremCCircuit L blk U CA` has
exactly `schedCost L U (k - 1) + m + |CA| + k + 1` gates, where
`schedCost L U j = Σ_{r=1}^{j} L r · |U r|`, and at every `w` it outputs the single value
`psiV blk CA w (schedV L U w (k - 1) 0)`.

*Proof.*  Step 1, a round (`roundB_impl`): the operands `(w, p)` are the `m + k` inputs of `U`
(`Fin.append`, by cases on the index, `Fin.addCases`); running `U` costs `|U|` gates and its
outputs carry `U(w, p)` (`runB_impl`); entry `b` is read at no cost.  Step 2, a stage: rounds
with the fixed context `w` (`Impl.iterateCtx`), `L r · |U r|` gates.  Step 3, stages
`1, …, j` (`schedB_impl`, induction on `j`): the counts add to `schedCost L U j`.  Step 4, the
output (`psiB_impl`): `m` subtractions `p_{blk(e)} - w_e`, `|CA|` gates (`runB_impl`), the sum
of the `p_b` with `k` additions (`sumB_spec`, induction on the list), one subtraction.  Step 5,
the circuit (`circuitOf_spec`): the constants for `p = 0` cost nothing; Steps 3 and 4 in
sequence.

**Proposition 10 (the rounds follow the schedule).**  `schedV_eq`.  Let `M` have ground set `E`,
rank `k` and a rainbow base, `L` valid stage lengths (`Schedule.ValidLength`), and `w ∈ ℝ^m`.
Suppose that for every `r ∈ {1, …, k - 1}` and every `p` with `ν(M^{w - p_blk}) ≥ r`,
`roundV (U r) w p = stageMap M blk w r p`.  Then for every `j ≤ k - 1`,
`schedV L U w j 0 = schedule L M blk w j 0`.

*Proof.*  Induction on `j`; for `j = 0` both are `0`.  Step 1, for `j + 1 ≤ k - 1`, so
`j + 1 < k`, the induction hypothesis gives the state `q = schedule M blk w j 0` after `j`
stages, and `ν₀(q) ≥ j + 1` (`le_nu_schedule` for valid `L`, with `ν₀(0) ≥ 1` from `one_le_nu`
as `k ≥ 1`).  Step 2, the set `{q : ν₀(q) ≥ j + 1}` is invariant under the stage map of stage
`j + 1`, since `ν₀` does not decrease (`nu_le_nu_stageMap`, Theorem `thm:validity`(2)), and on it
the round equals the stage map (hypothesis).  Step 3, so their `L (j + 1)`-th iterates agree at
`q` (`iterate_eq_iterate`, induction on the number of iterations).

**Proposition 11 (the output is the Lagrangian).**  `psiV_eq`.  If `CA(u) = [h_M(u)]` for every
`u`, then `psiV blk CA w p = Ψ(p) = Σ_b p_b + β_M(v)`.

*Proof.*  `p_blk - w = -v`, and `β_M(v) = -h_M(-v)` (`minBaseWeight_eq_neg_maxBasisWeight`).

**Proposition 12 (the schedule's gates).**  `schedCost_le`, `sum_range_sub_one`.  If
`|U r| ≤ S r` for every `r ∈ {1, …, k - 1}`, then
`schedCost L U (k - 1) ≤ Σ_{r ≤ k-1} L r · S r`, and the sum over `r ≤ k - 1` is the sum over
`r < k` when its term at `0` vanishes (`L 0 = 0`).  For `L = stageLength k m`,
`Σ_r L r = rounds k m` is at most `(⌊m²/4⌋ + 1) · k(k - 1)/2` (`Schedule.rounds_le_potential`)
and at most `2 k² m` for `k ≤ m` (`Schedule.rounds_le`), and
`40 Σ_r L r (r + 2) ≤ 49 k³ m` (`Schedule.sum_stageLength_mul_le`); for `L r = r`,
`Σ_r r ≤ k²` (`Schedule.sum_range_id_le`) and `2 Σ_r r (r + 2) ≤ k³`
(`Schedule.sum_range_mul_le`).

*Proof.*  Induction on `j ≤ k - 1` (`Finset.sum_range_succ`); for `k ≥ 1` the sum over
`r ≤ k - 1` is the sum over `r < k`, and for `k = 0` both are the term at `0`.

**Theorem 13 (Theorem `thm:C`, with observers).**  `theoremC_of_validLength`, and its instances
`theoremC` (`L = stageLength k m`) and `theoremC_rankOne` (`L r = r`, every component of rank at
most one).  Let `M` be a matroid on `E = Fin m` with ground set `E`, rank `k` and a rainbow base,
its elements partitioned into the `k` blocks `blk`.  Let `B` be a Boolean circuit of size `s`
that outputs the binary digits of `r(S)`, least significant first, from the indicator vector of
`S`, for every `S ⊆ E`.  Let `O_r` (`r ∈ ℕ`) be Boolean circuits on the `qn m` event bits such
that for every `r ∈ {1, …, k - 1}`, `O_r` is an observer of stage `r` with at most `s_O(r)`
gates.  Then a signed tropical circuit `C` on `m` inputs with
`|C| ≤ Σ_{r<k} L r · (6m s_O(r) + updOver m k s) + 3ms + mL' + 9m² + 5m + 4L' + k + 2`,
for valid stage lengths `L` with `L 0 = 0`, has the single output `Opt(w)` at every `w ∈ ℝ^E`.

*Proof.*  Step 1, the circuit is `theoremCCircuit L blk U CA` with `U r = updCircuit M B blk O_r`
(Lemma `lem:oneupdate`) and `CA` the circuit of Theorem A (`theoremACircuit B (rank M)`, with
`rank M = k`).  Step 2, the size: every `U r`, `r ∈ {1, …, k - 1}`, has at most
`6m s_O(r) + updOver m k s` gates (Proposition 5); Proposition 12 bounds the schedule; `CA` has
at most `3ms + mL' + 9m² + 4m + 4L' + 1` gates (`theoremACircuit_spec`); Proposition 9 adds
`m + k + 1`.  Step 3, the value: by Proposition 9 the output is
`psiV blk CA w (schedV L U w (k - 1) 0)`.  A round with `U r` is the stage map at every state
with `ν₀ ≥ r` (`roundV_updCircuit`, from Proposition 4), so the state is
`schedule L M blk w (k - 1) 0` (Proposition 10).  The output is `Ψ` of that state
(Proposition 11 with `theoremACircuit_correct`), which is `Opt(w)` (`psi_schedule`: `ν₀ = k`
after the schedule, and Lemma `lem:duality`).

**Theorem 14 (Theorem `thm:C`, order of the size).**  `outSize_le`, `roundSize_le`,
`theoremC_bigO`, `theoremC_bigO_rankOne`.  Under the hypotheses of Theorem 13 with observers of
stage `r` of size at most `c (r + 2) m² (s + m)` (the order of Lemma `lem:observer`), a signed
tropical circuit `C` with `40 |C| ≤ (294c + 8440) k³ m⁴ (s + m) + 80` has the single output
`Opt(w)` at every `w ∈ ℝ^E`: the paper's `O(k³ m⁴ (s + m))`.  When every component of `M` has
rank at most one, `2 |C| ≤ (6c + 236) k³ m³ (s + m) + 4`.

*Proof.*  Step 1, if `k = 0`, then `m = 0` (an element lies in a block), every sum is empty, and
`|C| ≤ 2`.  Step 2, for `k ≥ 1`, `m ≥ k ≥ 1`, and a round of stage `r` has at most
`6c (r + 2) m³ (s + m) + 93 m² (s + m)` gates (Theorem 7), so the schedule has at most
`6c m³ (s + m) Σ_r L r (r + 2) + 93 m² (s + m) Σ_r L r` gates.  Step 3, with
`40 Σ_r L r (r + 2) ≤ 49 k³ m` and `Σ_r L r ≤ 2 k² m`, forty times this is at most
`294c k³ m⁴ (s + m) + 7440 k² m³ (s + m)`.  Step 4, the output part
`3ms + mL' + 9m² + 5m + 4L' + k + 2` is at most `25 k³ m⁴ (s + m)` (`outSize_le`, `L' ≤ k`), and
`7440 + 40 · 25 = 8440`.  Step 5, for `L r = r`: `2 Σ_r r (r + 2) ≤ k³` and `Σ_r r ≤ k²`, so twice
the schedule is at most `6c k³ m³ (s + m) + 186 k² m² (s + m)`, the output part is at most
`25 k³ m³ (s + m)`, and `186 + 2 · 25 = 236`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer`, the conclusion, as a hypothesis | `IsObserver`, `IsObserver.length_outs` | `OneUpdate` | definition |
| `lem:oneupdate`, Step 1 (`v`) | `shiftB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 2 (entry times by the compiler) | `dxB_impl`, `closCircuit_spec`, `compileB_impl`, `entry_eq_compVal`, `entryB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 2 (`W`, Floyd–Warshall, `σ`, `ω`) | `wB_impl`, `wV_eq_wgt`, `fwB_impl`, `fw_eq_bq`, `rhoB_impl`, `rho_eq`, `uB_impl`, `u_eq`, `eventsB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 3 (the update as a sum over the levels) | `GapUpdate.update_eq_levSum`, `updV_eq_update` | `GapUpdate`, `OneUpdate` | proved |
| `lem:oneupdate`, Step 4 (the compiler at the levels) | `levB_impl`, `qlev_impl` (with `levVal_eq`) | `OneUpdate` | proved |
| `lem:oneupdate`, Step 5 (`p + a`) | `addB_impl`, `updB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, the circuit and its size | `updCircuit`, `updCircuit_spec`, `updCircuit_eval`, `entryCost_le`, `evCost_le`, `updOver_le`, `updCircuit_size_le` | `OneUpdate` | proved |
| `lem:oneupdate` | `oneUpdate`, `roundSize_le` | `OneUpdate`, `TheoremC` | proved (observer as hypothesis) |
| `thm:C`, Step 1 (the schedule as a circuit) | `roundB_impl`, `schedB_impl`, `schedCost` | `TheoremC` | proved |
| `thm:C`, Step 2 (the circuit follows the schedule) | `roundV_updCircuit`, `schedV_eq`, `iterate_eq_iterate` | `TheoremC` | proved |
| `thm:C`, Step 3 (output `Σ_b p_b - h_M(-v)` by Theorem A) | `psiB_impl`, `sumB_spec`, `psiV_eq` | `TheoremC` | proved |
| `thm:C`, Step 4 (size) | `schedCost_le`, `sum_range_sub_one`, `outSize_le`, `theoremC_bigO` (with `Schedule.sum_stageLength_mul_le`, `Schedule.rounds_le`) | `TheoremC` | proved |
| `thm:C` | `theoremCCircuit`, `theoremCCircuit_spec`, `theoremC_of_validLength`, `theoremC`, `theoremC_bigO` | `TheoremC` | proved (observers as hypotheses) |
| `cor:rankone` in Theorem C | `theoremC_rankOne`, `theoremC_bigO_rankOne` | `TheoremC` | proved (observers as hypotheses) |
| `thm:C`, uniformity | none | | not formalized |


## 3. Differences from the paper

1. **Observers as hypotheses.**  Lemma `lem:observer` enters here as the hypothesis
   `IsObserver M blk r (O r)` with `|O r| ≤ s_O(r)` for `r ∈ {1, …, k - 1}`; `TheoremCFinal.lean`
   supplies the observers of `Observer.lean`.
2. **Pairs that are not joined.**  The weights, merge values and order values of pairs that are
   not joined are the constant `0` (`wB`, `fwB`, `uB` keep only the pairs `Kr M a b`), the
   convention of Lemma `lem:observer`.  The paper's counts `5m²`, `4m³` and `6m²` bound the
   gates of all pairs.
3. **The domain of Lemma `lem:oneupdate`.**  The circuit computes `p + a` at every state of
   stage `r`, that is with `ν₀ ≥ r`, which covers both cases of Definition `def:update`
   (`ν₀ = r`, and `ν₀ > r` with `a = 0`); for `ν₀ < r` the update of stage `r` is not defined.
   The paper states this domain.
4. **Explicit sizes.**  Lemma `lem:oneupdate`: `6m s_O + updOver m k s` gates, at most
   `6c (r + 2) m³ (s + m) + 93 m² (s + m)` for `s_O ≤ c (r + 2) m² (s + m)`.  Theorem C: the
   polynomial of Theorem 13, and Theorem 14.  The additive constant covers `k = 0`, where `m = 0`
   and the circuit still has its final gates.  The output of Step 3 costs
   `3ms + mL' + 9m² + 5m + 4L' + k + 2` gates: Theorem A at `-v` and `m + k + 1` gates for
   `-v = p_blk - w`, `Σ_b p_b` and the subtraction, the paper's `O(ms + m²)`.
5. **Uniformity** is not formalized, as in Phase 1: the circuit is an explicit Lean definition,
   `theoremCCircuit L blk (fun r => updCircuit M B blk (O r)) (theoremACircuit B (rank M))`,
   built from the blocks, the rank circuit and the observers, but no statement about the time to
   produce it is made.
6. **The identity updates.**  The paper's Step 1 notes that an update at a state with
   `ν₀ > r` is the identity.  The circuit needs no separate argument for these states: Lemma
   `lem:oneupdate` covers every state with `ν₀ ≥ r`, and the stage map it computes is the
   identity there (`Potential.stageMap_eq_self`).


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/OneUpdate.lean` | 845 |
| `SignedTropical/Rainbow/TheoremC.lean` | 508 |
