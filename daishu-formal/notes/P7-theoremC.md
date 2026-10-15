# P7: the circuits of Lemma `lem:oneupdate` and Theorem C

Natural-language companion of `SignedTropical/Rainbow/OneUpdate.lean` and
`SignedTropical/Rainbow/TheoremC.lean`, namespace `SignedTropical.Rainbow.TheoremC`.  Source:
`daishu/paper/greedy_intersection.tex`, Section 4.7: Lemma `lem:oneupdate` and its proof, the
proof of Theorem `thm:C` (Steps 1 to 4) and the statement of Theorem `thm:C`.  The observer of
Lemma `lem:observer` enters as a hypothesis (`IsObserver`); `TheoremCFinal.lean` plugs in the
observer circuits of `Observer.lean` (notes/P6c-observer.md).

Build status: `lake build SignedTropical.Rainbow.OneUpdate` and
`lake build SignedTropical.Rainbow.TheoremC` succeed with no error and no warning.  No `sorry`,
`admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.  The main
theorems (`oneUpdate`, `oneUpdate_bigO`, `updCircuit_spec`, `updCircuit_eval`,
`updCircuit_size_le`, `gapV_eq_update`, `theoremCCircuit_spec`, `schedV_eq`, `psiV_eq`,
`theoremC`, `theoremC_bigO`, `theoremC_bigO_rankOne`) depend only on `propext`,
`Classical.choice` and `Quot.sound` (checked with `#print axioms`).

Imports: `Rainbow/GapUpdate.lean` (`pairOf`, `Dplus`, `relOf`, `obs`,
`relOf_sublevel`, `gapSum_congr_sublevel`, `update_eq_gapSum`), `Rainbow/Schedule.lean`
(`stageLength`, `schedule`, `stage_bound`, `one_le_nu`, `le_nu_schedule`, `psi_schedule`,
`rounds`, `rounds_le_potential`, `rounds_le`, `sum_stageLength_mul_le`, `sum_range_mul_le`),
`Rainbow/Potential.lean` (`stageMap`, `nu_le_nu_stageMap`), `BoolAlg/Impl.lean` (`Rep`, `Impl`,
`tabB`, `iterCtxB`, `runB_impl`, `circuitOf_spec`, `denL_ofFn`, `ofFn_impl`), `Compiler.lean`
(`compileB`, `compileB_spec`, `compVal_eq`, `compileCost_le`), `TheoremA.lean`
(`theoremACircuit`, `theoremACircuit_spec`, `theoremACircuit_correct`), `Rainbow/MinBases.lean`
(`minBaseWeight_eq_neg_maxBasisWeight`).


## Notation

`E = Fin m`; `M` a matroid with ground set `E` (`hE : M.E = Set.univ`), rank `k`
(`hk : rank M = k`) and a rainbow base (`hM`); the blocks are the fibres of
`blk : E → Fin k`.  For `w ∈ ℝ^m` and `p ∈ ℝ^k`, `v = w - p_blk` (`shift blk w p`),
`ν₀ = ν(M^v)`, and `a = update (POSL.N M v) blk r` is the PO-SL update of stage `r`
(Definitions `def:posl`, `def:update`).  The stage map is
`stageMap M blk w r p = p + a` (P5).  The `m²` ordered pairs `(e, f)` are indexed by
`Fin (m * m)` through `pairOf = finProdFinEquiv.symm`; `D⁺_{ef} = max(v_f - v_e, 0)`
(`Dplus v`), `G_t = {(e, f) : v_f - v_e ≤ t}` (`POSL.Gt v t`), `N_G` the matroid of a relation
(`POSL.NG M G`), `C_F(D)` the gap sum (`gapSum`).  `s = |B|` is the size of a Boolean circuit
`B` for the rank function, `L = ⌈log₂(k + 1)⌉` (`Nat.size k`).  A signed tropical circuit on
`m + k` inputs reads `(w, p)` as `Fin.append w p` (first `w`, then `p`).

Circuits are assembled with the representations of `BoolAlg/Impl.lean`: `realsR r` is a vector
of `r` reals carried by `r` operands, and `Impl R₁ R₂ b c F` says that the builder `b` appends
exactly `c` gates and its result carries `F` of the carried input.  All gate counts below are
exact unless written as bounds.


## 1. Results

### 1.1 Observers

**Definition 1.**  `IsObserver M blk r O`, for a Boolean circuit `O` on `m·m` inputs: for every
`v ∈ ℝ^E` and every `t ≥ 0`, on the input vector of `G_t` (input `i` is the bit
`[pairOf i ∈ G_t]`), the outputs of `O` are the `k` bits
`F_b(G_t) = [ν(N_{G_t}) ≤ r] ∧ [b ∈ Av(N_{G_t})]`, `b = 0, …, k - 1`, in this order.

This is the conclusion of Lemma `lem:observer` for `r₀ = r`: the outputs are required only at
the relations `G = G_t`.  `IsObserver.length_outs`: an observer has `k` outputs (evaluate at
`v = 0`, `t = 0`).

### 1.2 The one-update circuit

**Proposition 2 (the circuit and what it computes).**  `updCircuit_spec`.  For every `blk` and
every Boolean circuit `O` on `m·m` inputs, the signed tropical circuit `updCircuit blk O` on
`m + k` inputs has exactly `m + 2m² + compileCost O + k` gates, and at every `w ∈ ℝ^m`,
`p ∈ ℝ^k` it outputs the `k` values `p_b + gapV O v b`, `v = w - p_blk`, where `gapV O v b` is
entry `b` of the compiled values `compVal O (D⁺(v))` of Theorem `thm:compiler`.

*Proof.*  Step 1, `v` (`shiftB_impl`): one subtraction `w_e - p_{blk(e)}` per element, `m`
gates.  Step 2, `D⁺` (`dplusB_impl`): for each pair index `i`, `pairOf i = (e, f)`, the gates
`v_f - v_e` and `max(·, 0)`, `2m²` gates.  Step 3, the compiler (`compileB_impl`): `compileB O`
on the `m²` operands of `D⁺` appends `compileCost O` gates and its outputs carry
`compVal O (D⁺)` (`compileB_spec`); entry `b` is read from the list of outputs at no cost.
Step 4, `p + a` (`addB_impl`): one addition per block, `k` gates; the results are read as a list
at no cost (`ofFn_impl`).  Step 5, composition (`updB_impl`): `p` is kept beside the
computation of `a` (`Impl.snd.pair`), and the counts add.  Step 6, the circuit
(`circuitOf_spec`): `w` is read from the first `m` inputs and `p` from the last `k`; at
`Fin.append w p` these are `w` and `p` (`Fin.append_left`, `Fin.append_right`).

**Proposition 3 (the observed gap sums are the update).**  `gapV_eq_update`.  Let `r < k` and
let `O` be an observer of stage `r`.  For every `v` with `ν(M^v) ≥ r` and every block `b`,
`gapV O v b = a_b`, the PO-SL update of stage `r` at `v`.

*Proof.*  Step 1, `O` has `k` outputs, so at the indicator vector of every `S ⊆ Fin (m·m)` its
output list is `(F'_b(S))_{b<k}`, `F'_b(S)` the `b`-th output bit.  Step 2, by the value of the
compiled circuit on `D⁺ ≥ 0` (`compVal_eq`), `gapV O v b = C_{F'_b}(D⁺)`, `F'_b` read as `0` or
`1`.  Step 3, by `update_eq_gapSum` (Lemma `lem:oneupdate`, Step 2, using `r ≤ ν₀` and `r < k`),
`a_b = C_{obs_b}(D⁺)`, where `obs_b(S) = F_b(relOf S)`.  Step 4, by `gapSum_congr_sublevel` it
suffices that `F'_b` and `obs_b` agree on every sublevel set `S_t = {D⁺ ≤ t}`, `t ≥ 0`.  For
`t ≥ 0`, `D⁺_{ef} ≤ t` iff `v_f - v_e ≤ t`, so the indicator vector of `S_t` is the input vector
of `G_t` (`indicator_sublevel`), at which the observer outputs `F_b(G_t)`; and
`relOf S_t = G_t` (`relOf_sublevel`), so `obs_b(S_t) = [F_b(G_t)]` as well.

**Proposition 4 (the size).**  `updCircuit_size_le`.  If `O` has `k` outputs, then
`|updCircuit blk O| ≤ 3m²|O| + km² + 6m⁴ + 2m² + m + k`.

*Proof.*  `compileCost O ≤ 3(m·m)|O| + (m·m)k + 6(m·m)²` (`compileCost_le`, Theorem
`thm:compiler` on `m²` coordinates with `k` outputs), and Proposition 2.

**Theorem 5 (Lemma `lem:oneupdate`).**  `oneUpdate`.  Let `M` have ground set `E`, rank `k` and
a rainbow base, let `r < k`, and let `O` be an observer of stage `r` with `s_O` gates.  There is
a signed tropical circuit `U` on the `m + k` inputs `(w, p)` with
`|U| ≤ 3m²s_O + km² + 6m⁴ + 2m² + m + k` such that for all `w`, `p` with `ν(M^v) ≥ r`,
`v = w - p_blk`, `U` outputs `p + a`, `a` the PO-SL update of stage `r` at `v`.  The circuit is
`updCircuit blk O` (`updCircuit_eval`: its output at such states is `p + a`).

*Proof.*  Step 1, the size: Proposition 4 with `IsObserver.length_outs`.  Step 2, the value:
Proposition 2, and Proposition 3 for each block.

**Theorem 6 (Lemma `lem:oneupdate`, order of the size).**  `updSize_le`, `oneUpdate_bigO`.
Under the hypotheses of Theorem 5, if `s_O ≤ c (r + 2) m² (s + m)` (the order of Lemma
`lem:observer`, whose observer of stage `r` has `r + 1` rounds), the bound of Theorem 5 is at
most `3c (r + 2) m⁴ (s + m) + 11 m⁴` (`updSize_le`, for `k ≤ m`), and the circuit has at most
`(3c + 11)(r + 2) m⁴ (s + m)` gates.

*Proof.*  Step 1, `m ≥ k ≥ 1` (`rank_le_card`, `r < k`).  Step 2, `3m² s_O ≤ 3c (r + 2) m⁴ (s + m)`,
and `km² ≤ m⁴`, `6m⁴`, `2m² ≤ 2m⁴`, `m ≤ m⁴`, `k ≤ m⁴` add to at most `11 m⁴ ≤
11 (r + 2) m⁴ (s + m)`.

### 1.3 The circuit of Theorem C

**Definition 7.**  For stage lengths `L : ℕ → ℕ`, circuits `U r : Circuit STOp (m + k)`
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

**Proposition 8 (size and value).**  `theoremCCircuit_spec`.  `theoremCCircuit L blk U CA` has
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

**Proposition 9 (the rounds follow the schedule).**  `schedV_eq`.  Let `M` have ground set `E`,
rank `k` and a rainbow base, `L` valid stage lengths (`Schedule.ValidLength`), and `w ∈ ℝ^m`.
Suppose that for every `r ∈ {1, …, k - 1}` and every `p` with `ν(M^{w - p_blk}) ≥ r`,
`roundV (U r) w p = stageMap M blk w r p`.  Then for every `j ≤ k - 1`,
`schedV L U w j 0 = schedule L M blk w j 0`.

*Proof.*  Induction on `j`; for `j = 0` both are `0`.  Step 1, for `j + 1 ≤ k - 1`, so
`j + 1 < k`, the induction hypothesis gives the state `q = schedule M blk w j 0` after `j`
stages, and `ν₀(q) ≥ j + 1` (`le_nu_schedule` for valid `L`, with `ν₀(0) ≥ 1` from `one_le_nu`
as `k ≥ 1`).
Step 2, the set `{q : ν₀(q) ≥ j + 1}` is invariant under the stage map of stage `j + 1`, since
`ν₀` does not decrease (`nu_le_nu_stageMap`, Theorem `thm:validity`(2)), and on it the round
equals the stage map (hypothesis).  Step 3, so their `L (j + 1)`-th iterates agree
at `q` (`iterate_eq_iterate`, induction on the number of iterations).

**Proposition 10 (the output is the Lagrangian).**  `psiV_eq`.  If `CA(u) = [h_M(u)]` for every
`u`, then `psiV blk CA w p = Ψ(p) = Σ_b p_b + β_M(v)`.

*Proof.*  `p_blk - w = -v`, and `β_M(v) = -h_M(-v)` (`minBaseWeight_eq_neg_maxBasisWeight`).

**Proposition 11 (the schedule's gates).**  `schedCost_le`, `sum_range_sub_one`.  If
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

**Theorem 12 (Theorem `thm:C`, with observers).**  `theoremC_of_validLength`, and its instances
`theoremC` (`L = stageLength k m`) and `theoremC_rankOne` (`L r = r`, every circuit with at most
two elements).  Let `M` be a matroid on
`E = Fin m` with ground set `E`, rank `k` and a rainbow base, its elements partitioned into the
`k` blocks `blk`.  Let `B` be a Boolean circuit of size `s` that outputs the binary digits of
`r(S)`, least significant first, from the indicator vector of `S`, for every `S ⊆ E`.  Let
`O_r` (`r ∈ ℕ`) be Boolean circuits on `m·m` inputs such that for every `r ∈ {1, …, k - 1}`,
`O_r` is an observer of stage `r` with at most `s_O(r)` gates.  Then a signed tropical
circuit `C` on `m` inputs with
`|C| ≤ Σ_{r<k} L r · (3m²s_O(r) + km² + 6m⁴ + 2m² + m + k) + 3ms + mL' + 9m² + 5m + 4L' + k + 2`,
for valid stage lengths `L` with `L 0 = 0` (`stageLength k m` in general, `L r = r` for
components of rank one), `L' = ⌈log₂(k + 1)⌉`, has the single output `Opt(w)` at every
`w ∈ ℝ^E`.

*Proof.*  Step 1, the circuit is `theoremCCircuit L blk U CA` with `U r = updCircuit blk O_r`
(Lemma `lem:oneupdate`) and `CA` the circuit of Theorem A (`theoremACircuit B (rank M)`, with
`rank M = k`).  Step 2,
the size: every `U r`, `r ∈ {1, …, k - 1}`, has at most `3m²s_O(r) + km² + 6m⁴ + 2m² + m + k`
gates (Proposition 4); Proposition 11 bounds the schedule; `CA` has at most
`3ms + mL' + 9m² + 4m + 4L' + 1` gates (`theoremACircuit_spec`); Proposition 8 adds `m + k + 1`.
Step 3, the value: by Proposition 8 the output is `psiV blk CA w (schedV L U w (k - 1) 0)`.  A
round with `U r` is the stage map at every state with `ν₀ ≥ r` (`roundV_updCircuit`, from
Theorem 5), so the state is `schedule L M blk w (k - 1) 0` (Proposition 9).  The output is
`Ψ` of that state (Proposition 10 with `theoremACircuit_correct`), which is `Opt(w)`
(`psi_schedule`: `ν₀ = k` after the schedule, and Lemma `lem:duality`).

**Theorem 13 (Theorem `thm:C`, order of the size).**  `outSize_le`, `theoremC_bigO`,
`theoremC_bigO_rankOne`.  Under the hypotheses of Theorem 12 with observers of stage `r` of size
at most `c (r + 2) m² (s + m)` (the order of Lemma `lem:observer`), a signed tropical circuit `C`
with `40 |C| ≤ (147c + 1880) k³ m⁵ (s + m) + 80` has the single output `Opt(w)` at every
`w ∈ ℝ^E`: the paper's `O(k³ m⁵ (s + m))`.  When every component of `M` has rank at most one,
`2 |C| ≤ (3c + 72) k³ m⁴ (s + m) + 4`.

*Proof.*  Step 1, if `k = 0`, then `m = 0` (an element lies in a block), every sum is empty, and
`|C| ≤ 2`.  Step 2, for `k ≥ 1`, `m ≥ k ≥ 1`, and a round of stage `r` has at most
`3c (r + 2) m⁴ (s + m) + 11 m⁴` gates (`updSize_le`), so the schedule has at most
`3c m⁴ (s + m) Σ_r L r (r + 2) + 11 m⁴ Σ_r L r` gates.  Step 3, with
`40 Σ_r L r (r + 2) ≤ 49 k³ m` and `Σ_r L r ≤ 2 k² m`, forty times this is at most
`147c k³ m⁵ (s + m) + 880 k² m⁵`.  Step 4, the output part
`3ms + mL' + 9m² + 5m + 4L' + k + 2` is at most `25 k³ m⁵ (s + m)` (`outSize_le`, `L' ≤ k`), and
`880 + 40 · 25 = 1880`.  Step 5, for `L r = r`: `2 Σ_r r (r + 2) ≤ k³` and `Σ_r r ≤ k²`, so twice
the schedule is at most `3c k³ m⁴ (s + m) + 22 k² m⁴`, and `22 + 2 · 25 = 72`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer`, the conclusion, as a hypothesis | `IsObserver`, `IsObserver.length_outs` | `OneUpdate` | definition |
| `lem:oneupdate`, Step 1 (`v`, `D⁺`) | `shiftB_impl`, `dplusB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 2 (compiler on the pairs, `a_b = C_{F_b}(D⁺)`) | `compileB_impl`, `gapV_eq_update`, `indicator_sublevel` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 3 (`p + a`) | `addB_impl`, `updB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, the circuit and its size | `updCircuit`, `updCircuit_spec`, `updCircuit_size_le`, `updCircuit_eval` | `OneUpdate` | proved |
| `lem:oneupdate` | `oneUpdate`, `updSize_le`, `oneUpdate_bigO` | `OneUpdate` | proved (observer as hypothesis) |
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
2. **`D⁺` over all `m²` ordered pairs.**  The paper forms `D⁺` over the `m(m - 1)` pairs
   `e ≠ f` (`2m(m - 1)` gates), whose sublevel set at `t ≥ 0` is `G_t` without the diagonal.
   Here `D⁺` is formed over all `m²` pairs (`2m²` gates); the diagonal entries are `0`, and the
   sublevel set at `t ≥ 0` is `G_t` itself, which is what the observer reads.  The compiler then
   runs on `m²` coordinates, the count the paper uses in its bound.  The size grows by `2m`
   gates; the order is unchanged.  No change to the paper is needed; optional wording for
   Step 1: "$v$ costs $m$ gates and the vector $D^{+}_{ef}=\max(v_f-v_e,0)$ over all $m^{2}$
   ordered pairs costs $2m^{2}$; its sublevel set at level $t\ge0$ is $G_t$."
3. **The domain of Lemma `lem:oneupdate`.**  The circuit computes `p + a` at every state of
   stage `r`, that is with `ν₀ ≥ r`, which covers both cases of Definition `def:update`
   (`ν₀ = r`, and `ν₀ > r` with `a = 0`); for `ν₀ < r` the update of stage `r` is not defined.
   The paper states this domain.
4. **Explicit sizes.**  Lemma `lem:oneupdate`: `3m²s_O + km² + 6m⁴ + 2m² + m + k` gates, and
   `(3c + 11)(r + 2) m⁴ (s + m)` for `s_O ≤ c (r + 2) m² (s + m)`.  Theorem C: the polynomial of
   Theorem 12, and Theorem 13.  The additive constant covers `k = 0`, where `m = 0` and the
   circuit still has its final gates.  The output of
   Step 3 costs `3ms + mL + 9m² + 5m + 4L + k + 2` gates: Theorem A at `-v` and `m + k + 1`
   gates for `-v = p_blk - w`, `Σ_b p_b` and the subtraction, the paper's `O(ms + m²)`.  No
   change to the paper.
5. **Uniformity** is not formalized, as in Phase 1: the circuit is an explicit Lean definition,
   `theoremCCircuit L blk (fun r => updCircuit blk (O r)) (theoremACircuit B (rank M))`, built from the
   blocks, the rank circuit and the observers, but no statement about the time to produce it is
   made.
6. **The identity updates.**  The paper's Step 1 notes that an update at a state with
   `ν₀ > r` is the identity.  The circuit needs no separate argument for these states: Lemma
   `lem:oneupdate` covers every state with `ν₀ ≥ r`, and the stage map it computes is the
   identity there (`Potential.stageMap_eq_self`).  No change.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/OneUpdate.lean` | 274 |
| `SignedTropical/Rainbow/TheoremC.lean` | 488 |
