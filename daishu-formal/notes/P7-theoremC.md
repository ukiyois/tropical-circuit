# P7: the circuits of Lemma `lem:oneupdate` and Theorem C

Natural-language companion of `SignedTropical/Rainbow/OneUpdate.lean` and
`SignedTropical/Rainbow/TheoremC.lean`, namespace `SignedTropical.Rainbow.TheoremC`.  Source:
`daishu/paper/greedy_intersection.tex`, Section 4.7: Lemma `lem:oneupdate` and its proof, the
proof of Theorem `thm:C` (Steps 1 to 4) and the statement of Theorem `thm:C`.  The observer of
Lemma `lem:observer` is being formalized by another agent (P6b, P6c); here it enters as a
hypothesis (`IsObserver`), so that the final theorem follows by plugging the observer in.

Build status: `lake build SignedTropical.Rainbow.OneUpdate` and
`lake build SignedTropical.Rainbow.TheoremC` succeed with no error and no warning.  No `sorry`,
`admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.  The main
theorems (`oneUpdate`, `oneUpdate_bigO`, `updCircuit_spec`, `updCircuit_eval`,
`updCircuit_size_le`, `gapV_eq_update`, `theoremCCircuit_spec`, `schedV_eq`, `psiV_eq`,
`theoremC`, `theoremC_bigO`, `size_le_of_observer_le`) depend only on `propext`,
`Classical.choice` and `Quot.sound` (checked with `#print axioms`).

Imports, all frozen and unchanged: `Rainbow/GapUpdate.lean` (`pairOf`, `Dplus`, `relOf`, `obs`,
`relOf_sublevel`, `gapSum_congr_sublevel`, `update_eq_gapSum`), `Rainbow/Schedule.lean`
(`stageLength`, `schedule`, `stage_bound`, `one_le_nu`, `le_nu_schedule`, `psi_schedule`, `rounds`, `rounds_le_potential`, `rounds_le`),
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

**Theorem 6 (Lemma `lem:oneupdate`, order of the size).**  `oneUpdate_bigO`.  Under the
hypotheses of Theorem 5, if `s_O ≤ c k m³ (s + m)` for a natural number `c` and some `s`, the
circuit has at most `(3c + 11) k m⁵ (s + m)` gates.

*Proof.*  Step 1, `k ≥ 1` since `r < k`, and `m ≥ k` since a base has `k` elements
(`rank_le_card`).  Step 2, `updSize_le`: `3m²s_O ≤ 3c k m⁵ (s + m)`, and each of `km²`, `m⁴`,
`m²`, `m`, `k` is at most `k m⁵ (s + m)` (`pow_mul_pow_le`: `k^i m^j ≤ k^{i'} m^{j'} a` for
`i ≤ i'`, `j ≤ j'`, `k, m, a ≥ 1`), with coefficients `1 + 6 + 2 + 1 + 1 = 11`.

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
`L = stageLength k m` (`min(r(⌊m²/4⌋ + 1), 1 + (r - 1) k m)`, Theorems `thm:potential` and
`thm:stagelength`) and, when every component of `M` has rank at most one, `L r = r` (Corollary
`cor:rankone`).

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

**Proposition 11 (the number of rounds).**  `schedCost_le`, `sum_range_sub_one`.  If
`|U r| ≤ S` for every `r ∈ {1, …, k - 1}`, then
`schedCost L U (k - 1) ≤ (Σ_{r ≤ k-1} L r) · S`, and `Σ_{r ≤ k-1} L r = Σ_{r<k} L r` when
`L 0 = 0`.  For `L = stageLength k m` this is `rounds k m`, at most `(⌊m²/4⌋ + 1) · k(k - 1)/2`
(`Schedule.rounds_le_potential`) and at most `k³ m` for `k ≤ m` (`Schedule.rounds_le`); for
`L r = r` it is `k(k - 1)/2 ≤ k²` (`Schedule.sum_range_id_le`).

*Proof.*  Step 1, induction on `j ≤ k - 1`: `schedCost L U j ≤ (Σ_{r ≤ j} L r) · S`
(`Finset.sum_range_succ`).  Step 2, for `k ≥ 1` the sum over `r ≤ k - 1` is the sum over
`r < k`, and for `k = 0` both are `L 0 = 0`.

**Theorem 12 (Theorem `thm:C`, with observers).**  `theoremC_of_validLength`, and its instances
`theoremC` (`L = stageLength k m`) and `theoremC_rankOne` (`L r = r`, every circuit with at most
two elements).  Let `M` be a matroid on
`E = Fin m` with ground set `E`, rank `k` and a rainbow base, its elements partitioned into the
`k` blocks `blk`.  Let `B` be a Boolean circuit of size `s` that outputs the binary digits of
`r(S)`, least significant first, from the indicator vector of `S`, for every `S ⊆ E`.  Let
`O_r` (`r ∈ ℕ`) be Boolean circuits on `m·m` inputs such that for every `r ∈ {1, …, k - 1}`,
`O_r` is an observer of stage `r` with at most `s_O` gates.  Then a signed tropical circuit `C`
on `m` inputs with
`|C| ≤ R · (3m²s_O + km² + 6m⁴ + 2m² + m + k) + 3ms + mL + 9m² + 5m + 4L + k + 2`,
`R = Σ_{r<k} L r` for valid stage lengths `L` with `L 0 = 0` (`R = rounds k m` in general,
`R = k(k-1)/2` for components of rank one), `L = ⌈log₂(k + 1)⌉`, has the single output `Opt(w)`
at every `w ∈ ℝ^E`.

*Proof.*  Step 1, the circuit is `theoremCCircuit L blk U CA` with `U r = updCircuit blk O_r`
(Lemma `lem:oneupdate`) and `CA` the circuit of Theorem A (`theoremACircuit B (rank M)`, with
`rank M = k`).  Step 2,
the size: every `U r`, `r ∈ {1, …, k - 1}`, has at most `3m²s_O + km² + 6m⁴ + 2m² + m + k`
gates (Proposition 4, `|O_r| ≤ s_O`); Proposition 11 bounds the schedule; `CA` has at most
`3ms + mL + 9m² + 4m + 4L + 1` gates (`theoremACircuit_spec`); Proposition 8 adds `m + k + 1`.
Step 3, the value: by Proposition 8 the output is `psiV blk CA w (schedV L U w (k - 1) 0)`.  A
round with `U r` is the stage map at every state with `ν₀ ≥ r` (`roundV_updCircuit`, from
Theorem 5), so the state is `schedule L M blk w (k - 1) 0` (Proposition 9).  The output is
`Ψ` of that state (Proposition 10 with `theoremACircuit_correct`), which is `Opt(w)`
(`psi_schedule`: `ν₀ = k` after the schedule, and Lemma `lem:duality`).

**Theorem 13 (Theorem `thm:C`, order of the size).**  `theoremC_bigO`,
`theoremC_bigO_rankOne`, `size_le_of_observer_le`.  Under the hypotheses of Theorem 12 with
observers of size at most `c k m³ (s + m)` (the order `O(k m³ (s + m))` of Lemma `lem:observer`,
`c` a natural number), a signed tropical circuit of size at most `(3c + 36) k⁴ m⁶ (s + m) + 2`
has the single output `Opt(w)` at every `w ∈ ℝ^E`: the paper's `O(k⁴ m⁶ (s + m))`.  When every
component of `M` has rank at most one, the size is at most `(3c + 36) k³ m⁵ (s + m) + 2`.
`size_le_of_observer_le` is stated for `R ≤ k^a m^b` rounds, with the bound
`(3c + 36) k^(a+1) m^(b+5) (s + m) + 2`; the two cases are `(a, b) = (3, 1)` and `(2, 0)`.

*Proof.*  Step 1, Theorem 12 with `s_O = c k m³ (s + m)`.  Step 2, the bound of Theorem 12 is at
most `(3c + 36) k⁴ m⁶ (s + m) + 2` whenever `k ≤ m` (`rank_le_card`), `m > 0` forces `k > 0`
(an element lies in a block), `L ≤ k` (`k < 2^k`) and `R ≤ k³ m` (`Schedule.rounds_le`)
(`size_le_of_observer_le`).  If `k = 0`, then `m = 0` and `L = 0`, every round has `0` gates, and
the bound is `2`.  If `k ≥ 1`, then `m ≥ 1`; a round has at most `(3c + 11) k m⁵ (s + m)` gates
(`updSize_le`); the output part `3ms + mL + 9m² + 5m + 4L + k + 2` is at most
`25 k⁴ m⁶ (s + m)`, each monomial (with `mL ≤ mk`, `L ≤ k`) being at most its coefficient times
`k⁴ m⁶ (s + m)`; and `k³m (3c + 11) k m⁵ (s + m) + 25 k⁴ m⁶ (s + m) = (3c + 36) k⁴ m⁶ (s + m)`.

The explicit polynomial: with observers of size `s_O`,
`R · (3m²s_O + km² + 6m⁴ + 2m² + m + k) + 3ms + mL + 9m² + 5m + 4L + k + 2`, where `R` is at most
both `(⌊m²/4⌋ + 1) · k(k - 1)/2` and `k³ m`; with `s_O ≤ c k m³ (s + m)`, at most
`(3c + 36) k⁴ m⁶ (s + m) + 2`.


## 2. Correspondence table

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:observer`, the conclusion, as a hypothesis | `IsObserver`, `IsObserver.length_outs` | `OneUpdate` | definition |
| `lem:oneupdate`, Step 1 (`v`, `D⁺`) | `shiftB_impl`, `dplusB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 2 (compiler on the pairs, `a_b = C_{F_b}(D⁺)`) | `compileB_impl`, `gapV_eq_update`, `indicator_sublevel` | `OneUpdate` | proved |
| `lem:oneupdate`, Step 3 (`p + a`) | `addB_impl`, `updB_impl` | `OneUpdate` | proved |
| `lem:oneupdate`, the circuit and its size | `updCircuit`, `updCircuit_spec`, `updCircuit_size_le`, `updCircuit_eval` | `OneUpdate` | proved |
| `lem:oneupdate` | `oneUpdate`, `oneUpdate_bigO` | `OneUpdate` | proved (observer as hypothesis) |
| `thm:C`, Step 1 (the schedule as a circuit) | `roundB_impl`, `schedB_impl`, `schedCost` | `TheoremC` | proved |
| `thm:C`, Step 2 (the circuit follows the schedule) | `roundV_updCircuit`, `schedV_eq`, `iterate_eq_iterate` | `TheoremC` | proved |
| `thm:C`, Step 3 (output `Σ_b p_b - h_M(-v)` by Theorem A) | `psiB_impl`, `sumB_spec`, `psiV_eq` | `TheoremC` | proved |
| `thm:C`, Step 4 (size) | `schedCost_le`, `sum_range_sub_one`, `size_le_of_observer_le` | `TheoremC` | proved |
| `thm:C` | `theoremCCircuit`, `theoremCCircuit_spec`, `theoremC_of_validLength`, `theoremC`, `theoremC_bigO` | `TheoremC` | proved (observers as hypotheses) |
| `cor:rankone` in Theorem C | `theoremC_rankOne`, `theoremC_bigO_rankOne` | `TheoremC` | proved (observers as hypotheses) |
| `thm:C`, uniformity | none | | not formalized |


## 3. Differences from the paper

1. **Observers as hypotheses.**  Lemma `lem:observer` is formalized by another agent and enters
   here as the hypothesis `IsObserver M blk r (O r)` with `|O r| ≤ s_O` for
   `r ∈ {1, …, k - 1}`.  The final Theorem C follows from `theoremC` (or `theoremC_bigO`) once the
   observer lemma provides such circuits.  No change to the paper.
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
   The paper's statement leaves the domain implicit.  Proposed wording: "For each stage $r$, a
   signed tropical circuit of size $O(km^{5}(s+m))$ maps $(w,p)$ to $p+a$, with $a$ the PO-SL
   update at $v=w-p_{\blk}$, at every state with $\nu_0\ge r$."
4. **Explicit sizes.**  Lemma `lem:oneupdate`: `3m²s_O + km² + 6m⁴ + 2m² + m + k` gates, and
   `(3c + 11) k m⁵ (s + m)` for `s_O ≤ c k m³ (s + m)`.  Theorem C: the polynomial of
   Theorem 12, and `(3c + 36) k⁴ m⁶ (s + m) + 2` for `s_O ≤ c k m³ (s + m)`.  The additive `2`
   covers `k = 0`, where `m = 0` and the circuit still has its final gates.  The output of
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
| `SignedTropical/Rainbow/OneUpdate.lean` | 271 |
| `SignedTropical/Rainbow/TheoremC.lean` | 389 |


## 5. Not done

* Lemma `lem:observer` itself (P6b, P6c).  To obtain Theorem C unconditionally, a later step
  must provide, for each `r ∈ {1, …, k - 1}`, a circuit `O_r : Circuit BoolOp (m * m)` with
  `IsObserver M blk r O_r` and a size bound.  The observer of P6c carries a relation as its bits
  `relBits G` (`m²` operands `R g f`); a circuit on `Fin (m * m)` inputs is obtained by reading
  `R g f` from input `finProdFinEquiv (g, f)`, whose bit at the input vector of `IsObserver` is
  `[pairOf (finProdFinEquiv (g, f)) ∈ G] = [(g, f) ∈ G]`.  Its outputs must be the list
  `(F_b(G_t))_{b<k}`; a different `Decidable` instance in `decide` is harmless
  (`Bool.decide_congr`, `decide_eq_decide`).
* Uniformity (difference 5).


## 6. API for later agents

Namespace `SignedTropical.Rainbow.TheoremC`.  `M : Matroid (Fin m)`, `blk : Fin m → Fin k`,
`hE : M.E = Set.univ`, `hk : rank M = k`, `hM : ∃ B, IsRainbowBase M blk B`.

* `IsObserver M blk r O : Prop` for `O : Circuit BoolOp (m * m)`: `∀ v t, 0 ≤ t →
  O.eval boolInterp (fun i => decide (pairOf i ∈ POSL.Gt v t)) = List.ofFn fun b : Fin k =>
  decide (nu (POSL.NG M (POSL.Gt v t)) blk ≤ r ∧ b ∈ Av (POSL.NG M (POSL.Gt v t)) blk)`.
* `IsObserver.length_outs : IsObserver M blk r O → O.outs.length = k`.
* `updCircuit blk O : Circuit STOp (m + k)`, the one-update circuit on `Fin.append w p`.
* `updCircuit_spec blk O : (updCircuit blk O).size = m + m * m * 2 + compileCost O + k ∧ ∀ w p,
  (updCircuit blk O).eval (stInterp ℝ) (Fin.append w p) = List.ofFn (p + gapV O (shift blk w p))`.
* `updCircuit_size_le blk (hO : O.outs.length = k) : (updCircuit blk O).size ≤ 3 * m ^ 2 * O.size +
  k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k`.
* `updCircuit_eval hE hk hM (hrk : r < k) (hO : IsObserver M blk r O) (hr : r ≤ nu (minBases M
  (shift blk w p)) blk) : (updCircuit blk O).eval (stInterp ℝ) (Fin.append w p) = List.ofFn (p +
  Validity.update (POSL.N M (shift blk w p)) blk r)`.
* `gapV_eq_update hE hk hM hrk hO hr : gapV O v = Validity.update (POSL.N M v) blk r`.
* `oneUpdate hE hk hM hrk hO : ∃ U : Circuit STOp (m + k), U.size ≤ 3 * m ^ 2 * O.size + k * m ^ 2 +
  6 * m ^ 4 + 2 * m ^ 2 + m + k ∧ ∀ w p, r ≤ nu (minBases M (shift blk w p)) blk → U.eval (stInterp
  ℝ) (Fin.append w p) = List.ofFn (p + Validity.update (POSL.N M (shift blk w p)) blk r)`
  (Lemma `lem:oneupdate`); `oneUpdate_bigO ... (hs : O.size ≤ c * (k * m ^ 3 * (s + m)))`: the
  same with `U.size ≤ (3 * c + 11) * (k * m ^ 5 * (s + m))`.
* `theoremCCircuit L blk U CA : Circuit STOp m` for `L : ℕ → ℕ`, `U : ℕ → Circuit STOp (m + k)`,
  `CA : Circuit STOp m`; `theoremCCircuit_spec L blk U CA : size = schedCost L U (k - 1) +
  (m + CA.size + k + 1) ∧ ∀ w, eval w = [psiV blk CA w (schedV L U w (k - 1) 0)]`.
* `schedV_eq hE hk hM hL w hU : ∀ j, j ≤ k - 1 → schedV L U w j 0 = Schedule.schedule L M blk w j 0`,
  for valid `L` and
  rounds that are the stage maps on the states of their stage; `roundV_updCircuit`: the rounds of
  `updCircuit blk O` are; `psiV_eq hCA w p : psiV blk CA w p = Psi M blk w p` for `CA` computing
  `h_M`.
* `theoremC hE hk hM B hB O sO hO : ∃ C : Circuit STOp m, C.size ≤ Schedule.rounds k m *
  (3 * m ^ 2 * sO + k * m ^ 2 + 6 * m ^ 4 + 2 * m ^ 2 + m + k) + (3 * m * B.size + m * Nat.size
  k + 9 * m ^ 2 + 5 * m + 4 * Nat.size k + k + 2) ∧ ∀ w, C.eval (stInterp ℝ) w = [Opt M blk w]`,
  where `hB` is the rank hypothesis of `theoremA` and `hO : ∀ r, 1 ≤ r → r < k → IsObserver M blk r
  (O r) ∧ (O r).size ≤ sO`.  `theoremC_of_validLength hE hk hM hL hL0 B hB O sO hO`: the same with
  `Σ_{r<k} L r` in place of `Schedule.rounds k m`, for valid `L` with `L 0 = 0`;
  `theoremC_rankOne hE hk hM hpar B hB O sO hO`: the same with `Σ_{r<k} r`, for
  `hpar : ∀ C, M.IsCircuit C → C.encard ≤ 2`.
* `theoremC_bigO hE hk hM B hB O c hO` with `(O r).size ≤ c * (k * m ^ 3 * (B.size + m))`:
  `∃ C, C.size ≤ (3 * c + 36) * (k ^ 4 * m ^ 6 * (B.size + m)) + 2 ∧ ∀ w, C.eval (stInterp ℝ) w =
  [Opt M blk w]`; `theoremC_bigO_rankOne hE hk hM hpar B hB O c hO`: the same with
  `k ^ 3 * m ^ 5`.
* `rank_le_card M : rank M ≤ m` (`Matroid.lean`); `pow_mul_pow_le`, `updSize_le`, `size_le_of_observer_le`
  (arithmetic of the bounds).
* Builders, with their `Impl` lemmas: `realsR r`, `shiftB`, `dplusB`, `updB`, `roundB`, `schedB`,
  `sumB`, `psiB`, `thmCB`.
