# Phase 2 and the compiler-layer extensions: index

Lean 4 `v4.32.0`, Mathlib `v4.32.0`.  Companion to `daishu/paper/greedy_intersection.tex`
(Sections 2 to 5) and `daishu/paper/signed_assignment.tex` (Section 3 and Proposition
`prop:normal-form`).  Phase 1 is documented in `PHASE1.md`.

This file is the index.  The natural-language statement and the step-structured proof of every
formalized result, written to agree with the Lean statement exactly, are in the companion file of
its module under `notes/`, listed in the last column of the tables below.

Labels follow the revision of `greedy_intersection.tex` of 2026-10-16.  Some notes predate the
revision of 2026-10-12 and use two old labels: `lem:observer`, Step 4 (the Boolean augmenting
path circuit) is now `lem:augment`, and `cor:classes`, items 6 and 7 (transversal matroids and
gammoids) are now `cor:transversal`.

Consolidation of 2026-10-12.  Duplicated lemmas were merged and the notes predate it: the bounds
`rank_le_card`, `rk_le_card` (`Matroid.lean`), `rk_lt_two_pow`, `size_div_two_add_one`
(`TheoremA.lean`), `indicator_filter`, `filter_indicator` (`Models.lean`) replace their local
copies (`TheoremC.rank_le_card_fin`, `Counting.rk_lt_two_pow_size` among them); `Exchange` uses
`IsRainbowIndep.card_le_nu`, `exists_isRainbowIndep_card_eq_nu`, `mem_Av`, `nu_le` of
`MinBases.lean`; `minBases_congr` and `minBases_eq_self` are unconditional (`MinBases.lean`); the
independence tests from rank queries are `indepOfRankV`, `indepOfRankB`, `indepOfRankB_impl`,
`indepOfRank_correct` (`BoolAlg/Count.lean`), used by the observer oracle and by transversal
matroids; the column matroid and the elimination over a field are `Elimination.lean`, through
which `Binary.lean` reads its Boolean elimination (`zst_elimV`).  Theorem C now uses the stage
bound of Theorem `thm:stagelength` (`Rainbow/StageLength.lean`) through valid stage lengths
(`Schedule.ValidLength`).  A base fixed for the whole stage bounds every stage by
`1 + k (2m - k - 1)` updates (`StageLength.le_of_nu_iterate_eq`), so the schedule has at most
`2 k² m` updates.

Revision of 2026-10-14.  The matroid intersection circuit asks the test of `y` only about sets
`A ∋ y` with `A - y` independent (`MI.ExchOracle`), and such a set is independent in `N_G` iff
the term of the cluster of `y` in the rank formula is tight: one rank evaluation per test
(`Observer.locV_exchOracle`) instead of `m`.  The observer of stage `r` runs `r + 1` rounds of
augmentation (`MI.avGuardV_eq`), and its size is `O(r m² (s + m))`.  Theorem D for common
independent sets uses one padded instance (`TheoremD.minCommonBaseWeight_pad`) instead of `m`
truncations.

Revision of 2026-10-16 (event levels).  The observer reads the `m + 2m²` event bits
`[t_x ≤ t]`, `[T_xy ≤ t]`, `[ω_xy ≤ t]` of Lemma `lem:events` (`Rainbow/Events.lean`) instead of
the `m²` bits of `G_t`, and `N(t)` changes only at the `2m` levels `t_x`, `ρ_x`
(`Events.bott_inLev`, `Events.uval_inLev`).  The one-update circuit computes these values (the
entry times by the compiler of Theorem `thm:compiler`, the merge values by the Floyd–Warshall
algorithm over `(min, max)`) and runs the compiler at the `2m` levels (Corollary `cor:levels`,
`LevelCompiler.lean`): `2m` lifted copies of the observer instead of `m²`.  Theorem C has size at
most `3328 k³ m⁴ (s+m) + 2`, and `1390 k³ m³ (s+m) + 2` when every component of `M` has rank at
most one (Corollary `cor:rankone`, `Rainbow/RankOne.lean`).  Theorem D:
`3328 · 1200 m⁷ (s₁+s₂+m) + 2` for common bases and `3328 · 653313 m⁷ (s₁+s₂+m) + 3` for common
independent sets.

Status: complete (2026-10-16).  67 modules, about 24,530 lines; `lake build` reports no errors and no warnings, and every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## 1. Module map

| Module | Namespace | Content | Companion |
|---|---|---|---|
| `NormalForm.lean` | `SignedTropical.NormalForm` | the `±` normal form, interchange of `max` and `min` | `notes/E1-normal-form.md` |
| `Integral.lean` | `SignedTropical.Integral` | integral readings of the gap sum, Lipschitz bounds | `notes/E2-integral.md` |
| `SparsePaving.lean`, `Asymptotic.lean` | `SignedTropical.SparsePaving`, `SignedTropical.Asymptotic` | sparse paving matroids, the number of matroids, Corollary D | `notes/E3-asymptotic.md` |
| `Elimination.lean` | `SignedTropical` | the column matroid over a field, elimination without branching (shared by `Binary.lean` and `Classes/Field.lean`) | `notes/E4-classes.md`, Section 1.2 |
| `Classes/Dual.lean`, `Classes/Field.lean`, `Classes/Rational.lean` | `SignedTropical.Classes` | duals, matroids over finite fields and over ℚ | `notes/E4-classes.md` |
| `Classes/Graphic.lean`, `Classes/Cographic.lean` | `SignedTropical.Classes.Graphic` | cycles, the cycle matroid, its circuits, rank circuits; cographic matroids | `notes/Graphic.md` |
| `Rainbow/Defs.lean` | `SignedTropical.Rainbow` | shared definitions: rainbow sets, `ν`, `Av`, `β`, `Opt`, `Ψ`, `M^u`, `θ`, `P_t`, admissible families | this file, Section 2 |
| `Rainbow/Connectivity.lean` | `SignedTropical.Rainbow.Conn` | connected components, `lem:minbases`(1),(4) | `notes/P0b-connectivity.md` |
| `Rainbow/MinBases.lean` | `SignedTropical.Rainbow` | `lem:minbases`(2),(3), `eq:rank-mu`, API | `notes/P0a-minbases.md` |
| `Rainbow/Exchange.lean` | `SignedTropical.Rainbow.Exchange` | exchange graphs, `lem:avoidable`, augmenting paths | `notes/P2-exchange.md` |
| `Rainbow/PossiblyOptimal.lean`, `Rainbow/Lagrangian.lean` | `SignedTropical.Rainbow.Pos` | `prop:pos`, `lem:path`, `lem:duality` | `notes/P1-core.md` |
| `Rainbow/Partition.lean`, `Rainbow/NotMatroid.lean`, `Rainbow/Doubling.lean` | `...Partition`, `...NotMatroid`, `...Doubling` | partition matroids and `prop:assign-pos`, `U_{2,4}` and `prop:notmatroid`, `lem:doubling` and the rank of `M₁ ⊕ M₂✶` | `notes/P1x-partition-doubling.md` |
| `Rainbow/Truncation.lean` | `SignedTropical.Rainbow.Trunc` | truncations (the padded matroids of Theorem D, Step 4) | `notes/Truncation.md` |
| `Rainbow/Star.lean`, `Rainbow/NPHard.lean` | `SignedTropical.Rainbow.Graphs` | `prop:star`, the reduction of `prop:nphard` | `notes/P1g-graphs.md` |
| `Rainbow/Update.lean`, `Rainbow/Validity.lean` | `SignedTropical.Rainbow.Validity` | `def:update`, `eq:update-integral`, `thm:validity` | `notes/P3-validity.md` |
| `Rainbow/POSL.lean`, `Rainbow/POSLRank.lean`, `Rainbow/POSLAssign.lean` | `SignedTropical.Rainbow.POSL`, `...POSLAssign` | `def:posl`, `prop:posl` (with the assignment clause), the rank of `N_G` | `notes/P4-posl.md` |
| `Rainbow/Potential.lean` | `SignedTropical.Rainbow.Potential` | `thm:potential`, the stage map and the stage bound | `notes/P5-potential.md` |
| `Rainbow/StageLength.lean` | `SignedTropical.Rainbow.StageLength` | `thm:stagelength`: the crossing pair (in one component), the epoch with `ρ = 0`, the stage bounds `1 + (r - 1) k m` and, with a base fixed for the whole stage, `1 + k (2m - k - 1)` | `notes/StageLength.md` |
| `Rainbow/RankOne.lean` | `SignedTropical.Rainbow.RankOne` | `cor:rankone`: components of rank at most one, every update ends an epoch, stages of at most `r` updates | `notes/StageLength.md`, Section 1.7 |
| `BoolAlg/*.lean` | `SignedTropical.BoolAlg` | Boolean gadgets: arithmetic, counting, relations, paths, composition | `notes/P6a-boolalg.md` |
| `Rainbow/MICircuit.lean` | `SignedTropical.Rainbow.MI` | `lem:augment`: the matroid intersection circuit with `j` rounds, generic in context-dependent exchange tests indexed by the added element (used in `lem:observer`, Step 3, and in `cor:transversal`) | `notes/P6b-micircuit.md` |
| `Rainbow/Events.lean` | `SignedTropical.Rainbow.Events` | `lem:events`: entry times, merge values by Floyd–Warshall over `(min, max)`, the `2m` levels and the covering lemma, order values, the query values `𝒬(v)` | `notes/P6d-events.md` |
| `LevelCompiler.lean` | `SignedTropical` | `cor:levels`: the compiler at levels computed inside the circuit | `notes/P6d-events.md` |
| `Rainbow/ObserverOracle.lean` | `SignedTropical.Rainbow.Observer` | `lem:observer`, Steps 1 and 2: the context from the event bits and the exchange tests of `N(t)` | `notes/P6c-observer.md` |
| `Rainbow/Observer.lean`, `Rainbow/TheoremCFinal.lean` | `SignedTropical.Rainbow.Observer`, `...TheoremCFinal` | `lem:observer` (`r₀ + 1` rounds, on the `m + 2m²` event bits); Theorem C, unconditional, size at most `3328 k³ m⁴ (s+m) + 2` | `notes/P6c-observer.md` |
| `Rainbow/GapUpdate.lean` | `SignedTropical.Rainbow.GapUpdate` | `lem:oneupdate`, Step 3: the update as a gap sum over the `2m` event levels | `notes/GapUpdate.md` |
| `Rainbow/Schedule.lean` | `SignedTropical.Rainbow.Schedule` | `thm:C`, Steps 1 to 4: the schedule for valid stage lengths (`min(r(⌊m²/4⌋+1), 1+(r-1)km, 1+k(2m-k-1))` in general, `r` for components of rank one), the invariant, `Ψ = Opt`, the number of updates, weighted by the rounds of the observers | `notes/Schedule.md` |
| `Rainbow/OneUpdate.lean`, `Rainbow/TheoremC.lean` | `SignedTropical.Rainbow.TheoremC` | the circuits of `lem:oneupdate` (the event values, the compiler at the `2m` levels) and Theorem C, from observers | `notes/P7-theoremC.md` |
| `Rainbow/TheoremDRank.lean` | `SignedTropical.Rainbow.TheoremD` | rank circuits of `M₁ ⊕ M₂✶`, of truncations and of the padded matroids | `notes/P8-theoremD.md` |
| `Rainbow/TheoremD.lean` | `SignedTropical.Rainbow.TheoremD` | Theorem D, both parts, explicit constants | `notes/P8-theoremD.md` |
| `Classes/Transversal.lean`, `Classes/TransversalGammoid.lean` | `SignedTropical.Classes.Transversal` | `cor:transversal`: transversal matroids, gammoids, the Ingleton and Piff theorem | `notes/E5-transversal.md` |

## 2. Shared definitions (`Rainbow/Defs.lean`)

A matroid is `M : Matroid (Fin m)` with ground set `univ`; the blocks `R_1, …, R_k` are the
fibres of `blk : Fin m → Fin k`.

* `IsRainbow blk S`: `S` meets every block at most once.  `blockSet blk Q = E_Q`.
  `blocksMet blk S`: the blocks that `S` meets.
* `nu N blk = ν(N)`, the largest size of a rainbow independent set of `N`; `Av N blk = Av(N)`,
  the blocks missed by some rainbow independent set of size `ν(N)`.
* `IsRainbowBase M blk B`: a rainbow base; with `k = r(M)` blocks it meets every block once.
* `IsMinBase M u B`, `minBaseWeight M u = β_M(u)`, `Opt M blk w`, `shift blk w p = w - p_blk`,
  `Psi M blk w p = Σ_b p_b + β_M(w - p_blk)`.
* `minBases M u = M^u`, the direct sum over the values `ℓ` of `u` of the matroids
  `(M | {u ≤ ℓ}) / {u < ℓ}` on the level sets.
* `theta M v B = θ(B)` (with Mathlib's fundamental circuits), `Pos M v t = P_t`.
* `connRel M e f`: `e = f`, or `e` and `f` lie on a common circuit.
* `IsAdmissible M blk v N`: (F1) `N(0) = M^v`; (F2) bases of `N(t)` are bases of `N(t')` for
  `t ≤ t'`; (F3) `P_t ⊆ Bases(N(t))`; (F4) a rainbow base for all large `t`; (F5) finitely many
  levels, `0` among them, with `N` constant between consecutive levels (on half-open intervals).

## 3. Correspondence with the papers

| Paper | Result | Lean | Status |
|---|---|---|---|
| `signed_assignment.tex` | `prop:normal-form` | `NormalForm.normal_form`, `normal_form_shared`, `interchange` | proved |
| `signed_assignment.tex` | `prop:two-readings` | `Integral.gapSum_eq_integral_Ioi`, `gapSum_eq_integral_lovasz` | proved |
| `signed_assignment.tex` | `lem:lipschitz`, Lipschitz part of `cor:integer-observable` | `Integral.lipschitz`, `integer_observable_lipschitz` | proved |
| `greedy_intersection.tex` | `def:ti` (the two expressions) | `Integral.gapSum_eq_intervalIntegral`, `gapSum_eq_integral_Ioi` | proved |
| `greedy_intersection.tex` | `cor:levels` | `levB_spec`, `levCost_le`, `levVal_eq` | proved |
| `greedy_intersection.tex` | `cor:count` | `Asymptotic.corollaryD_tendsto`, `corollaryD_explicit`, `SparsePaving.rpow_le_ncard_matroids` | proved |
| `greedy_intersection.tex` | `cor:classes`, item 5 (cycle matroids) | `Classes.Graphic.Multigraph.corollaryC_graphic` | proved |
| `greedy_intersection.tex` | `lem:minbases` | `Conn.isMinBase_iff_fundCircuit`, `isMinBase_iff_forall_subset_closure`, `isBase_minBases_iff`, `IsMinBase.isMinBase_exchange_iff`, `IsMinBase.fundCircuit_minBases`, `Conn.connRel_equivalence`, `Conn.isMinBase_iff_comp`, `minBases_congr` | proved |
| `greedy_intersection.tex` | `eq:rank-mu` | `rk_minBases` | proved |
| `greedy_intersection.tex` | `lem:duality` | `Pos.psi_le_opt`, `Pos.psi_eq_opt` | proved |
| `greedy_intersection.tex` | `prop:pos` and the remark after it | `Pos.tfae_pos`, `pos_mono`, `mem_pos_zero`, `mem_pos_iff_isBase` | proved |
| `greedy_intersection.tex` | `lem:path` | `Pos.mem_pos_of_isMinBase_shift` | proved |
| `greedy_intersection.tex` | `lem:avoidable` | `Exchange.card_add_nu_le`, `card_av_add_nu`, `av_subset` | proved |
| `greedy_intersection.tex` | `thm:D`, Step 4 (the padded matroids) | `TheoremD.isBase_pad_iff`, `padRankCircuit_rank`, `minCommonBaseWeight_pad` | proved |
| `greedy_intersection.tex` | `prop:assign-pos` | `Partition.theta_eq_sup'`, `Partition.pos_eq`, `Partition.pos_eq_restrict` | proved |
| `greedy_intersection.tex` | `prop:notmatroid` | `NotMatroid.theta_values`, `pos_two`, `pos_two_not_exchange`, `pos_two_not_matroid` | proved |
| `greedy_intersection.tex` | `lem:doubling`; `thm:D`, Steps 1 and 2 | `Doubling.doubling`, `isRainbowBase_iff`, `opt_eq`, `rank_double_eq`, `rk_pair` | proved |
| `greedy_intersection.tex` | `prop:star` | `Graphs.isRainbowSpanningTree_star_iff`, `rainbowTreePolynomial_eq_permanent` | proved |
| `greedy_intersection.tex` | `prop:nphard`, Steps 2 to 4 (the reduction) | `Graphs.exists_rainbowSpanningTree_theta_le_iff`, `rank_reduction` | proved; complexity classes cited |
| `greedy_intersection.tex` | `def:update`, the paragraph after it, `eq:update-integral` | `Validity.tau`, `lam`, `update`, `isLeast_tau`, `mem_Av_iff_lam_le`, `volume_eq`, `update_eq_integral` | proved |
| `greedy_intersection.tex` | `thm:validity` | `Validity.validity`, `psi_update`, `isMinBase_update`, `nu_le_nu_update` | proved |
| `greedy_intersection.tex` | `def:posl`, `prop:posl` | `POSL.u`, `POSL.N`, `isAdmissible`, `prop_posl`, `N_eq_NG`, `POSLAssign.isBase_N_iff_restrict` | proved |
| `greedy_intersection.tex` | `lem:events` | `Events.entry_spec`, `Events.mem_PO_iff`, `Events.fwV_le_iff`, `Events.sameCluster_iff`, `Events.bott_inLev`, `Events.uval_inLev`, `Events.ord_iff`, `Events.Qv_inLev` | proved |
| `greedy_intersection.tex` | `thm:potential` | `Potential.potential`, `stage_bound`, `stageMap_eq_self`, `card_piPairs_le` | proved |
| `greedy_intersection.tex` | `thm:stagelength` | `StageLength.exists_crossing_pair`, `crossPairs_ssubset`, `av_ne_of_rk_eq_zero`, `av_ne_of_card_av_eq`, `lt_of_nu_iterate_eq`, `resolvedPairs_ssubset`, `le_of_nu_iterate_eq`, `Schedule.validLength_stageLength` | proved |
| `greedy_intersection.tex` | `cor:rankone` | `RankOne.circuit_encard_le_two`, `RankOne.av_ne_av`, `RankOne.lt_of_nu_iterate_eq`, `Schedule.validLength_rankOne`, `TheoremCFinal.theoremC_final_rankOne` | proved |
| `greedy_intersection.tex` | `prop:ladder` | none | not formalized; checked by computation (Section `sec:checks` of the paper) |
| `greedy_intersection.tex` | `lem:augment` | `MI.ExchOracle`, `MI.roundsB_impl`, `MI.stateV_eq`, `MI.miV_spec`, `MI.miCost_add_le`, `MI.avGuardCircuit_spec`, `MI.nuCircuit_spec` | proved |
| `greedy_intersection.tex` | `lem:observer` | `Observer.lem_observer`, `Observer.evCtxV_eq`, `Observer.locV_exchOracle`, `TheoremCFinal.isObserver_observer`, `observer_size_le` | proved |
| `greedy_intersection.tex` | `lem:oneupdate` | `TheoremC.oneUpdate`, `TheoremC.updV_eq_update`, `TheoremC.roundSize_le`, `GapUpdate.update_eq_levSum` | proved |
| `greedy_intersection.tex` | `thm:C` | `TheoremCFinal.theoremC_final`, `theoremC_final_poly`, `theoremC_final_rankOne`, `TheoremC.theoremC_of_validLength`, `TheoremC.theoremC_bigO`, `Schedule.psi_schedule`, `Schedule.rounds_le`, `Schedule.sum_stageLength_mul_le` | proved |
| `greedy_intersection.tex` | `thm:D` | `TheoremD.theoremD`, `theoremD_commonBase`, `theoremD_commonIndep`, `minCommonBaseWeight_pad` | proved |
| `greedy_intersection.tex` | `cor:classes`, items 2 to 4 and the dual in item 5 | `Classes.theoremA_field`, `theoremA_rat`, `dual_rankCircuit`, `Graphic.Multigraph.corollaryC_cographic` | proved |
| `greedy_intersection.tex` | `cor:transversal` (transversal matroids, gammoids) | `Classes.Transversal.theoremA_transversal`, `transversal_rankCircuit`, `dual_indep_iff_isLinked`, `gammoid_rankCircuit`, `theoremA_gammoid` | proved |

## 4. Conventions and scope

* No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, zero warnings.
* Where the paper writes `O(·)`, the Lean statement gives an explicit bound.
* Not formalized: uniformity of the circuit families (as in Phase 1); complexity classes in
  `prop:nphard` (the reduction itself is formalized); the Pippenger and Fischer simulation
  remark after `cor:classes` (concrete classes get explicit circuits instead); the example
  `prop:ladder` (checked by computation).
