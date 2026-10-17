# Lean formalization of "Greedy and Matroid Intersection without Branching"

This archive contains the Lean 4 development that accompanies the submission.  It proves the
results of Sections 2 to 5 of the paper, with the explicit constants of the appendix.

## Building

The toolchain is fixed in `lean-toolchain` (Lean 4.32.0), and Mathlib v4.32.0 is pinned in
`lake-manifest.json`.

```
lake exe cache get        # downloads the prebuilt Mathlib
lake build                # builds the library GreedyIntersection
lake env lean Axioms.lean # prints the axioms of the main results
```

`lake build` reports no errors, no warnings and no `sorry`.  The main results depend on no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Conventions

* A matroid is Mathlib's `Matroid (Fin m)` with ground set `Set.univ`; sets of elements are
  `Finset (Fin m)`, and `rk M S` is the rank of `S`.
* A circuit `Circuit Op n` is a list of gates, each applied to inputs, the constant source or
  earlier gates, together with a list of output operands.  `Circuit.size` is the number of
  gates, and `Circuit.eval I C x` evaluates `C` at `x` under a reading `I` of the gate set.
  The gates of a (max,+,-)-circuit are `MPMOp` with `mpmInterp`, those of a Boolean circuit
  `BoolOp` with `boolInterp`.  Boolean circuits output integers in binary, least significant
  bit first (`bitsVal`).
* Where the paper writes `O(·)`, the Lean statement gives an explicit bound.  Theorem C is
  proved with size at most `3328 k³ m⁴ (s+m) + 2`, and `1390 k³ m³ (s+m) + 2` when every
  connected component of `M` has rank at most one; Theorem D with
  `3328 · 1200 m⁷ (s₁+s₂+m) + 2` for common bases and `3328 · 653313 m⁷ (s₁+s₂+m) + 3` for
  common independent sets.

## Results of the paper

Names are relative to the namespace `GreedyIntersection`; modules are relative to the
directory `GreedyIntersection/`.

| Paper | Lean | Module |
|---|---|---|
| Definition 1 | `Circuit`, `Circuit.size`, `Circuit.eval`, `MPMOp`, `BoolOp` | `Circuit`, `Models` |
| Definition 2 and the remark after it | `levelSum`, `sublevelSet`, `Integral.levelSum_eq_intervalIntegral`, `Integral.levelSum_eq_integral_lovasz` | `LevelSum`, `Integral` |
| Theorem 3 | `thm_levelSum`, `sumCircuit_size` | `SumCircuit` |
| Corollary 4 | `levB_spec`, `levCost_le`, `levVal_eq` | `LevelSumCircuit` |
| Lemma 5 | `maxBasisWeight_eq_levelSum`, `maxBasisWeight_add_const`, `maxBasisWeight_indicator` | `Matroid` |
| Theorem A | `theoremA` | `TheoremA` |
| Theorem B | `theoremB`, `theoremB_of_forall` | `Converse` |
| Corollary 6 | (1) `classes_binary_poly`; (2) `Classes.theoremA_field`; (3) `Classes.theoremA_rat`; (4) `Classes.dual_rankCircuit`; (5) `Classes.Graphic.Multigraph.classes_graphic`, `Classes.Graphic.Multigraph.classes_cographic` | `Binary`, `Classes` |
| Lemma 7 | `Rainbow.Pos.psi_le_opt`, `Rainbow.Pos.psi_eq_opt` | `Rainbow/Lagrangian` |
| Definition 8, Proposition 9 | `Rainbow.theta`, `Rainbow.Pos`, `Rainbow.Pos.tfae_pos` | `Rainbow/Defs`, `Rainbow/PossiblyOptimal` |
| Proposition 10 | (1) `Rainbow.NotMatroid.pos_two_not_matroid`; (2) the reduction, `Rainbow.Graphs.exists_rainbowSpanningTree_theta_le_iff` | `Rainbow/NotMatroid`, `Rainbow/NPHard` |
| Definition 11 | `Rainbow.IsAdmissible` | `Rainbow/Defs` |
| Definition 12, Lemma 13 | `Rainbow.Validity.update`, `Rainbow.Validity.mem_Av_iff_lam_le`, `Rainbow.Validity.update_eq_integral` | `Rainbow/Update` |
| Theorem 14 | `Rainbow.Validity.validity` | `Rainbow/Validity` |
| Definition 15, Proposition 16 | `Rainbow.POSL.N`, `Rainbow.POSL.prop_posl` | `Rainbow/POSL` |
| Lemma 17 | `Rainbow.Events.mem_PO_iff`, `Rainbow.Events.sameCluster_iff`, `Rainbow.Events.bott_inLev`, `Rainbow.Events.ord_iff` | `Rainbow/Events` |
| Theorem 18 | `Rainbow.Potential.potential`, `Rainbow.Potential.stage_bound` | `Rainbow/Potential` |
| Theorem 19, Lemma 31 | `Rainbow.StageLength.exists_crossing_pair`, `Rainbow.StageLength.lt_of_nu_iterate_eq`, `Rainbow.StageLength.le_of_nu_iterate_eq` | `Rainbow/StageLength` |
| Corollary 20 | `Rainbow.RankOne.lt_of_nu_iterate_eq` | `Rainbow/RankOne` |
| Lemma 21 | `Rainbow.MI.miV_spec`, `Rainbow.MI.avIndCircuit_spec` | `Rainbow/MICircuit` |
| Lemma 22 | `Rainbow.Tests.lem_levelTests` | `Rainbow/Tests` |
| Lemma 23 | `Rainbow.TheoremC.oneUpdate`, `Rainbow.LevelUpdate.update_eq_levSum` | `Rainbow/OneUpdate`, `Rainbow/LevelUpdate` |
| Theorem C | `Rainbow.TheoremCFinal.theoremC_final`, `Rainbow.TheoremCFinal.theoremC_final_rankOne` | `Rainbow/TheoremCFinal` |
| Lemma 24 | `Rainbow.Doubling.doubling` | `Rainbow/Doubling` |
| Theorem D | `Rainbow.TheoremD.theoremD`, `Rainbow.TheoremD.theoremD_commonBase`, `Rainbow.TheoremD.theoremD_commonIndep` | `Rainbow/TheoremD` |
| Lemma 25, equation (1) | `Rainbow.Conn.isMinBase_iff_fundCircuit`, `Rainbow.rk_minBases` | `Rainbow/Connectivity`, `Rainbow/MinBases` |
| Corollary 26 | `integer_levelSum` | `SumCircuit` |
| Corollary 27 | `Asymptotic.count_explicit`, `Asymptotic.count_tendsto` | `Asymptotic` |
| Proposition 28 | `Rainbow.Graphs.rainbowTreePolynomial_eq_permanent` | `Rainbow/Star` |
| Lemma 29 | `Rainbow.Pos.mem_pos_of_isMinBase_shift` | `Rainbow/PossiblyOptimal` |
| Lemma 30 | `Rainbow.Exchange.card_av_add_nu` | `Rainbow/Exchange` |
| Corollary 32 | `Classes.Transversal.theoremA_transversal`, `Classes.Transversal.theoremA_gammoid` | `Classes/Transversal`, `Classes/TransversalGammoid` |

Not formalized: the uniformity of the circuit families, and the complexity classes in
Proposition 10(2), whose reduction is formalized.

The modules `Lattice` and `Subtractionfree`, and the Lipschitz bounds in `Integral`, contain
auxiliary results that the paper does not state.
