import GreedyIntersection

/-!
# Axioms of the main results

`lake env lean Axioms.lean` prints the axioms on which the main results depend.  Each list
consists of `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms GreedyIntersection.thm_levelSum                                -- Theorem 3
#print axioms GreedyIntersection.levB_spec                                   -- Corollary 4
#print axioms GreedyIntersection.maxBasisWeight_eq_levelSum                  -- Lemma 5
#print axioms GreedyIntersection.theoremA                                    -- Theorem A
#print axioms GreedyIntersection.theoremB                                    -- Theorem B
#print axioms GreedyIntersection.classes_binary_poly                         -- Corollary 6(1)
#print axioms GreedyIntersection.Classes.theoremA_field                      -- Corollary 6(2)
#print axioms GreedyIntersection.Classes.theoremA_rat                        -- Corollary 6(3)
#print axioms GreedyIntersection.Rainbow.Validity.validity                   -- Theorem 14
#print axioms GreedyIntersection.Rainbow.POSL.prop_posl                      -- Proposition 16
#print axioms GreedyIntersection.Rainbow.Potential.potential                 -- Theorem 18
#print axioms GreedyIntersection.Rainbow.TheoremCFinal.theoremC_final        -- Theorem C
#print axioms GreedyIntersection.Rainbow.TheoremCFinal.theoremC_final_rankOne -- Corollary 20
#print axioms GreedyIntersection.Rainbow.TheoremD.theoremD                   -- Theorem D
#print axioms GreedyIntersection.Asymptotic.count_tendsto                    -- Corollary 28
#print axioms GreedyIntersection.Classes.Transversal.theoremA_gammoid        -- Corollary 33
