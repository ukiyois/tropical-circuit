import SignedTropical.Rainbow.POSL
import SignedTropical.Rainbow.Partition
import SignedTropical.Rainbow.PossiblyOptimal

/-!
# PO-SL for the assignment problem

`greedy_intersection.tex`, Proposition `prop:posl`, the last sentence and Step 6 of its proof:
for the partition matroid of the columns of a bipartite graph, `N(t)` is the column matroid
restricted to the threshold graph `{D ≤ t}` of Proposition `prop:assign-pos`, where
`D_f = v_f - min{v_e : e in the column of f}` (`Partition.slack`).

Step 6.  `PO_t` is `{D ≤ t}` (`Partition.notMem_closure_iff_slack_le`), the components are the
columns, and the elements of `PO_t` in one column lie within `t` of the column minimum, so they
are pairwise linked and form one cluster.  A base of `N(t)` lies in `PO_t`
(`POSL.subset_PO_of_isBase_N`); conversely a base inside `PO_t` is minimum for `u_t` by Lemma
`lem:minbases`(1), since the element of `B` in the column of `e ∉ B` shares the cluster of `e`
or `e ∉ PO_t` has the top weight.
-/

open Finset

namespace SignedTropical.Rainbow.POSLAssign

open SignedTropical.Rainbow SignedTropical.Rainbow.POSL SignedTropical.Rainbow.Partition

variable {m n : ℕ} (col : Fin m → Fin n) (v : Fin m → ℝ)

/-- `PO_t = {D ≤ t}` for the column matroid. -/
theorem mem_PO_iff {t : ℝ} (f : Fin m) : f ∈ PO (colMatroid col) v t ↔ slack col v f ≤ t :=
  notMem_closure_iff_slack_le col v f t

/-- **Proposition `prop:posl`, assignment.**  For the partition matroid of the columns of a
bipartite graph and `t ≥ 0`, the bases of `N(t)` are the bases of the column matroid restricted
to the threshold graph `{D ≤ t}`. -/
theorem isBase_N_iff_restrict {t : ℝ} (ht : 0 ≤ t) (B : Finset (Fin m)) :
    (N (colMatroid col) v t).IsBase (B : Set (Fin m)) ↔
      ((colMatroid col).restrict {f | slack col v f ≤ t}).IsBase (B : Set (Fin m)) := by
  have hE : (colMatroid col).E = Set.univ := colMatroid_ground
  have hT : ∀ e, ∃ g ∈ {f | slack col v f ≤ t}, col g = col e := fun e => by
    obtain ⟨g, hg, h0⟩ := exists_slack_eq_zero col v e
    exact ⟨g, show slack col v g ≤ t by rw [h0]; exact ht, hg⟩
  rw [isBase_restrict_iff hT]
  refine ⟨fun h => ⟨((isBase_N_iff hE).1 h).1, fun f hf =>
    (mem_PO_iff col v f).1 (subset_PO_of_isBase_N hE ht h hf)⟩, fun ⟨hB, hBT⟩ => ?_⟩
  refine (isBase_N_iff hE).2 (Conn.isMinBase_iff_fundCircuit.2 ⟨hB, fun e he f hf => ?_⟩)
  obtain rfl | hfe := eq_or_ne f e
  · exact le_rfl
  have hfB : f ∈ B := Pos.mem_of_mem_fundCircuit hf hfe
  have hcol : col e = col f :=
    connRel_iff.1 (Conn.mem_comp.1 (Conn.fundCircuit_subset_comp hB e hf))
  have hfPO : f ∈ PO (colMatroid col) v t := (mem_PO_iff col v f).2 (hBT (mem_coe.2 hfB))
  by_cases heP : e ∈ PO (colMatroid col) v t
  · have hfs := (slack_le_iff col v).1 ((mem_PO_iff col v f).1 hfPO) e hcol
    have hes := (slack_le_iff col v).1 ((mem_PO_iff col v e).1 heP) f hcol.symm
    have hlink : SameCluster (colMatroid col) (PO (colMatroid col) v t) (near v t) f e :=
      .of_link hfPO heP (connRel_iff.2 hcol.symm) (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
    exact le_of_eq (by exact_mod_cast (u_eq_u_iff ht hfPO heP (connRel_iff.2 hcol.symm)).2 hlink)
  · rw [u_of_notMem heP]
    exact_mod_cast (u_le_iff_mem.2 hfPO).trans (Nat.le_succ m)

end SignedTropical.Rainbow.POSLAssign
