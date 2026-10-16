import SignedTropical.BoolAlg.Path
import SignedTropical.Rainbow.Exchange

/-!
# Bits of the exchange graph

The values of the gadgets of `BoolAlg/Rel.lean` and `BoolAlg/Bits.lean` on the exchange graph of
`Rainbow/Exchange.lean` (Step 3 of the proof of `lem:observer`).  Let the bits `S` mark the
sources, `G` the arcs and `K` the sinks of the exchange graph of `I`.  Then:

* `layerV G S d` marks `layer N blk I d` (`layerV_iff_mem_layer`), so `layersB` computes the
  breadth-first layers, and `layerV G S m` marks `reachSet N blk I` (`layerV_iff_mem_reachSet`);
* a sink lies in some layer if and only if one lies in layer `m`, so the first layer containing a
  sink is at most `m` (`find_sink_layer_le`), and least-index selection over the layers
  `0, …, m` marks it (`leadV_eq_find` of `BoolAlg/Bits.lean`);
* least-index selection among the sinks of a layer marks the sink of least index
  (`leadV_sink_eq`), and among the in-neighbours of `y` in `layer i` it marks
  `leastPred N blk I i y` (`leadV_pred_eq`): the choices of `augStep`;
* the least-index shortest path of `BoolAlg/Path.lean` is the path of `augStep`:
  `predV = leastPred`, `backV = backPath` (`predV_eq_leastPred`, `backV_eq_backPath`), and
  **one round of the augmenting path algorithm** is `augStep N blk I = I ∆ pathSet G S K`
  (`augStep_eq_symmDiff`); in bits, `augStep N blk I` is `I ⊕ pathV G S K` (`augStep_bits`),
  the value of the gadget `exchangeB` (`exchangeB_impl`, `pathCost m + 4m` gates).
-/

namespace SignedTropical.BoolAlg

open Finset SignedTropical.Rainbow.Exchange

variable {m k : ℕ} {N : Matroid (Fin m)} {blk : Fin m → Fin k} {I : Finset (Fin m)}
  {G : Fin m → Fin m → Bool} {S K : Fin m → Bool}

/-- **The layers of the exchange graph**: with `S` marking the sources and `G` the arcs,
`layerV G S d` marks `layer N blk I d`. -/
theorem layerV_iff_mem_layer (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (d : ℕ) (v : Fin m) :
    layerV G S d v = true ↔ v ∈ layer N blk I d := by
  induction d generalizing v with
  | zero => rw [layerV_zero, hS, mem_layer_zero]
  | succ d ih =>
    rw [layerV_succ, mem_layer_succ]
    simp only [bfsStep, Bool.or_eq_true, decide_eq_true_eq, ih, hG]

/-- **The reachable set**: `layerV G S m` marks `reachSet N blk I`. -/
theorem layerV_iff_mem_reachSet (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (v : Fin m) :
    layerV G S m v = true ↔ v ∈ reachSet N blk I := by
  rw [layerV_iff_mem_layer hS hG, reachSet_eq_layer]

open Classical in
/-- The first layer containing a sink is at most `m`. -/
theorem find_sink_layer_le (h : ∃ d, ((layer N blk I d).filter (IsSink N I)).Nonempty) :
    Nat.find h ≤ m := by
  obtain ⟨d, y, hy⟩ := h
  rw [mem_filter] at hy
  exact Nat.find_min' _ ⟨y, mem_filter.2 ⟨layer_subset_layer_card d hy.1, hy.2⟩⟩

open Classical in
/-- **The sink of least index** in a layer: with `S`, `G` and `K` marking the sources, arcs and
sinks, least-index selection among the sinks in `layer d` marks the `min'` of these sinks. -/
theorem leadV_sink_eq (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (hK : ∀ y, K y = true ↔ IsSink N I y)
    {d : ℕ} (hd : ((layer N blk I d).filter (IsSink N I)).Nonempty) (y : Fin m) :
    leadV (fun y => layerV G S d y && K y) y
      = decide (y = ((layer N blk I d).filter (IsSink N I)).min' hd) := by
  have hmem := mem_filter.1 (min'_mem _ hd)
  refine leadV_eq ?_ (fun j hj => ?_) y
  · simp only [Bool.and_eq_true]
    exact ⟨(layerV_iff_mem_layer hS hG d _).2 hmem.1, (hK _).2 hmem.2⟩
  · show (layerV G S d j && K j) = false
    cases hc : (layerV G S d j && K j)
    · rfl
    · rw [Bool.and_eq_true] at hc
      exact absurd (min'_le _ j (mem_filter.2 ⟨(layerV_iff_mem_layer hS hG d j).1 hc.1,
        (hK j).1 hc.2⟩)) (not_le.2 hj)

/-- `leastPred N blk I i y` is at most every in-neighbour of `y` in `layer i`. -/
theorem leastPred_le {i : ℕ} {y u : Fin m} (hu : u ∈ layer N blk I i)
    (huy : Arc N blk I u y) : leastPred N blk I i y ≤ u := by
  classical
  unfold leastPred
  split_ifs with h
  · exact min'_le _ _ (mem_filter.2 ⟨hu, huy⟩)
  · exact absurd ⟨u, mem_filter.2 ⟨hu, huy⟩⟩ h

/-- **The predecessor of least index**: with `S` and `G` marking the sources and arcs,
least-index selection among the in-neighbours of `y` in `layer i` marks
`leastPred N blk I i y`, when `y` lies in `layer (i + 1)` but not in `layer i`. -/
theorem leadV_pred_eq (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) {i : ℕ} {y : Fin m}
    (hy : y ∈ layer N blk I (i + 1)) (hy' : y ∉ layer N blk I i) (u : Fin m) :
    leadV (fun u => layerV G S i u && G u y) u = decide (u = leastPred N blk I i y) := by
  obtain ⟨h₁, h₂⟩ := leastPred_spec hy hy'
  refine leadV_eq ?_ (fun j hj => ?_) u
  · simp only [Bool.and_eq_true]
    exact ⟨(layerV_iff_mem_layer hS hG i _).2 h₁, (hG _ _).2 h₂⟩
  · show (layerV G S i j && G j y) = false
    cases hc : (layerV G S i j && G j y)
    · rfl
    · rw [Bool.and_eq_true] at hc
      exact absurd (leastPred_le ((layerV_iff_mem_layer hS hG i j).1 hc.1) ((hG j y).1 hc.2))
        (not_le.2 hj)

/-! ### One round of the augmenting path algorithm -/

/-- Equal finsets have equal least elements (with a default when empty). -/
theorem dite_min'_eq {s t : Finset (Fin m)} (hst : s = t) (y : Fin m) :
    (if h : s.Nonempty then s.min' h else y) = (if h : t.Nonempty then t.min' h else y) := by
  subst hst; rfl

/-- Equal finsets have equal least elements. -/
theorem min'_eq_of_eq {s t : Finset (Fin m)} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst hst; rfl

/-- The predecessor of least index of `BoolAlg/Path.lean` is `leastPred`. -/
theorem predV_eq_leastPred (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (i : ℕ) (y : Fin m) :
    predV G S i y = leastPred N blk I i y := by
  classical
  unfold predV leastPred
  exact dite_min'_eq (by ext u; simp [layerV_iff_mem_layer hS hG, hG]) y

/-- The path chosen backwards of `BoolAlg/Path.lean` is `backPath`. -/
theorem backV_eq_backPath (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (d : ℕ) (y : Fin m) (i : ℕ) :
    backV G S d y i = backPath N blk I d y i := by
  induction d generalizing y with
  | zero => rfl
  | succ d ih => simp only [backV, backPath, predV_eq_leastPred hS hG, ih]

open Classical in
/-- **One round of the augmenting path algorithm is an exchange along the least-index shortest
path**: with `S`, `G` and `K` marking the sources, arcs and sinks of the exchange graph of `I`,
`augStep N blk I = I ∆ pathSet G S K`. -/
theorem augStep_eq_symmDiff (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (hK : ∀ y, K y = true ↔ IsSink N I y) :
    augStep N blk I = symmDiff I (pathSet G S K) := by
  have hiff : ∀ d, (∃ y, hitV G S K d y = true) ↔
      ((layer N blk I d).filter (IsSink N I)).Nonempty := fun d => by
    simp only [Finset.Nonempty, mem_filter, hitV, Bool.and_eq_true, layerV_iff_mem_layer hS hG, hK]
  unfold augStep pathSet
  by_cases h : Hits G S K
  · have h' : ∃ d, ((layer N blk I d).filter (IsSink N I)).Nonempty :=
      let ⟨d, hd⟩ := h; ⟨d, (hiff d).1 hd⟩
    rw [dif_pos h', dif_pos h]
    have hfind : Nat.find h = Nat.find h' :=
      le_antisymm (Nat.find_mono fun d hd => (hiff d).2 hd)
        (Nat.find_mono fun d hd => (hiff d).1 hd)
    have hy : firstY G S K h =
        ((layer N blk I (Nat.find h')).filter (IsSink N I)).min' (Nat.find_spec h') := by
      unfold firstY
      refine min'_eq_of_eq ?_ _ _
      rw [hfind]
      ext y
      simp [hitV, layerV_iff_mem_layer hS hG, hK]
    rw [hy, hfind]
    congr 2
    funext i
    exact (backV_eq_backPath hS hG _ _ i).symm
  · rw [dif_neg fun ⟨d, hd⟩ => h ⟨d, (hiff d).2 hd⟩, dif_neg h, ← Finset.bot_eq_empty,
      symmDiff_bot]

/-- **One round of the augmenting path algorithm, in bits**: the bits of `augStep N blk I` are
the bits of `I` exclusive-or the output of `pathB` on `(G, S, K)`. -/
theorem augStep_bits (hS : ∀ y, S y = true ↔ IsSource blk I y)
    (hG : ∀ u v, G u v = true ↔ Arc N blk I u v) (hK : ∀ y, K y = true ↔ IsSink N I y)
    (u : Fin m) : decide (u ∈ augStep N blk I) = (decide (u ∈ I) ^^ pathV G S K u) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, augStep_eq_symmDiff hS hG hK, Finset.mem_symmDiff,
    ← pathV_eq_true_iff (G := G) (S := S) (Y := K) u]
  cases pathV G S K u <;> by_cases hu : u ∈ I <;> simp [hu]

end SignedTropical.BoolAlg
