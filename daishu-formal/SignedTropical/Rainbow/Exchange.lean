import SignedTropical.Rainbow.MinBases

/-!
# Exchange graphs and avoidable blocks

`greedy_intersection.tex`, Lemma `lem:avoidable`, and the augmenting path algorithm of matroid
intersection (Lawler; Schrijver, *Combinatorial Optimization*, Theorem 41.2 with
Corollary 39.13a) for a matroid `N : Matroid (Fin m)` and the partition of `Fin m` into the
blocks of `blk : Fin m → Fin k`.  No hypothesis on the ground set of `N` is needed.

The exchange graph of a set `I` (Step 2 of the proof of `lem:avoidable`):

* `Arc N blk I`: arcs `y → x` for `x ∈ I`, `y ∉ I` with `I - x + y` independent in `N`, and
  arcs `x → y` for `x ∈ I`, `y ∉ I` with `blk y = blk x`;
* `IsSource blk I y`: the block of `y` is missed by `I` (so `y ∉ I`, `isSource_iff`);
  `IsSink N I y`: `y ∉ I` and `I + y` is independent;
* `layer N blk I d`: the breadth-first layers, `layer 0` the sources and `layer (d + 1)` the
  layer `d` together with its out-neighbours; `distance N blk I y : ℕ∞`, the least `d` with
  `y ∈ layer d` (`distance_eq_iff`);
* `reachSet N blk I`: the set `R` of elements reachable from a source, equal to `layer m`
  (`reachSet_eq_layer`);
* `IsShortestPath N blk I v n`: `v 0 → ⋯ → v n` is a path on which `v i` has distance exactly
  `i`, that is a path from a source whose length is the distance of its end
  (`isShortestPath_iff`);
* `avOf N blk I`: the blocks missed by `I` together with the blocks of `I ∩ R`.

Results:

* `indep_exchange`: exchange along a path without shortcuts, for any matroid, by induction on
  the number of exchanged pairs.
* `isShortestPath_of_rule`: a path chosen backwards from an element of distance `d` by any rule
  of predecessors in the previous layer is a shortest path; `exists_isShortestPath`.
* `IsShortestPath.augment`: exchanging along a shortest path from a source to a sink of least
  distance gives a rainbow independent set of size `|I| + 1`; `augment` and `augment_of_pred`
  state it in the form a circuit uses, the path chosen backwards from the sink;
  `exists_augment`.
* `augStep`: one round of the augmenting path algorithm with least-index choices (`leastPred`,
  `backPath`); `augStep_spec`.
* `card_eq_nu`, `card_eq_nu_iff`: `|I| = ν(N)` exactly when no sink is reachable.
* `iterate_step`, `iterate_augStep`: `j` rounds of augmentation from `∅` give a rainbow
  independent set with at least `min(j, ν(N))` elements; `card_iterate_augStep`: for `j ≥ ν(N)`,
  in particular `j = k` (`nu_le` of `Rainbow/MinBases.lean`), it has `ν(N)` elements.
* `IsShortestPath.exchange`, `exists_exchange` (Step 3): exchanging along a shortest path from
  a source to `x ∈ I` keeps the size and misses `blk x`.
* `av_eq` (Steps 3 to 6): for a largest `I`, `Av(N)` is the set of blocks missed by `I`
  together with the blocks of `I ∩ R`.
* Lemma `lem:avoidable`, items 1 to 3, written without subtraction: `card_add_nu_le`,
  `card_av_add_nu`, `av_subset`.
-/

open Finset
open scoped symmDiff

namespace SignedTropical.Rainbow.Exchange

/-! ### Exchange along a path without shortcuts -/

section Matroid

variable {α : Type*} {M : Matroid α}

private theorem Iio_add_one_eq_insert (t : ℕ) : Set.Iio (t + 1) = insert t (Set.Iio t) := by
  ext j
  simp only [Set.mem_Iio, Set.mem_insert_iff]
  omega

/-- Two independent sets that contain a common set `K` spanning `y`, and do not contain `y`,
give the same answer to every exchange of `y`: both answers are read off the fundamental
circuit of `y` in `K`. -/
theorem indep_insert_sdiff_iff {J J' K : Set α} (hJ : M.Indep J) (hJ' : M.Indep J')
    (hKJ : K ⊆ J) (hKJ' : K ⊆ J') {y : α} (hy : y ∈ M.closure K) (hyJ : y ∉ J)
    (hyJ' : y ∉ J') (e : α) : M.Indep (insert y J \ {e}) ↔ M.Indep (insert y J' \ {e}) := by
  have hC := (hJ.subset hKJ).fundCircuit_isCircuit hy fun h => hyJ (hKJ h)
  have hsub := M.fundCircuit_subset_insert y K
  rw [← hJ.mem_fundCircuit_iff (M.closure_subset_closure hKJ hy) hyJ,
    ← hJ'.mem_fundCircuit_iff (M.closure_subset_closure hKJ' hy) hyJ',
    ← hC.eq_fundCircuit_of_subset hJ (hsub.trans (Set.insert_subset_insert hKJ)),
    ← hC.eq_fundCircuit_of_subset hJ' (hsub.trans (Set.insert_subset_insert hKJ'))]

/-- **Exchange along a path without shortcuts**, the exchange lemma for shortest paths
(Schrijver, Corollary 39.13a).  Let `J` be independent, and `x i ∈ J`, `y i ∉ J` for `i < t`,
such that `J - x i + y i` is independent for every `i < t` and `J - x i + y j` is dependent
whenever `j < i < t`.  Then `J - {x i : i < t} + {y i : i < t}` is independent.  The proof
exchanges the last pair first and inducts on `t`. -/
theorem indep_exchange {J : Set α} (hJ : M.Indep J) {x y : ℕ → α} {t : ℕ}
    (hx : ∀ i < t, x i ∈ J) (hy : ∀ i < t, y i ∉ J)
    (harc : ∀ i < t, M.Indep (insert (y i) (J \ {x i})))
    (hno : ∀ i < t, ∀ j < i, ¬ M.Indep (insert (y j) (J \ {x i}))) :
    M.Indep (J \ x '' Set.Iio t ∪ y '' Set.Iio t) := by
  induction t generalizing J with
  | zero => simpa using hJ
  | succ t ih =>
    -- exchange the last pair first: no `y j` with `j < t` has an arc to `x t`
    have hxne : ∀ i < t, x i ≠ x t := fun i hi h =>
      hno t (by omega) i hi (h ▸ harc i (by omega))
    have hyne : ∀ i < t, y i ≠ y t := fun i hi h =>
      hno t (by omega) i hi (h ▸ harc t (by omega))
    have hJ' : M.Indep (insert (y t) (J \ {x t})) := harc t (by omega)
    have hyJ' : ∀ i < t, y i ∉ insert (y t) (J \ {x t}) := fun i hi h =>
      (Set.mem_insert_iff.1 h).elim (hyne i hi) fun h => hy i (by omega) h.1
    have hcl : ∀ i < t, y i ∈ M.closure (J \ {x t}) := fun i hi => by
      by_contra h
      refine hno t (by omega) i hi (((hJ.sdiff _).insert_indep_iff_of_notMem
        fun h' => hy i (by omega) h'.1).2 ⟨?_, h⟩)
      exact (harc i (by omega)).subset_ground (Set.mem_insert _ _)
    -- so the arcs among the remaining pairs are the same for `J` and `J - x t + y t`
    have htr : ∀ i < t, ∀ j < t, (M.Indep (insert (y i) (J \ {x j})) ↔
        M.Indep (insert (y i) (insert (y t) (J \ {x t}) \ {x j}))) := fun i hi j hj => by
      have hne : y i ≠ x j := fun h => hy i (by omega) (h ▸ hx j (by omega))
      rw [Set.insert_sdiff_singleton_comm hne, Set.insert_sdiff_singleton_comm hne]
      exact indep_insert_sdiff_iff hJ hJ' Set.sdiff_subset (Set.subset_insert _ _) (hcl i hi)
        (hy i (by omega)) (hyJ' i hi) _
    have hih := ih hJ' (fun i hi => Set.mem_insert_of_mem _ ⟨hx i (by omega), hxne i hi⟩) hyJ'
      (fun i hi => (htr i hi i hi).1 (harc i (by omega)))
      (fun i hi j hj => by rw [← htr j (by omega) i hi]; exact hno i (by omega) j hj)
    have hyx : y t ∉ x '' Set.Iio t := fun ⟨j, hj, h⟩ =>
      hy t (by omega) (h ▸ hx j (Nat.lt_succ_of_lt hj))
    rwa [Set.insert_sdiff_of_notMem _ hyx, Set.sdiff_sdiff, Set.singleton_union,
      Set.insert_union, ← Set.union_insert, ← Set.image_insert_eq, ← Set.image_insert_eq,
      ← Iio_add_one_eq_insert] at hih

end Matroid

/-! ### The exchange graph -/

section Graph

variable {m k : ℕ} (N : Matroid (Fin m)) (blk : Fin m → Fin k) (I : Finset (Fin m))

/-- The arcs of the exchange graph of `I`: `y → x` for `x ∈ I`, `y ∉ I` with `I - x + y`
independent in `N`, and `x → y` for `x ∈ I`, `y ∉ I` with `blk y = blk x`. -/
def Arc (u v : Fin m) : Prop :=
  u ∉ I ∧ v ∈ I ∧ N.Indep (insert u ((I : Set (Fin m)) \ {v})) ∨
    u ∈ I ∧ v ∉ I ∧ blk v = blk u

/-- The sources of the exchange graph: the elements of the blocks missed by `I`. -/
def IsSource (y : Fin m) : Prop := blk y ∉ blocksMet blk I

/-- The sinks of the exchange graph: the `y ∉ I` with `I + y` independent in `N`. -/
def IsSink (y : Fin m) : Prop := y ∉ I ∧ N.Indep (insert y (I : Set (Fin m)))

open Classical in
/-- The breadth-first layers of the exchange graph: `layer 0` is the set of sources, and
`layer (d + 1)` is `layer d` together with the out-neighbours of `layer d`. -/
noncomputable def layer : ℕ → Finset (Fin m)
  | 0 => univ.filter (IsSource blk I)
  | d + 1 => layer d ∪ univ.filter fun v => ∃ u ∈ layer d, Arc N blk I u v

/-- The distance from the sources: the least `d` with `y ∈ layer d`, and `⊤` if there is
none. -/
noncomputable def distance (y : Fin m) : ℕ∞ :=
  ⨅ (d : ℕ) (_ : y ∈ layer N blk I d), (d : ℕ∞)

open Classical in
/-- The set `R` of the elements reachable from a source. -/
noncomputable def reachSet : Finset (Fin m) :=
  univ.filter fun y => ∃ s, IsSource blk I s ∧ Relation.ReflTransGen (Arc N blk I) s y

/-- `v 0 → v 1 → ⋯ → v n` is a path of the exchange graph on which `v i` has distance exactly
`i`: a shortest path from the source `v 0` to `v n`. -/
structure IsShortestPath (v : ℕ → Fin m) (n : ℕ) : Prop where
  arc : ∀ i < n, Arc N blk I (v i) (v (i + 1))
  distance_eq : ∀ i ≤ n, distance N blk I (v i) = i

/-- The blocks missed by `I` together with the blocks of `I ∩ R`: the set `A'` of Step 2 of the
proof of `lem:avoidable`. -/
noncomputable def avOf : Finset (Fin k) :=
  (univ \ blocksMet blk I) ∪ blocksMet blk (I ∩ reachSet N blk I)

variable {N blk I}

theorem IsSource.notMem {y : Fin m} (h : IsSource blk I y) : y ∉ I := fun hy =>
  h (mem_image_of_mem blk hy)

/-- The sources are the `y ∉ I` whose block is missed by `I`. -/
theorem isSource_iff {y : Fin m} : IsSource blk I y ↔ y ∉ I ∧ blk y ∉ blocksMet blk I :=
  ⟨fun h => ⟨h.notMem, h⟩, And.right⟩

theorem Arc.mem_iff {u v : Fin m} (h : Arc N blk I u v) : u ∈ I ↔ v ∉ I := by
  rcases h with ⟨hu, hv, -⟩ | ⟨hu, hv, -⟩ <;> simp [hu, hv]

theorem Arc.mem_blk_eq {u v : Fin m} (h : Arc N blk I u v) (hv : v ∉ I) :
    u ∈ I ∧ blk v = blk u := by
  rcases h with ⟨-, hv', -⟩ | ⟨hu, -, h⟩
  · exact absurd hv' hv
  · exact ⟨hu, h⟩

theorem arc_iff_indep {u v : Fin m} (hu : u ∉ I) (hv : v ∈ I) :
    Arc N blk I u v ↔ N.Indep (insert u ((I : Set (Fin m)) \ {v})) := by
  simp [Arc, hu, hv]

/-! ### Layers, distance and reachability -/

theorem mem_layer_zero {y : Fin m} : y ∈ layer N blk I 0 ↔ IsSource blk I y := by
  simp [layer]

theorem mem_layer_succ {y : Fin m} {d : ℕ} : y ∈ layer N blk I (d + 1) ↔
    y ∈ layer N blk I d ∨ ∃ u ∈ layer N blk I d, Arc N blk I u y := by
  simp [layer]

theorem layer_mono : Monotone (layer N blk I) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_union_left

/-- A predecessor at distance one less: an element of `layer (d + 1)` outside `layer d` has an
in-neighbour in `layer d`. -/
theorem exists_arc_of_mem_layer_succ {y : Fin m} {d : ℕ} (h : y ∈ layer N blk I (d + 1))
    (h' : y ∉ layer N blk I d) : ∃ u ∈ layer N blk I d, Arc N blk I u y :=
  (mem_layer_succ.1 h).resolve_left h'

theorem le_distance_iff {y : Fin m} {d : ℕ} :
    (d : ℕ∞) ≤ distance N blk I y ↔ ∀ j < d, y ∉ layer N blk I j := by
  refine ⟨fun h j hj hy => ?_, fun h => le_iInf₂ fun j hj => ?_⟩
  · exact absurd (ENat.coe_le_coe.1 (h.trans (iInf₂_le j hy))) (by omega)
  · exact ENat.coe_le_coe.2 (not_lt.1 fun hlt => h j hlt hj)

theorem distance_le_iff {y : Fin m} {d : ℕ} :
    distance N blk I y ≤ d ↔ y ∈ layer N blk I d := by
  refine ⟨fun h => ?_, fun h => iInf₂_le d h⟩
  by_contra hy
  have := (le_distance_iff (d := d + 1)).2 fun j hj hj' => hy (layer_mono (by omega) hj')
  exact absurd (ENat.coe_le_coe.1 (this.trans h)) (by omega)

theorem distance_eq_iff {y : Fin m} {d : ℕ} :
    distance N blk I y = d ↔ y ∈ layer N blk I d ∧ ∀ j < d, y ∉ layer N blk I j := by
  rw [← distance_le_iff, ← le_distance_iff, le_antisymm_iff]

theorem mem_reachSet {y : Fin m} : y ∈ reachSet N blk I ↔
    ∃ s, IsSource blk I s ∧ Relation.ReflTransGen (Arc N blk I) s y := by
  simp [reachSet]

theorem mem_reachSet_iff_exists_layer {y : Fin m} :
    y ∈ reachSet N blk I ↔ ∃ d, y ∈ layer N blk I d := by
  rw [mem_reachSet]
  constructor
  · rintro ⟨s, hs, h⟩
    induction h with
    | refl => exact ⟨0, mem_layer_zero.2 hs⟩
    | tail _ huy ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + 1, mem_layer_succ.2 (Or.inr ⟨_, hd, huy⟩)⟩
  · rintro ⟨d, hd⟩
    induction d generalizing y with
    | zero => exact ⟨y, mem_layer_zero.1 hd, .refl⟩
    | succ d ih =>
      rcases mem_layer_succ.1 hd with hd | ⟨u, hu, huy⟩
      · exact ih hd
      · obtain ⟨s, hs, h⟩ := ih hu
        exact ⟨s, hs, h.tail huy⟩

theorem distance_lt_top_iff {y : Fin m} : distance N blk I y < ⊤ ↔ y ∈ reachSet N blk I := by
  rw [mem_reachSet_iff_exists_layer]
  refine ⟨fun h => ?_, fun ⟨d, hd⟩ => (distance_le_iff.2 hd).trans_lt (ENat.coe_lt_top d)⟩
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 h.ne
  exact ⟨d, distance_le_iff.1 hd.ge⟩

theorem layer_succ_congr {d e : ℕ} (h : layer N blk I d = layer N blk I e) :
    layer N blk I (d + 1) = layer N blk I (e + 1) := by
  ext y; simp only [mem_layer_succ, h]

/-- The layers stabilize by the `m`-th. -/
theorem layer_subset_layer_card (d : ℕ) : layer N blk I d ⊆ layer N blk I m := by
  obtain ⟨j, hj, hjeq⟩ : ∃ j ≤ m, layer N blk I (j + 1) = layer N blk I j := by
    by_contra! h
    have hcard : ∀ j ≤ m + 1, j ≤ (layer N blk I j).card := by
      intro j hj
      induction j with
      | zero => exact Nat.zero_le _
      | succ j ih =>
        refine Nat.succ_le_of_lt ((ih (by omega)).trans_lt (card_lt_card ?_))
        exact Finset.ssubset_iff_subset_ne.2 ⟨layer_mono j.le_succ, (h j (by omega)).symm⟩
    have := (hcard (m + 1) le_rfl).trans (card_le_univ _)
    simp at this
  have hstab : ∀ i, layer N blk I (j + i) = layer N blk I j := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => exact (layer_succ_congr ih).trans hjeq
  rcases le_total d j with hdj | hjd
  · exact layer_mono (hdj.trans hj)
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjd
    rw [hstab]
    exact layer_mono hj

/-- The reachable set is the `m`-th breadth-first layer. -/
theorem reachSet_eq_layer : reachSet N blk I = layer N blk I m := by
  ext y
  rw [mem_reachSet_iff_exists_layer]
  exact ⟨fun ⟨d, hd⟩ => layer_subset_layer_card d hd, fun h => ⟨m, h⟩⟩

theorem mem_reachSet_of_isSource {y : Fin m} (h : IsSource blk I y) : y ∈ reachSet N blk I :=
  mem_reachSet.2 ⟨y, h, .refl⟩

theorem mem_reachSet_of_arc {u y : Fin m} (hu : u ∈ reachSet N blk I) (h : Arc N blk I u y) :
    y ∈ reachSet N blk I := by
  obtain ⟨s, hs, hsu⟩ := mem_reachSet.1 hu
  exact mem_reachSet.2 ⟨s, hs, hsu.tail h⟩

/-! ### Shortest paths -/

/-- A path chosen backwards from an element `v n` of distance exactly `n`, each `v i` an
in-neighbour of `v (i + 1)` in `layer i`, is a shortest path. -/
theorem isShortestPath_of_pred {v : ℕ → Fin m} {n : ℕ} (hn : v n ∈ layer N blk I n)
    (hmin : ∀ j < n, v n ∉ layer N blk I j)
    (hpred : ∀ i < n, v i ∈ layer N blk I i ∧ Arc N blk I (v i) (v (i + 1))) :
    IsShortestPath N blk I v n := by
  have key : ∀ l i, i + l = n → ∀ j < i, v i ∉ layer N blk I j := by
    intro l
    induction l with
    | zero => intro i hi; rw [Nat.add_zero] at hi; subst hi; exact hmin
    | succ l ih =>
      intro i hil j hj hvj
      exact ih (i + 1) (by omega) (j + 1) (by omega)
        (mem_layer_succ.2 (Or.inr ⟨v i, hvj, (hpred i (by omega)).2⟩))
  refine ⟨fun i hi => (hpred i hi).2, fun i hi => distance_eq_iff.2 ⟨?_, key (n - i) i (by omega)⟩⟩
  rcases hi.lt_or_eq with hi | rfl
  · exact (hpred i hi).1
  · exact hn

/-- **A path chosen backwards by a rule is a shortest path.**  Let `pred i y` be an
in-neighbour of `y` in `layer i` whenever `y` lies in `layer (i + 1)` but not in `layer i` (any
rule, for instance `leastPred`).  If `v d` has distance exactly `d` and `v i = pred i (v (i + 1))`
for `i < d`, then `v 0 → ⋯ → v d` is a shortest path. -/
theorem isShortestPath_of_rule (pred : ℕ → Fin m → Fin m)
    (hpred : ∀ i y, y ∈ layer N blk I (i + 1) → y ∉ layer N blk I i →
      pred i y ∈ layer N blk I i ∧ Arc N blk I (pred i y) y)
    {d : ℕ} {v : ℕ → Fin m} (hd : v d ∈ layer N blk I d) (hmin : ∀ j < d, v d ∉ layer N blk I j)
    (hv : ∀ i < d, v i = pred i (v (i + 1))) : IsShortestPath N blk I v d := by
  -- going down from `v d`, each `v (d - l)` lies in `layer (d - l)` and in no earlier layer
  have key : ∀ l ≤ d, v (d - l) ∈ layer N blk I (d - l) ∧
      ∀ j < d - l, v (d - l) ∉ layer N blk I j := by
    intro l hl
    induction l with
    | zero => exact ⟨hd, hmin⟩
    | succ l ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [show d - l = d - (l + 1) + 1 by omega] at h1 h2
      rw [hv _ (by omega)]
      obtain ⟨hp1, hp2⟩ := hpred _ _ h1 (h2 _ (by omega))
      exact ⟨hp1, fun j hj hj' => h2 (j + 1) (by omega) (mem_layer_succ.2 (Or.inr ⟨_, hj', hp2⟩))⟩
  refine isShortestPath_of_pred hd hmin fun i hi => ?_
  obtain ⟨h1, h2⟩ := key (d - (i + 1)) (by omega)
  rw [show d - (d - (i + 1)) = i + 1 by omega] at h1 h2
  rw [hv i hi]
  exact hpred i _ h1 (h2 i (by omega))

variable (N blk I) in
open Classical in
/-- The in-neighbour of `y` in `layer i` of least index (and `y` if there is none): a rule of
predecessors for `isShortestPath_of_rule` (`leastPred_spec`). -/
noncomputable def leastPred (i : ℕ) (y : Fin m) : Fin m :=
  if h : ((layer N blk I i).filter fun u => Arc N blk I u y).Nonempty then
    ((layer N blk I i).filter fun u => Arc N blk I u y).min' h else y

theorem leastPred_spec {i : ℕ} {y : Fin m} (h : y ∈ layer N blk I (i + 1))
    (h' : y ∉ layer N blk I i) :
    leastPred N blk I i y ∈ layer N blk I i ∧ Arc N blk I (leastPred N blk I i y) y := by
  classical
  obtain ⟨u, hu, huy⟩ := exists_arc_of_mem_layer_succ h h'
  have hne : ((layer N blk I i).filter fun u => Arc N blk I u y).Nonempty :=
    ⟨u, mem_filter.2 ⟨hu, huy⟩⟩
  simp only [leastPred, dif_pos hne]
  exact mem_filter.1 (min'_mem _ hne)

variable (N blk I) in
/-- The path chosen backwards from `y` by `leastPred`: `backPath d y d = y` and
`backPath d y i = leastPred i (backPath d y (i + 1))` for `i < d` (`backPath_self`,
`backPath_pred`). -/
noncomputable def backPath : ℕ → Fin m → ℕ → Fin m
  | 0, y, _ => y
  | d + 1, y, i => if i ≤ d then backPath d (leastPred N blk I d y) i else y

theorem backPath_self (d : ℕ) (y : Fin m) : backPath N blk I d y d = y := by
  cases d <;> simp [backPath]

theorem backPath_pred {d i : ℕ} (hi : i < d) (y : Fin m) :
    backPath N blk I d y i = leastPred N blk I i (backPath N blk I d y (i + 1)) := by
  induction d generalizing y with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ d ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simp only [backPath, if_pos hi.le, if_pos (show i + 1 ≤ d by omega)]
      exact ih hi _
    · simp [backPath, backPath_self]

/-- Every element `y` of distance exactly `d` is the end of a shortest path of length `d`,
`backPath d y`. -/
theorem exists_isShortestPath {y : Fin m} {d : ℕ} (hd : y ∈ layer N blk I d)
    (hmin : ∀ j < d, y ∉ layer N blk I j) :
    ∃ v : ℕ → Fin m, v d = y ∧ IsShortestPath N blk I v d :=
  ⟨backPath N blk I d y, backPath_self d y, isShortestPath_of_rule (leastPred N blk I)
    (fun _ _ => leastPred_spec) (by rwa [backPath_self]) (by rwa [backPath_self])
    fun i hi => backPath_pred hi y⟩

theorem exists_isShortestPath_of_mem_reachSet {y : Fin m} (hy : y ∈ reachSet N blk I) :
    ∃ (v : ℕ → Fin m) (n : ℕ), v n = y ∧ IsShortestPath N blk I v n := by
  classical
  have h := mem_reachSet_iff_exists_layer.1 hy
  obtain ⟨v, hv, hsp⟩ := exists_isShortestPath (Nat.find_spec h) fun j hj => Nat.find_min h hj
  exact ⟨v, _, hv, hsp⟩

namespace IsShortestPath

variable {v : ℕ → Fin m} {n : ℕ}

theorem mem_layer (hv : IsShortestPath N blk I v n) {i : ℕ} (hi : i ≤ n) :
    v i ∈ layer N blk I i :=
  (distance_eq_iff.1 (hv.distance_eq i hi)).1

theorem notMem_layer (hv : IsShortestPath N blk I v n) {i j : ℕ} (hi : i ≤ n) (hj : j < i) :
    v i ∉ layer N blk I j :=
  (distance_eq_iff.1 (hv.distance_eq i hi)).2 j hj

theorem isSource (hv : IsShortestPath N blk I v n) : IsSource blk I (v 0) :=
  mem_layer_zero.1 (hv.mem_layer n.zero_le)

theorem injOn (hv : IsShortestPath N blk I v n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (h : v i = v j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hv.notMem_layer hj hlt (h ▸ hv.mem_layer hi)
  · exact hv.notMem_layer hi hlt (h ▸ hv.mem_layer hj)

/-- No shortcuts: there is no arc `v j → v i` with `j + 1 < i`. -/
theorem not_arc (hv : IsShortestPath N blk I v n) {i j : ℕ} (hi : i ≤ n) (hji : j + 1 < i) :
    ¬ Arc N blk I (v j) (v i) := fun h =>
  hv.notMem_layer hi hji (mem_layer_succ.2 (Or.inr ⟨v j, hv.mem_layer (by omega), h⟩))

/-- The path alternates between the outside of `I` and `I`, starting outside. -/
theorem mem_iff (hv : IsShortestPath N blk I v n) {i : ℕ} (hi : i ≤ n) :
    v i ∈ I ↔ i % 2 = 1 := by
  induction i with
  | zero => simpa using hv.isSource.notMem
  | succ i ih =>
    rw [← not_iff_not, ← (hv.arc i (by omega)).mem_iff, ih (by omega)]
    omega

theorem image_inter (hv : IsShortestPath N blk I v n) :
    (range (n + 1)).image v ∩ I = (range ((n + 1) / 2)).image fun i => v (2 * i + 1) := by
  ext e
  simp only [mem_inter, mem_image, mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, he⟩
    have := (hv.mem_iff (by omega)).1 he
    exact ⟨i / 2, by omega, by congr 1; omega⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨2 * i + 1, by omega, rfl⟩, (hv.mem_iff (by omega)).2 (by omega)⟩

theorem image_sdiff (hv : IsShortestPath N blk I v n) :
    (range (n + 1)).image v \ I = (range (n / 2 + 1)).image fun i => v (2 * i) := by
  ext e
  simp only [mem_sdiff, mem_image, mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, he⟩
    have := (hv.mem_iff (by omega)).not.1 he
    exact ⟨i / 2, by omega, by congr 1; omega⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨2 * i, by omega, rfl⟩, fun h => by have := (hv.mem_iff (by omega)).1 h; omega⟩

theorem coe_symmDiff (hv : IsShortestPath N blk I v n) :
    ((I ∆ (range (n + 1)).image v : Finset (Fin m)) : Set (Fin m)) =
      (I : Set (Fin m)) \ (fun i => v (2 * i + 1)) '' Set.Iio ((n + 1) / 2) ∪
        (fun i => v (2 * i)) '' Set.Iio (n / 2 + 1) := by
  rw [Finset.symmDiff_def, ← sdiff_inter_self_right I, hv.image_inter, hv.image_sdiff]
  simp only [coe_union, coe_sdiff, coe_image, coe_range]

theorem card_symmDiff (hv : IsShortestPath N blk I v n) :
    (I ∆ (range (n + 1)).image v).card + (n + 1) / 2 = I.card + (n / 2 + 1) := by
  have hX : ((range ((n + 1) / 2)).image fun i => v (2 * i + 1)).card = (n + 1) / 2 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := hv.injOn (by omega) (by omega) h
    omega
  have hY : ((range (n / 2 + 1)).image fun i => v (2 * i)).card = n / 2 + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := hv.injOn (by omega) (by omega) h
    omega
  have h := card_sdiff_add_card_inter I ((range (n + 1)).image v)
  rw [inter_comm, hv.image_inter, hX] at h
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff, hv.image_sdiff, hY]
  omega

/-- The rainbow half of the exchange: every element of the path outside `I`, other than the
source, has the block of its predecessor, which lies in `I`. -/
theorem isRainbow_symmDiff (hv : IsShortestPath N blk I v n) (hI : IsRainbow blk I) :
    IsRainbow blk (I ∆ (range (n + 1)).image v) := by
  have key : ∀ e ∈ (range (n + 1)).image v, e ∉ I →
      e = v 0 ∨ ∃ i < n, e = v (i + 1) ∧ v i ∈ I ∧ blk e = blk (v i) := by
    simp only [mem_image, mem_range]
    rintro e ⟨i, hi, rfl⟩ he
    rcases i with _ | i
    · exact Or.inl rfl
    · exact Or.inr ⟨i, by omega, rfl, (hv.arc i (by omega)).mem_blk_eq he⟩
  have hsrc : blk (v 0) ∉ blocksMet blk I := hv.isSource
  have hmet : ∀ x ∈ I, blk x ∈ blocksMet blk I := fun x hx => mem_image_of_mem blk hx
  have hP : ∀ i ≤ n, v i ∈ (range (n + 1)).image v := fun i hi =>
    mem_image_of_mem v (mem_range.2 (by omega))
  have hne : ∀ a ∈ I, a ∉ (range (n + 1)).image v → ∀ b ∈ (range (n + 1)).image v, b ∉ I →
      blk a ≠ blk b := by
    intro a ha haP b hbP hb hab
    rcases key b hbP hb with rfl | ⟨i, hi, rfl, hvi, hblk⟩
    · exact hsrc (hab ▸ hmet a ha)
    · exact haP (hI ha hvi (hab.trans hblk) ▸ hP i (by omega))
  intro a ha b hb hab
  simp only [mem_coe, mem_symmDiff] at ha hb
  rcases ha with ⟨ha, haP⟩ | ⟨haP, ha⟩ <;> rcases hb with ⟨hb, hbP⟩ | ⟨hbP, hb⟩
  · exact hI ha hb hab
  · exact absurd hab (hne a ha haP b hbP hb)
  · exact absurd hab.symm (hne b hb hbP a haP ha)
  · rcases key a haP ha with rfl | ⟨i, hi, rfl, hvi, hai⟩ <;>
      rcases key b hbP hb with rfl | ⟨j, hj, rfl, hvj, hbj⟩
    · rfl
    · exact absurd (hab.trans hbj ▸ hmet _ hvj) hsrc
    · exact absurd (hab.symm.trans hai ▸ hmet _ hvi) hsrc
    · rw [hv.injOn (by omega) (by omega) (hI hvi hvj (hai.symm.trans (hab.trans hbj)))]

/-- The matroid half of the exchange along a shortest path from a source to an element of
`I`. -/
theorem indep_symmDiff_of_mem (hv : IsShortestPath N blk I v n) (hI : N.Indep (I : Set (Fin m)))
    (hn : v n ∈ I) : N.Indep ((I ∆ (range (n + 1)).image v : Finset (Fin m)) : Set (Fin m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 1 := ⟨n / 2, by have := (hv.mem_iff le_rfl).1 hn; omega⟩
  rw [hv.coe_symmDiff, show (2 * s + 1 + 1) / 2 = s + 1 by omega,
    show (2 * s + 1) / 2 + 1 = s + 1 by omega]
  have hx : ∀ i < s + 1, v (2 * i + 1) ∈ I := fun i hi => (hv.mem_iff (by omega)).2 (by omega)
  have hy : ∀ i < s + 1, v (2 * i) ∉ I := fun i hi h => by
    have := (hv.mem_iff (by omega)).1 h; omega
  exact indep_exchange hI hx hy
    (fun i hi => (arc_iff_indep (hy i hi) (hx i hi)).1 (hv.arc (2 * i) (by omega)))
    (fun i hi j hj => (arc_iff_indep (hy j (by omega)) (hx i hi)).not.1
      (hv.not_arc (by omega) (by omega)))

/-- The matroid half of the augmentation along a shortest path from a source to a sink, when no
earlier element of the path is a sink. -/
theorem indep_symmDiff_of_sink (hv : IsShortestPath N blk I v n) (hI : N.Indep (I : Set (Fin m)))
    (hsink : IsSink N I (v n)) (hns : ∀ i < n, ¬ IsSink N I (v i)) :
    N.Indep ((I ∆ (range (n + 1)).image v : Finset (Fin m)) : Set (Fin m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s :=
    ⟨n / 2, by have := (hv.mem_iff le_rfl).not.1 hsink.1; omega⟩
  have hsE := (hI.insert_indep_iff_of_notMem hsink.1).1 hsink.2
  have hx : ∀ i < s, v (2 * i + 1) ∈ I := fun i hi => (hv.mem_iff (by omega)).2 (by omega)
  have hy : ∀ i < s, v (2 * i) ∉ I := fun i hi h => by
    have := (hv.mem_iff (by omega)).1 h; omega
  have hyn : ∀ i < s, v (2 * i) ≠ v (2 * s) := fun i hi h => by
    have := hv.injOn (by omega) le_rfl h; omega
  have hxn : ∀ i < s, v (2 * s) ≠ v (2 * i + 1) := fun i hi h => hsink.1 (h ▸ hx i hi)
  -- `J = I + v n`; its arcs are those of `I`, since `v n` is not spanned by `I`
  have harc : ∀ i < s, N.Indep (insert (v (2 * i))
      (insert (v (2 * s)) (I : Set (Fin m)) \ {v (2 * i + 1)})) := fun i hi => by
    have h := (arc_iff_indep (hy i hi) (hx i hi)).1 (hv.arc (2 * i) (by omega))
    have hcl : v (2 * i) ∈ N.closure I := by
      by_contra hc
      exact hns (2 * i) (by omega) ⟨hy i hi, (hI.insert_indep_iff_of_notMem (hy i hi)).2
        ⟨h.subset_ground (Set.mem_insert _ _), hc⟩⟩
    rw [← Set.insert_sdiff_singleton_comm (hxn i hi), Set.insert_comm]
    refine (h.insert_indep_iff_of_notMem ?_).2 ⟨hsE.1, fun hc => hsE.2 ?_⟩
    · rintro (h' | h')
      · exact hyn i hi h'.symm
      · exact hsink.1 h'.1
    · exact N.closure_subset_closure_of_subset_closure (Set.insert_subset hcl
        (Set.sdiff_subset.trans (N.subset_closure _ hI.subset_ground))) hc
  have hno : ∀ i < s, ∀ j < i, ¬ N.Indep (insert (v (2 * j))
      (insert (v (2 * s)) (I : Set (Fin m)) \ {v (2 * i + 1)})) := fun i hi j hj h =>
    (arc_iff_indep (hy j (by omega)) (hx i hi)).not.1 (hv.not_arc (by omega) (by omega))
      (h.subset (Set.insert_subset_insert (Set.sdiff_subset_sdiff_left (Set.subset_insert _ _))))
  have h := indep_exchange (x := fun i => v (2 * i + 1)) (y := fun i => v (2 * i)) hsink.2
    (fun i hi => Set.mem_insert_of_mem _ (hx i hi))
    (fun i hi h => (Set.mem_insert_iff.1 h).elim (hyn i hi) (hy i hi)) harc hno
  have hvx : v (2 * s) ∉ (fun i => v (2 * i + 1)) '' Set.Iio s := fun ⟨j, hj, h⟩ =>
    hxn j hj h.symm
  rw [Set.insert_sdiff_of_notMem _ hvx, Set.insert_union, ← Set.union_insert] at h
  rwa [hv.coe_symmDiff, show (2 * s + 1) / 2 = s by omega, show 2 * s / 2 + 1 = s + 1 by omega,
    Iio_add_one_eq_insert, Set.image_insert_eq]

/-- **Augmentation along a shortest path** (Lawler; Schrijver, Theorem 41.2 with
Corollary 39.13a).  Let `I` be rainbow independent and `v 0 → ⋯ → v n` a path from a source
to a sink on which `v i` has distance exactly `i`, with `n` least among the distances of the
sinks.  Then removing the path's elements of `I` and adding its elements outside `I` gives a
rainbow independent set `I ∆ {v 0, …, v n}` of size `|I| + 1`. -/
theorem augment (hv : IsShortestPath N blk I v n) (hI : IsRainbowIndep N blk I)
    (hsink : IsSink N I (v n)) (hmin : ∀ y, IsSink N I y → (n : ℕ∞) ≤ distance N blk I y) :
    IsRainbowIndep N blk (I ∆ (range (n + 1)).image v) ∧
      (I ∆ (range (n + 1)).image v).card = I.card + 1 := by
  have hns : ∀ i < n, ¬ IsSink N I (v i) := fun i hi hs =>
    le_distance_iff.1 (hmin _ hs) i hi (hv.mem_layer hi.le)
  have hpar := (hv.mem_iff le_rfl).not.1 hsink.1
  refine ⟨⟨hv.indep_symmDiff_of_sink hI.1 hsink hns, hv.isRainbow_symmDiff hI.2⟩, ?_⟩
  have := hv.card_symmDiff
  omega

/-- **Step 3 of the proof of `lem:avoidable`.**  For a rainbow independent `I`, exchanging along
a shortest path from a source `v 0` to an element `v n` of `I` gives a rainbow independent set
`I ∆ {v 0, …, v n}` of size `|I|` that meets the block of the source and misses the block of
`v n`. -/
theorem exchange (hv : IsShortestPath N blk I v n) (hI : IsRainbowIndep N blk I) (hn : v n ∈ I) :
    IsRainbowIndep N blk (I ∆ (range (n + 1)).image v) ∧
      (I ∆ (range (n + 1)).image v).card = I.card ∧
      blk (v 0) ∈ blocksMet blk (I ∆ (range (n + 1)).image v) ∧
      blk (v n) ∉ blocksMet blk (I ∆ (range (n + 1)).image v) := by
  have hpar := (hv.mem_iff le_rfl).1 hn
  refine ⟨⟨hv.indep_symmDiff_of_mem hI.1 hn, hv.isRainbow_symmDiff hI.2⟩, ?_,
    mem_image_of_mem blk (mem_symmDiff.2 (Or.inr ⟨mem_image_of_mem v (mem_range.2 (by omega)),
      hv.isSource.notMem⟩)), ?_⟩
  · have := hv.card_symmDiff
    omega
  · rw [blocksMet, mem_image]
    rintro ⟨e, he, hblk⟩
    rcases mem_symmDiff.1 he with ⟨he, heP⟩ | ⟨heP, he⟩
    · rw [hI.2 he hn hblk] at heP
      exact heP (mem_image_of_mem v (mem_range.2 (by omega)))
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 heP
      rw [mem_range] at hi
      rcases i with _ | i
      · exact hv.isSource (hblk ▸ mem_image_of_mem blk hn)
      · obtain ⟨hvi, hb⟩ := (hv.arc i (by omega)).mem_blk_eq he
        have := hv.injOn (by omega) le_rfl (hI.2 hvi hn (hb.symm.trans hblk))
        omega

end IsShortestPath

/-- A shortest path is a path from a source whose length is the distance of its end. -/
theorem isShortestPath_iff {v : ℕ → Fin m} {n : ℕ} : IsShortestPath N blk I v n ↔
    IsSource blk I (v 0) ∧ (∀ i < n, Arc N blk I (v i) (v (i + 1))) ∧
      distance N blk I (v n) = n := by
  refine ⟨fun hv => ⟨hv.isSource, hv.arc, hv.distance_eq n le_rfl⟩, fun ⟨h0, harc, hn⟩ => ?_⟩
  -- following the path from an element of `layer j` for `l` steps stays in `layer (j + l)`
  have hfol : ∀ i j l, i + l ≤ n → v i ∈ layer N blk I j → v (i + l) ∈ layer N blk I (j + l) := by
    intro i j l hl hij
    induction l with
    | zero => exact hij
    | succ l ih => exact mem_layer_succ.2 (Or.inr ⟨_, ih (by omega), harc (i + l) (by omega)⟩)
  rw [distance_eq_iff] at hn
  refine ⟨harc, fun i hi => distance_eq_iff.2 ⟨?_, fun j hj hij => ?_⟩⟩
  · simpa using hfol 0 0 i (by omega) (mem_layer_zero.2 h0)
  · have := hfol i j (n - i) (by omega) hij
    rw [show i + (n - i) = n by omega] at this
    exact hn.2 (j + (n - i)) (by omega) this

/-- **Augmentation, in the form a circuit uses.**  Let `I` be rainbow independent and `v d` a
sink in `layer d` such that no sink lies in an earlier layer, and choose the path backwards
from it, each `v i` (`i < d`) an in-neighbour of `v (i + 1)` lying in `layer i` (any choice,
for instance the least index).  Then `I ∆ {v 0, …, v d}` is rainbow independent of size
`|I| + 1`. -/
theorem augment {d : ℕ} {v : ℕ → Fin m} (hI : IsRainbowIndep N blk I)
    (hsink : IsSink N I (v d)) (hd : v d ∈ layer N blk I d)
    (hmin : ∀ y, IsSink N I y → ∀ j < d, y ∉ layer N blk I j)
    (hpred : ∀ i < d, v i ∈ layer N blk I i ∧ Arc N blk I (v i) (v (i + 1))) :
    IsRainbowIndep N blk (I ∆ (range (d + 1)).image v) ∧
      (I ∆ (range (d + 1)).image v).card = I.card + 1 :=
  (isShortestPath_of_pred hd (hmin _ hsink) hpred).augment hI hsink fun y hy =>
    le_distance_iff.2 (hmin y hy)

/-- **Augmentation with the predecessors chosen by a rule.**  Let `I` be rainbow independent
and let `pred i y` be an in-neighbour of `y` in `layer i` whenever `y` lies in `layer (i + 1)`
but not in `layer i` (any rule, for instance the least index, `leastPred`).  Let `v d` be a
sink in `layer d` such that no sink lies in an earlier layer, and `v i = pred i (v (i + 1))`
for `i < d`.  Then `I ∆ {v 0, …, v d}` is rainbow independent of size `|I| + 1`. -/
theorem augment_of_pred (pred : ℕ → Fin m → Fin m)
    (hpred : ∀ i y, y ∈ layer N blk I (i + 1) → y ∉ layer N blk I i →
      pred i y ∈ layer N blk I i ∧ Arc N blk I (pred i y) y)
    {d : ℕ} {v : ℕ → Fin m} (hI : IsRainbowIndep N blk I)
    (hsink : IsSink N I (v d)) (hd : v d ∈ layer N blk I d)
    (hmin : ∀ y, IsSink N I y → ∀ j < d, y ∉ layer N blk I j)
    (hv : ∀ i < d, v i = pred i (v (i + 1))) :
    IsRainbowIndep N blk (I ∆ (range (d + 1)).image v) ∧
      (I ∆ (range (d + 1)).image v).card = I.card + 1 :=
  (isShortestPath_of_rule pred hpred hd (hmin _ hsink) hv).augment hI hsink fun y hy =>
    le_distance_iff.2 (hmin y hy)

variable (N blk I) in
open Classical in
/-- One round of the augmenting path algorithm, with least-index choices.  If some layer
contains a sink, let `d` be the least such layer and `y` the sink of least index in `layer d`;
the round returns `I ∆ {v 0, …, v d}` for the path `v = backPath d y`.  Otherwise it returns
`I`. -/
noncomputable def augStep : Finset (Fin m) :=
  if h : ∃ d, ((layer N blk I d).filter (IsSink N I)).Nonempty then
    I ∆ (range (Nat.find h + 1)).image (backPath N blk I (Nat.find h)
      (((layer N blk I (Nat.find h)).filter (IsSink N I)).min' (Nat.find_spec h)))
  else I

/-- One round keeps `I` rainbow independent and does not decrease its size; it adds one element
when a sink is reachable from a source. -/
theorem augStep_spec (hI : IsRainbowIndep N blk I) :
    IsRainbowIndep N blk (augStep N blk I) ∧ I.card ≤ (augStep N blk I).card ∧
      ((∃ y ∈ reachSet N blk I, IsSink N I y) → (augStep N blk I).card = I.card + 1) := by
  classical
  unfold augStep
  split_ifs with h
  · have hmin : ∀ y, IsSink N I y → ∀ j < Nat.find h, y ∉ layer N blk I j :=
      fun y hy j hj hyj => Nat.find_min h hj ⟨y, mem_filter.2 ⟨hyj, hy⟩⟩
    have hy := min'_mem _ (Nat.find_spec h)
    generalize ((layer N blk I (Nat.find h)).filter (IsSink N I)).min' (Nat.find_spec h) = y
      at hy ⊢
    obtain ⟨h1, h2⟩ := augment_of_pred (v := backPath N blk I (Nat.find h) y) (leastPred N blk I)
      (fun _ _ => leastPred_spec) hI (by rw [backPath_self]; exact (mem_filter.1 hy).2)
      (by rw [backPath_self]; exact (mem_filter.1 hy).1) hmin fun i hi => backPath_pred hi y
    exact ⟨h1, by omega, fun _ => h2⟩
  · refine ⟨hI, le_rfl, fun ⟨y, hy, hs⟩ => absurd ?_ h⟩
    obtain ⟨d, hd⟩ := mem_reachSet_iff_exists_layer.1 hy
    exact ⟨d, y, mem_filter.2 ⟨hd, hs⟩⟩

/-- If a sink of the exchange graph of a rainbow independent `I` is reachable from a source,
there is a rainbow independent set of size `|I| + 1`. -/
theorem exists_augment (hI : IsRainbowIndep N blk I)
    (h : ∃ y ∈ reachSet N blk I, IsSink N I y) :
    ∃ J, IsRainbowIndep N blk J ∧ J.card = I.card + 1 :=
  ⟨_, (augStep_spec hI).1, (augStep_spec hI).2.2 h⟩

end Graph

/-! ### Largest rainbow independent sets and avoidable blocks -/

section Avoidable

variable {m k : ℕ} {N : Matroid (Fin m)} {blk : Fin m → Fin k} {I : Finset (Fin m)}

theorem isRainbowIndep_empty (N : Matroid (Fin m)) (blk : Fin m → Fin k) :
    IsRainbowIndep N blk ∅ :=
  ⟨by simp, by simp [IsRainbow]⟩

/-- Steps 1 and 5 of the proof of `lem:avoidable`: a rainbow independent `J` has at most
`r_N(E_Q)` elements in `E_Q`, and its other elements lie in distinct blocks, none in `Q` and
none missed by `J`.  So `|J| + |Q ∪ M_J| ≤ k + r_N(E_Q)`, where `M_J` is the set of blocks
missed by `J`. -/
theorem card_add_card_le {J : Finset (Fin m)} (hJ : IsRainbowIndep N blk J)
    (Q : Finset (Fin k)) :
    J.card + (Q ∪ (univ \ blocksMet blk J)).card ≤ k + rk N (blockSet blk Q) := by
  have h1 : (J ∩ blockSet blk Q).card ≤ rk N (blockSet blk Q) :=
    card_le_rk N (hJ.1.subset (coe_subset.2 inter_subset_left)) inter_subset_right
  have h2 : (J \ blockSet blk Q).card + (Q ∪ (univ \ blocksMet blk J)).card ≤ k := by
    rw [← card_image_of_injOn (hJ.2.mono (coe_subset.2 sdiff_subset)),
      ← card_union_of_disjoint]
    · simpa using card_le_univ ((J \ blockSet blk Q).image blk ∪ (Q ∪ (univ \ blocksMet blk J)))
    · rw [disjoint_left]
      simp only [mem_image, mem_sdiff, blockSet, mem_filter, mem_univ, true_and, mem_union,
        blocksMet]
      rintro _ ⟨e, ⟨he, heQ⟩, rfl⟩ (h | h)
      · exact heQ h
      · exact h ⟨e, he, rfl⟩
  have h3 := card_sdiff_add_card_inter J (blockSet blk Q)
  omega

/-- **Lemma `lem:avoidable`(1).**  `|Q| - r_N(E_Q) ≤ k - ν(N)` for every set of blocks `Q`,
written `|Q| + ν(N) ≤ k + r_N(E_Q)`. -/
theorem card_add_nu_le (N : Matroid (Fin m)) (blk : Fin m → Fin k) (Q : Finset (Fin k)) :
    Q.card + nu N blk ≤ k + rk N (blockSet blk Q) := by
  obtain ⟨J, hJ, hJn⟩ := exists_isRainbowIndep_card_eq_nu N blk
  have := card_add_card_le hJ Q
  have := card_le_card (subset_union_left : Q ⊆ Q ∪ (univ \ blocksMet blk J))
  omega

/-- **Lemma `lem:avoidable`(3).**  `Av(N) ⊆ Q` for every `Q` attaining equality in item 1. -/
theorem av_subset {Q : Finset (Fin k)} (hQ : Q.card + nu N blk = k + rk N (blockSet blk Q)) :
    Av N blk ⊆ Q := by
  intro b hb
  by_contra hbQ
  obtain ⟨J, hJ, hJn, hbJ⟩ := mem_Av.1 hb
  have h := card_add_card_le hJ Q
  have := card_le_card (insert_subset (mem_union_right _ (mem_sdiff.2 ⟨mem_univ _, hbJ⟩))
    (subset_union_left : Q ⊆ Q ∪ (univ \ blocksMet blk J)))
  rw [card_insert_of_notMem hbQ] at this
  omega

/-- `|A'| + |I| = k + |I ∩ R|` for a rainbow set `I` (Step 2). -/
theorem card_avOf_add (hI : IsRainbow blk I) :
    (avOf N blk I).card + I.card = k + (I ∩ reachSet N blk I).card := by
  have hdisj : Disjoint (univ \ blocksMet blk I) (blocksMet blk (I ∩ reachSet N blk I)) :=
    disjoint_left.2 fun b hb hb' => (mem_sdiff.1 hb).2 (image_subset_image inter_subset_left hb')
  have h1 := card_sdiff_add_card_eq_card (subset_univ (blocksMet blk I))
  have h2 : (blocksMet blk I).card = I.card := card_image_of_injOn hI
  have h3 : (blocksMet blk (I ∩ reachSet N blk I)).card = (I ∩ reachSet N blk I).card :=
    card_image_of_injOn (hI.mono (coe_subset.2 inter_subset_left))
  rw [card_univ, Fintype.card_fin] at h1
  rw [avOf, card_union_of_disjoint hdisj]
  omega

/-- **Step 4 of the proof of `lem:avoidable`.**  If no sink is reachable from a source, then
every element of `E_{A'}` in the ground set of `N` is spanned by `I ∩ R`, so
`r_N(E_{A'}) ≤ |I ∩ R|`. -/
theorem rk_blockSet_avOf_le (hI : IsRainbowIndep N blk I)
    (h : ∀ y ∈ reachSet N blk I, ¬ IsSink N I y) :
    rk N (blockSet blk (avOf N blk I)) ≤ (I ∩ reachSet N blk I).card := by
  have hIR : N.Indep ((I ∩ reachSet N blk I : Finset (Fin m)) : Set (Fin m)) :=
    hI.1.subset (coe_subset.2 inter_subset_left)
  have hcl : ((blockSet blk (avOf N blk I) : Finset (Fin m)) : Set (Fin m)) ∩ N.E ⊆
      N.closure ((I ∩ reachSet N blk I : Finset (Fin m)) : Set (Fin m)) := by
    rintro y ⟨hy, hyE⟩
    have hy' : blk y ∈ avOf N blk I := by simpa [blockSet] using hy
    rw [avOf, mem_union, mem_sdiff] at hy'
    replace hy' : IsSource blk I y ∨ ∃ x ∈ I ∩ reachSet N blk I, blk x = blk y :=
      hy'.imp (fun h => h.2) mem_image.1
    by_cases hyI : y ∈ I
    · rcases hy' with hy' | ⟨x, hx, hxy⟩
      · exact absurd hyI hy'.notMem
      · obtain rfl := hI.2 (mem_inter.1 hx).1 hyI hxy
        exact N.subset_closure _ hIR.subset_ground (mem_coe.2 hx)
    · -- `y` is reachable, as a source or through an arc `x → y` from `x ∈ I ∩ R`
      have hyR : y ∈ reachSet N blk I := by
        rcases hy' with hy' | ⟨x, hx, hxy⟩
        · exact mem_reachSet_of_isSource hy'
        · exact mem_reachSet_of_arc (mem_inter.1 hx).2
            (Or.inr ⟨(mem_inter.1 hx).1, hyI, hxy.symm⟩)
      -- so it is not a sink, and `I` spans it
      have hycl : y ∈ N.closure I := by
        by_contra hc
        exact h y hyR ⟨hyI, (hI.1.insert_indep_iff_of_notMem hyI).2 ⟨hyE, hc⟩⟩
      -- every other element of its circuit in `I + y` receives an arc from `y`
      have hC := hI.1.fundCircuit_isCircuit hycl hyI
      refine N.closure_subset_closure ?_ (hC.mem_closure_sdiff_singleton_of_mem
        (N.mem_fundCircuit y I))
      rintro x ⟨hxC, hxy⟩
      have hxI : x ∈ I :=
        ((Set.mem_insert_iff.1 (N.fundCircuit_subset_insert y I hxC)).resolve_left hxy)
      have harc : Arc N blk I y x := Or.inl ⟨hyI, hxI, by
        rw [Set.insert_sdiff_singleton_comm (Ne.symm hxy)]
        exact (hI.1.mem_fundCircuit_iff hycl hyI).1 hxC⟩
      exact mem_coe.2 (mem_inter.2 ⟨hxI, mem_reachSet_of_arc hyR harc⟩)
  have : (rk N (blockSet blk (avOf N blk I)) : ℕ∞) ≤ (I ∩ reachSet N blk I).card := by
    rw [coe_rk, ← N.eRk_inter_ground, ← Set.encard_coe_eq_coe_finsetCard, ← hIR.eRk_eq_encard,
      ← N.eRk_closure_eq ((I ∩ reachSet N blk I : Finset (Fin m)) : Set (Fin m))]
    exact N.eRk_mono hcl
  exact_mod_cast this

/-- **Maximality.**  If no sink of the exchange graph of a rainbow independent `I` is reachable
from a source, then `|I| = ν(N)`. -/
theorem card_eq_nu (hI : IsRainbowIndep N blk I) (h : ∀ y ∈ reachSet N blk I, ¬ IsSink N I y) :
    I.card = nu N blk := by
  have h1 := card_add_nu_le N blk (avOf N blk I)
  have h2 := rk_blockSet_avOf_le hI h
  have h3 := card_avOf_add (N := N) hI.2
  have h4 := hI.card_le_nu
  omega

/-- A rainbow independent `I` is largest exactly when no sink is reachable from a source. -/
theorem card_eq_nu_iff (hI : IsRainbowIndep N blk I) :
    I.card = nu N blk ↔ ∀ y ∈ reachSet N blk I, ¬ IsSink N I y := by
  refine ⟨fun h y hy hs => ?_, card_eq_nu hI⟩
  obtain ⟨J, hJ, hJc⟩ := exists_augment hI ⟨y, hy, hs⟩
  have := hJ.card_le_nu
  omega

/-- **`j` rounds of augmentation.**  Let `step` send every rainbow independent `I` to a rainbow
independent set with at least `|I|` elements, and with `|I| + 1` elements when a sink is
reachable from a source.  Then `j` rounds from `∅` give a rainbow independent set with at least
`min(j, ν(N))` elements. -/
theorem iterate_step {step : Finset (Fin m) → Finset (Fin m)}
    (hstep : ∀ J, IsRainbowIndep N blk J → IsRainbowIndep N blk (step J) ∧
      J.card ≤ (step J).card ∧
        ((∃ y ∈ reachSet N blk J, IsSink N J y) → (step J).card = J.card + 1)) (j : ℕ) :
    IsRainbowIndep N blk (step^[j] ∅) ∧ min j (nu N blk) ≤ (step^[j] ∅).card := by
  induction j with
  | zero => exact ⟨isRainbowIndep_empty N blk, by simp⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := hstep _ ih.1
    refine ⟨h1, ?_⟩
    by_cases hc : ∃ y ∈ reachSet N blk (step^[j] ∅), IsSink N (step^[j] ∅) y
    · have := h3 hc
      omega
    · have := card_eq_nu ih.1 fun y hy hs => hc ⟨y, hy, hs⟩
      omega

/-- **The augmenting path algorithm.**  `j` rounds of `augStep` (least-index choices) from `∅`
give a rainbow independent set with at least `min(j, ν(N))` elements. -/
theorem iterate_augStep (N : Matroid (Fin m)) (blk : Fin m → Fin k) (j : ℕ) :
    IsRainbowIndep N blk ((augStep N blk)^[j] ∅) ∧
      min j (nu N blk) ≤ ((augStep N blk)^[j] ∅).card :=
  iterate_step (fun _ => augStep_spec) j

/-- **`j ≥ ν(N)` rounds**, in particular `j = k` (`nu_le`), give a rainbow independent set of size
`ν(N)`. -/
theorem card_iterate_augStep (N : Matroid (Fin m)) (blk : Fin m → Fin k) {j : ℕ}
    (hj : nu N blk ≤ j) : ((augStep N blk)^[j] ∅).card = nu N blk := by
  obtain ⟨h1, h2⟩ := iterate_augStep N blk j
  exact le_antisymm h1.card_le_nu (by omega)

/-- **Step 6.**  For a largest `I`, the set `A'` attains equality in item 1. -/
theorem card_avOf_add_nu (hI : IsRainbowIndep N blk I) (hmax : I.card = nu N blk) :
    (avOf N blk I).card + nu N blk = k + rk N (blockSet blk (avOf N blk I)) := by
  have h1 := card_add_nu_le N blk (avOf N blk I)
  have h2 := rk_blockSet_avOf_le hI ((card_eq_nu_iff hI).1 hmax)
  have h3 := card_avOf_add (N := N) hI.2
  omega

/-- **Step 3 of the proof of `lem:avoidable`.**  For a largest `I` and `x ∈ I ∩ R`, exchanging
along a shortest path from a source to `x` gives a rainbow independent set of size `ν(N)` that
misses `blk x`. -/
theorem exists_exchange (hI : IsRainbowIndep N blk I) (hmax : I.card = nu N blk) {x : Fin m}
    (hx : x ∈ I ∩ reachSet N blk I) :
    ∃ J, IsRainbowIndep N blk J ∧ J.card = nu N blk ∧ blk x ∉ blocksMet blk J := by
  obtain ⟨hxI, hxR⟩ := mem_inter.1 hx
  obtain ⟨v, n, rfl, hv⟩ := exists_isShortestPath_of_mem_reachSet hxR
  obtain ⟨hJ, hJc, -, hJb⟩ := hv.exchange hI hxI
  exact ⟨_, hJ, hJc.trans hmax, hJb⟩

/-- **Avoidable blocks from a largest rainbow independent set** (Steps 3 to 6 of the proof of
`lem:avoidable`).  If `|I| = ν(N)`, then `Av(N)` consists of the blocks missed by `I` and the
blocks of the elements of `I` reachable from a source. -/
theorem av_eq (hI : IsRainbowIndep N blk I) (hmax : I.card = nu N blk) :
    Av N blk = (univ \ blocksMet blk I) ∪ blocksMet blk (I ∩ reachSet N blk I) := by
  refine Subset.antisymm (av_subset (card_avOf_add_nu hI hmax)) fun b hb => mem_Av.2 ?_
  rcases mem_union.1 hb with hb | hb
  · exact ⟨I, hI, hmax, (mem_sdiff.1 hb).2⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    exact exists_exchange hI hmax hx

/-- **Lemma `lem:avoidable`(2).**  `|Av(N)| - r_N(E_{Av(N)}) = k - ν(N)`, written
`|Av(N)| + ν(N) = k + r_N(E_{Av(N)})`. -/
theorem card_av_add_nu (N : Matroid (Fin m)) (blk : Fin m → Fin k) :
    (Av N blk).card + nu N blk = k + rk N (blockSet blk (Av N blk)) := by
  obtain ⟨I, hI, hmax⟩ := exists_isRainbowIndep_card_eq_nu N blk
  rw [av_eq hI hmax]
  exact card_avOf_add_nu hI hmax

end Avoidable

end SignedTropical.Rainbow.Exchange
