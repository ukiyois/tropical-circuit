import SignedTropical.Rainbow.POSL
import SignedTropical.Subtractionfree

/-!
# The rank of `N(t)` and of `N_G` within components

`greedy_intersection.tex`, Lemma `lem:observer`, Steps 1 to 3, the mathematical content (the
Boolean circuit belongs to the observer module).  Throughout, `M : Matroid (Fin m)` has ground
set `univ`.

* `rk_minBases_eq_sum_comp`: equation `eq:rank-mu` applied within components.  For a weight `w`
  and `A ⊆ E`, `r_{M^w}(A) = Σ_x (r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x)))`, the sum over the
  least element `x` of each set `Lev(x)` (`compReps`), where `Lev(x)` (`compLevel`) and
  `Below(x)` (`compBelow`) are the elements of the component of `x` whose value equals, and is
  smaller than, that of `x`.
* `rk_N`: for `N(t) = M^{u_t}` the sets `Lev(x)` of the elements of `PO_t` are the clusters; the
  elements outside `PO_t` contribute nothing, since `PO_t` spans every component.  So
  `r_{N(t)}(A) = Σ_x (r(Below(x) ∪ (A ∩ cluster(x))) - r(Below(x)))` over the least element `x`
  of each cluster (`reps`), with `Below(x)` the elements of the component of `x` with smaller
  `u_t` (`below`).
* `rk_NG`: the same formula at `G = G_t`, `t ≥ 0`, with every set read from `G`: `PO_G`, the
  clusters of the links `linkG G` (`clusterG`), their least elements (`repsG`), and `Below_G(x)`
  (`belowG`), the `y ∈ PO_G` of the component of `x` outside the cluster of `x` with
  `(y, x) ∉ G`.
* `mem_POG_iff` (Step 1): `f ∈ PO_G` iff `r({g : (g, f) ∉ G}) < r({g : (g, f) ∉ G} + f)`.
* `uG_lt_uG_iff` (Step 2): at `G = G_t`, for `x`, `y` in one component, `u_G(x) < u_G(y)` iff
  `x ∈ PO_G ∌ y`, or `x, y ∈ PO_G` lie in different clusters and `(x, y) ∉ G`.

All differences of ranks are differences of natural numbers whose subtrahend is at most the
minuend (the rank is monotone), so no truncation occurs.
-/

open Finset

namespace SignedTropical.Rainbow.POSL

open SignedTropical.Rainbow

variable {m : ℕ} {M : Matroid (Fin m)}

/-- `r(S ∪ T) = r(S)` when `T ⊆ cl(S)`. -/
theorem rk_union_of_subset_closure {S T : Finset (Fin m)} (h : (T : Set (Fin m)) ⊆ M.closure S) :
    rk M (S ∪ T) = rk M S := by
  refine le_antisymm ?_ (rk_mono M subset_union_left)
  have hle : M.eRk ((S ∪ T : Finset (Fin m)) : Set (Fin m)) ≤ M.eRk (S : Set (Fin m)) :=
    calc M.eRk ((S ∪ T : Finset (Fin m)) : Set (Fin m))
        ≤ M.eRk (↑S ∪ M.closure ↑S) :=
          M.eRk_mono (by rw [coe_union]; exact Set.union_subset_union_right _ h)
      _ = M.eRk ↑S := by rw [Matroid.eRk_union_closure_right_eq, Set.union_self]
  rw [← coe_rk, ← coe_rk] at hle
  exact_mod_cast hle

/-! ### Equation `eq:rank-mu` within components -/

section RankComp

variable (M) (w : Fin m → ℝ)

open Classical in
/-- `Lev(x)`: the elements of the component of `x` whose value is that of `x`. -/
noncomputable def compLevel (x : Fin m) : Finset (Fin m) :=
  (Conn.comp M x).filter fun y => w y = w x

open Classical in
/-- `Below(x)`: the elements of the component of `x` with smaller value. -/
noncomputable def compBelow (x : Fin m) : Finset (Fin m) :=
  (Conn.comp M x).filter fun y => w y < w x

open Classical in
/-- The representatives: the least element of each set `Lev(x)`. -/
noncomputable def compReps : Finset (Fin m) :=
  univ.filter fun x => ∀ y ∈ compLevel M w x, x ≤ y

variable {M w} {x y : Fin m}

theorem mem_compLevel : y ∈ compLevel M w x ↔ connRel M x y ∧ w y = w x := by
  simp [compLevel, Conn.mem_comp]

theorem mem_compBelow : y ∈ compBelow M w x ↔ connRel M x y ∧ w y < w x := by
  simp [compBelow, Conn.mem_comp]

theorem mem_compReps : x ∈ compReps M w ↔ ∀ y ∈ compLevel M w x, x ≤ y := by
  simp [compReps]

theorem compLevel_eq (h : y ∈ compLevel M w x) : compLevel M w y = compLevel M w x := by
  obtain ⟨hxy, hw⟩ := mem_compLevel.1 h
  ext z
  simp only [mem_compLevel, hw]
  exact and_congr_left fun _ =>
    ⟨Conn.connRel_trans hxy, Conn.connRel_trans (Conn.connRel_symm hxy)⟩

/-- **Equation `eq:rank-mu` applied within components.**  For every weight `w` and `A ⊆ E`,
`r_{M^w}(A) = Σ_x (r(Below(x) ∪ (A ∩ Lev(x))) - r(Below(x)))`, the sum over the least element
`x` of each set `Lev(x)`.  Step 1: split every term of `eq:rank-mu` over the components
(`Conn.rk_eq_sum_comp`).  Step 2: the term of a value `ℓ` and a component `K` vanishes unless
`ℓ` is the value of some `x ∈ K`, and the pairs `(ℓ, K)` that remain are `(w_x, K_x)` for the
representatives `x`, each once. -/
theorem rk_minBases_eq_sum_comp (hE : M.E = Set.univ) (w : Fin m → ℝ) (A : Finset (Fin m)) :
    rk (minBases M w) A = ∑ x ∈ compReps M w,
      (rk M (compBelow M w x ∪ (A ∩ compLevel M w x)) - rk M (compBelow M w x)) := by
  classical
  -- `T ℓ K`: the term of `eq:rank-mu` at the value `ℓ`, restricted to the component `K`
  let T : ℝ → Finset (Fin m) → ℕ := fun ℓ K =>
    rk M ((univ.filter (fun e => w e < ℓ) ∪ A.filter (fun e => w e = ℓ)) ∩ K) -
      rk M (univ.filter (fun e => w e < ℓ) ∩ K)
  have h1 : ∀ ℓ, rk M (univ.filter (fun e => w e < ℓ) ∪ A.filter (fun e => w e = ℓ)) -
      rk M (univ.filter fun e => w e < ℓ) = ∑ K ∈ Conn.components M, T ℓ K := fun ℓ => by
    rw [Conn.rk_eq_sum_comp hE, Conn.rk_eq_sum_comp hE (univ.filter fun e => w e < ℓ),
      ← sum_tsub_distrib]
    exact fun K _ => rk_mono M (inter_subset_inter_right subset_union_left)
  have hsub : (compReps M w).image (fun x => (w x, Conn.comp M x)) ⊆
      (univ.image w) ×ˢ Conn.components M := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_product.2 ⟨mem_image_of_mem w (mem_univ x), Conn.comp_mem_components x⟩
  have hzero : ∀ p ∈ (univ.image w) ×ˢ Conn.components M,
      p ∉ (compReps M w).image (fun x => (w x, Conn.comp M x)) → T p.1 p.2 = 0 := by
    rintro ⟨ℓ, K⟩ hp hpn
    have hK := (mem_product.1 hp).2
    have hA : A.filter (fun e => w e = ℓ) ∩ K = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => hpn ?_
      obtain ⟨hyA, hyK⟩ := mem_inter.1 hy
      have hne : (compLevel M w y).Nonempty := ⟨y, mem_compLevel.2 ⟨Conn.connRel_refl M y, rfl⟩⟩
      have hx := min'_mem _ hne
      obtain ⟨hyx, hwx⟩ := mem_compLevel.1 hx
      refine mem_image.2 ⟨(compLevel M w y).min' hne, mem_compReps.2 fun z hz =>
        min'_le _ _ (by rwa [compLevel_eq hx] at hz), ?_⟩
      rw [hwx, (mem_filter.1 hyA).2, ← Conn.comp_eq_comp_iff.2 hyx,
        Conn.comp_eq_of_mem_components hK hyK]
    simp only [T, union_inter_distrib_right, hA, union_empty, Nat.sub_self]
  have hinj : Set.InjOn (fun x => (w x, Conn.comp M x)) (compReps M w : Set (Fin m)) := by
    intro x hx x' hx' hxx'
    obtain ⟨hw, hc⟩ := Prod.mk.inj hxx'
    have hc' := Conn.comp_eq_comp_iff.1 hc
    exact le_antisymm (mem_compReps.1 hx x' (mem_compLevel.2 ⟨hc', hw.symm⟩))
      (mem_compReps.1 hx' x (mem_compLevel.2 ⟨Conn.connRel_symm hc', hw⟩))
  rw [rk_minBases hE w A, sum_congr rfl fun ℓ _ => h1 ℓ, ← sum_product' (f := T),
    ← sum_subset hsub hzero, sum_image hinj]
  refine sum_congr rfl fun x _ => ?_
  have hB : univ.filter (fun e => w e < w x) ∩ Conn.comp M x = compBelow M w x := by
    ext y
    simp [compBelow, and_comm]
  have hL : (univ.filter (fun e => w e < w x) ∪ A.filter (fun e => w e = w x)) ∩ Conn.comp M x =
      compBelow M w x ∪ (A ∩ compLevel M w x) := by
    ext y
    simp only [compBelow, compLevel, mem_inter, mem_union, mem_filter, mem_univ, true_and]
    tauto
  simp only [T, hB, hL]

end RankComp

/-! ### The rank of `N(t)` -/

section RankN

variable {v : Fin m → ℝ} {t : ℝ} {x y : Fin m}

open Classical in
/-- The representatives of the clusters at scale `t`: the least element of each cluster. -/
noncomputable def reps (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) : Finset (Fin m) :=
  univ.filter fun x => x ∈ PO M v t ∧ ∀ y ∈ cluster M (PO M v t) (near v t) x, x ≤ y

open Classical in
/-- `Below(x)`: the elements of the component of `x` with smaller `u_t`. -/
noncomputable def below (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) (x : Fin m) :
    Finset (Fin m) :=
  (Conn.comp M x).filter fun y => u M v t y < u M v t x

theorem mem_reps : x ∈ reps M v t ↔
    x ∈ PO M v t ∧ ∀ y ∈ cluster M (PO M v t) (near v t) x, x ≤ y := by
  simp [reps]

theorem mem_below : y ∈ below M v t x ↔ connRel M x y ∧ u M v t y < u M v t x := by
  simp [below, Conn.mem_comp]

/-- For `x ∈ PO_t`, the level set of `u_t` within the component of `x` is the cluster of `x`. -/
theorem compLevel_u (ht : 0 ≤ t) (hx : x ∈ PO M v t) :
    compLevel M (fun e => (u M v t e : ℝ)) x = cluster M (PO M v t) (near v t) x := by
  ext y
  rw [mem_compLevel, mem_cluster, Nat.cast_inj]
  refine ⟨fun ⟨hxy, hu⟩ => (u_eq_u_iff ht hx ?_ hxy).1 hu.symm, fun h =>
    ⟨h.conn, (u_eq_u_of_sameCluster ht h).symm⟩⟩
  exact u_le_iff_mem.1 (hu ▸ u_le_iff_mem.2 hx)

theorem compBelow_u : compBelow M (fun e => (u M v t e : ℝ)) x = below M v t x := by
  ext y
  simp [compBelow, below]

/-- The elements outside `PO_t` contribute nothing: for `x ∉ PO_t`, `Below(x)` is `PO_t` within
the component of `x`, which spans the component. -/
theorem rk_compBelow_union_u (hE : M.E = Set.univ) (ht : 0 ≤ t) (hx : x ∉ PO M v t)
    (A : Finset (Fin m)) :
    rk M (compBelow M (fun e => (u M v t e : ℝ)) x ∪
        (A ∩ compLevel M (fun e => (u M v t e : ℝ)) x)) =
      rk M (compBelow M (fun e => (u M v t e : ℝ)) x) := by
  refine rk_union_of_subset_closure fun z hz => ?_
  have hxz := (mem_compLevel.1 (mem_inter.1 hz).2).1
  refine M.closure_subset_closure (fun y hy => ?_) (mem_closure_PO (v := v) hE ht z)
  rw [mem_coe, mem_compBelow, u_of_notMem hx]
  refine ⟨Conn.connRel_trans hxz (Conn.mem_comp.1 hy.2), ?_⟩
  have := u_le_iff_mem.2 hy.1
  exact_mod_cast Nat.lt_succ_of_le this

/-- **The rank of `N(t)`** (Lemma `lem:observer`, Step 3): for `t ≥ 0` and `A ⊆ E`,
`r_{N(t)}(A) = Σ_x (r(Below(x) ∪ (A ∩ cluster(x))) - r(Below(x)))`, the sum over the least
element `x` of each cluster at scale `t`, where `Below(x)` is the set of elements of the
component of `x` with smaller `u_t`. -/
theorem rk_N (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Finset (Fin m)) :
    rk (N M v t) A = ∑ x ∈ reps M v t,
      (rk M (below M v t x ∪ (A ∩ cluster M (PO M v t) (near v t) x)) - rk M (below M v t x)) := by
  classical
  rw [N, rk_minBases_eq_sum_comp hE, ← sum_filter_add_sum_filter_not _ (· ∈ PO M v t),
    sum_eq_zero (s := (compReps M _).filter (· ∉ PO M v t)) fun x hx => ?_, add_zero]
  · have hR : (compReps M fun e => (u M v t e : ℝ)).filter (· ∈ PO M v t) = reps M v t := by
      ext x
      simp only [mem_filter, reps, mem_univ, true_and]
      refine ⟨fun ⟨h, hx⟩ => ⟨hx, ?_⟩, fun ⟨hx, h⟩ => ⟨?_, hx⟩⟩
      · rwa [mem_compReps, compLevel_u ht hx] at h
      · rwa [mem_compReps, compLevel_u ht hx]
    rw [hR]
    refine sum_congr rfl fun x hx => ?_
    rw [compLevel_u ht (mem_filter.1 hx).2.1, compBelow_u]
  · rw [rk_compBelow_union_u hE ht (mem_filter.1 hx).2, Nat.sub_self]

/-! ### The rank of `N_G` read from `G` -/

open Classical in
/-- The cluster of `x` read from `G`: the cluster of the links `linkG G` on `PO_G`. -/
noncomputable def clusterG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) (x : Fin m) :
    Finset (Fin m) :=
  cluster M (POG M G) (linkG G) x

open Classical in
/-- The least element of each cluster read from `G`. -/
noncomputable def repsG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Finset (Fin m) :=
  univ.filter fun x => x ∈ POG M G ∧ ∀ y ∈ clusterG M G x, x ≤ y

open Classical in
/-- `Below_G(x)`: the `y ∈ PO_G` of the component of `x`, outside the cluster of `x`, with
`(y, x) ∉ G`. -/
noncomputable def belowG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) (x : Fin m) :
    Finset (Fin m) :=
  univ.filter fun y => y ∈ POG M G ∧ connRel M x y ∧
    ¬SameCluster M (POG M G) (linkG G) x y ∧ (y, x) ∉ G

theorem mem_repsG {G : Finset (Fin m × Fin m)} :
    x ∈ repsG M G ↔ x ∈ POG M G ∧ ∀ y ∈ clusterG M G x, x ≤ y := by
  simp [repsG]

theorem mem_belowG {G : Finset (Fin m × Fin m)} : y ∈ belowG M G x ↔
    y ∈ POG M G ∧ connRel M x y ∧ ¬SameCluster M (POG M G) (linkG G) x y ∧ (y, x) ∉ G := by
  simp [belowG]

theorem below_eq_belowG (ht : 0 ≤ t) (hx : x ∈ PO M v t) :
    below M v t x = belowG M (Gt v t) x := by
  ext y
  simp only [below, belowG, mem_filter, mem_univ, true_and, Conn.mem_comp, ← PO_eq_POG,
    ← near_eq_linkG]
  refine ⟨fun ⟨hxy, hlt⟩ => ?_, fun ⟨hy, hxy, hn, hG⟩ => ⟨hxy, ?_⟩⟩
  · obtain ⟨-, hxn⟩ | ⟨hy, -, hn, hlt⟩ := (u_lt_u_iff ht (Conn.connRel_symm hxy)).1 hlt
    · exact absurd hx hxn
    · exact ⟨hy, hxy, fun h => hn (h.symm near_comm), (lt_iff_notMem_Gt ht hy hx
        (Conn.connRel_symm hxy) hn).1 hlt⟩
  · have hn' : ¬SameCluster M (PO M v t) (near v t) y x := fun h => hn (h.symm near_comm)
    exact (u_lt_u_iff ht (Conn.connRel_symm hxy)).2 (.inr ⟨hy, hx, hn',
      (lt_iff_notMem_Gt ht hy hx (Conn.connRel_symm hxy) hn').2 hG⟩)

/-- **The rank of `N_G` read from `G`** (Lemma `lem:observer`, Step 3): for `G = G_t`, `t ≥ 0`,
and `A ⊆ E`, `r_{N_G}(A) = Σ_x (r(Below_G(x) ∪ (A ∩ cluster_G(x))) - r(Below_G(x)))`, the sum
over the least element `x` of each cluster read from `G`. -/
theorem rk_NG (hE : M.E = Set.univ) (ht : 0 ≤ t) (A : Finset (Fin m)) :
    rk (NG M (Gt v t)) A = ∑ x ∈ repsG M (Gt v t),
      (rk M (belowG M (Gt v t) x ∪ (A ∩ clusterG M (Gt v t) x)) -
        rk M (belowG M (Gt v t) x)) := by
  have hreps : repsG M (Gt v t) = reps M v t := by
    unfold repsG reps clusterG
    rw [← PO_eq_POG, ← near_eq_linkG]
  rw [← N_eq_NG ht, rk_N hE ht, hreps]
  refine sum_congr rfl fun x hx => ?_
  rw [below_eq_belowG ht (mem_reps.1 hx).1, clusterG, ← PO_eq_POG, ← near_eq_linkG]

/-- `PO_G` from rank queries (Lemma `lem:observer`, Step 1): `f ∈ PO_G` iff
`r({g : (g, f) ∉ G}) < r({g : (g, f) ∉ G} + f)`. -/
theorem mem_POG_iff (hE : M.E = Set.univ) (G : Finset (Fin m × Fin m)) (f : Fin m) :
    f ∈ POG M G ↔ rk M (univ.filter fun g => (g, f) ∉ G) <
      rk M (insert f (univ.filter fun g => (g, f) ∉ G)) := by
  have hX : ((univ.filter fun g => (g, f) ∉ G : Finset (Fin m)) : Set (Fin m)) =
      {g | (g, f) ∉ G} := by
    ext
    simp
  constructor
  · intro hf
    have h := M.eRk_insert_eq_add_one (e := f) (X := {g | (g, f) ∉ G}) ⟨by simp [hE], hf⟩
    rw [← hX, ← coe_insert, ← coe_rk, ← coe_rk] at h
    have h' : rk M (insert f (univ.filter fun g => (g, f) ∉ G)) =
        rk M (univ.filter fun g => (g, f) ∉ G) + 1 := by exact_mod_cast h
    omega
  · intro hlt hcl
    have h : rk M ((univ.filter fun g => (g, f) ∉ G) ∪ {f}) =
        rk M (univ.filter fun g => (g, f) ∉ G) :=
      rk_union_of_subset_closure (by rw [coe_singleton, Set.singleton_subset_iff, hX]; exact hcl)
    rw [union_comm, ← insert_eq] at h
    omega

/-- The order of `u_G` within a component, read from `G` (Lemma `lem:observer`, Step 2): at
`G = G_t`, `t ≥ 0`, for `x`, `y` in one component, `u_G(x) < u_G(y)` iff `x ∈ PO_G ∌ y`, or
`x, y ∈ PO_G` lie in different clusters and `(x, y) ∉ G`. -/
theorem uG_lt_uG_iff (ht : 0 ≤ t) (hxy : connRel M x y) :
    uG M (Gt v t) x < uG M (Gt v t) y ↔ (x ∈ POG M (Gt v t) ∧ y ∉ POG M (Gt v t)) ∨
      (x ∈ POG M (Gt v t) ∧ y ∈ POG M (Gt v t) ∧
        ¬SameCluster M (POG M (Gt v t)) (linkG (Gt v t)) x y ∧ (x, y) ∉ Gt v t) := by
  rw [← u_eq_uG ht, ← PO_eq_POG, ← near_eq_linkG, u_lt_u_iff ht hxy]
  exact or_congr_right
    ⟨fun ⟨hx, hy, hn, hlt⟩ => ⟨hx, hy, hn, (lt_iff_notMem_Gt ht hx hy hxy hn).1 hlt⟩,
      fun ⟨hx, hy, hn, h⟩ => ⟨hx, hy, hn, (lt_iff_notMem_Gt ht hx hy hxy hn).2 h⟩⟩

end RankN

end SignedTropical.Rainbow.POSL
