import SignedTropical.Rainbow.PossiblyOptimal

/-!
# PO-SL: single linkage on possibly optimal elements

`greedy_intersection.tex`, Section 4.5: Definition `def:posl` and the first two sentences of
Proposition `prop:posl`.  Throughout, `M : Matroid (Fin m)` has ground set `univ` (hypothesis
`hE`), `v : Fin m → ℝ` and `t ≥ 0`.

**Single linkage** for a set `P`, a link predicate `J` and an order predicate `L`
(`Link`, `SameCluster`, `cluster`, `lowerSet`, `clusterRank`): `x, y ∈ P` lying in one
component of `M` are linked when `J x y`; the clusters are the classes of the closure of the
links on `P`; `clusterRank` of `e ∈ P` is one more than the number of clusters `cluster y` of
the component of `e`, other than the cluster of `e`, with `L y e`, and it is `m + 1` for
`e ∉ P`.

**Definition `def:posl`.**  `PO M v t = {f : f ∉ cl{g : v_g < v_f - t}}`, the links
`near v t x y : |v_x - v_y| ≤ t`, `u M v t = clusterRank` with the order `v_y < v_e`, and
`N M v t = M^{u_t}`.  The clusters are the classes of the transitive closure of the links
(`sameCluster_iff_transGen`).  The facts stated in the definition: `SameCluster.of_le_of_le`
(clusters are intervals of the sorted values of `PO_t ∩ K`), `SameCluster.sub_le` (consecutive
values inside a cluster differ by at most `t`), `lt_abs_sub` and `lt_sub_of_not_sameCluster`
(two clusters of `K` differ by more than `t`, so they are ordered).  So `u_t(e)` is the rank of
the cluster of `e` in this order (`u_eq_card_add_one`; comparisons `u_le_u_iff`, `u_eq_u_iff`,
`u_lt_u_iff`, `u_le_iff_mem`).

**Proposition `prop:posl`** (`prop_posl`): the family `N M v` is admissible (`isAdmissible`:
(F1) `N_zero`, (F2) `isBase_N_mono`, (F3) `isBase_N_of_mem_Pos`, (F4) `N_eq_self`,
(F5) `N_eq_N_of_levels` with the levels `levels v = {0} ∪ {|v_e - v_f|}`), and it is determined
by `G_t = {(e, f) : v_f - v_e ≤ t}` (`Gt`): `N_eq_NG` gives `N(t) = N_{G_t}`, where `NG M G` is
defined for every relation `G ⊆ E × E` by reading `PO`, the links and the order of the clusters
from `G` (`POG`, `linkG`, `uG`), as in Step 5 of the proof and in Lemma `lem:observer`;
`NG_univ`: `N_{E × E} = M`.  The rank of `N_G` is in `Rainbow/POSLRank.lean`.

Along the way: `PO_0` is the set of elements of minimum bases of `v` (`mem_PO_zero_iff`),
`PO_t` grows with `t` and spans every component (`PO_mono`, `mem_closure_PO`), and every base
of `M^v` or of `N(t)` lies in `PO_t` (`subset_PO_of_isBase_minBases`, `subset_PO_of_isBase_N`).
-/

open Finset

namespace SignedTropical.Rainbow.POSL

open SignedTropical.Rainbow

variable {m k : ℕ} {M : Matroid (Fin m)}

/-! ### Single linkage within components -/

section Clusters

variable (M) (P : Set (Fin m)) (J : Fin m → Fin m → Prop)

/-- The links of single linkage: `x` and `y` lie in `P` and in one component of `M`, and
`J x y`. -/
def Link (x y : Fin m) : Prop :=
  x ∈ P ∧ y ∈ P ∧ connRel M x y ∧ J x y

/-- `x` and `y` lie in one cluster: `x ∈ P` and a chain of links, possibly empty, leads from `x`
to `y`.  For the links of Definition `def:posl` at `t ≥ 0`, which are reflexive on `P`, this is
the transitive closure of the links (`sameCluster_iff_transGen`). -/
def SameCluster (x y : Fin m) : Prop :=
  x ∈ P ∧ Relation.ReflTransGen (Link M P J) x y

open Classical in
/-- The cluster of `x`; it is empty when `x ∉ P`. -/
noncomputable def cluster (x : Fin m) : Finset (Fin m) :=
  univ.filter (SameCluster M P J x)

open Classical in
/-- The elements `y ∈ P` of the component of `e`, outside the cluster of `e`, with `L y e`. -/
noncomputable def lowerSet (L : Fin m → Fin m → Prop) (e : Fin m) : Finset (Fin m) :=
  univ.filter fun y => y ∈ P ∧ connRel M y e ∧ ¬SameCluster M P J y e ∧ L y e

open Classical in
/-- The rank of the cluster of `e` among the clusters of its component, ordered by `L`: one
more than the number of clusters `cluster y`, `y ∈ lowerSet M P J L e`, for `e ∈ P`; and
`m + 1` for `e ∉ P`. -/
noncomputable def clusterRank (L : Fin m → Fin m → Prop) (e : Fin m) : ℕ :=
  if e ∈ P then #((lowerSet M P J L e).image (cluster M P J)) + 1 else m + 1

end Clusters

/-! ### Definition `def:posl` and the matroid `N_G` of a relation -/

/-- `PO_t = {f : f ∉ cl{g : v_g < v_f - t}}`, the possibly optimal elements at scale `t`. -/
def PO (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) : Set (Fin m) :=
  {f | f ∉ M.closure {g | v g < v f - t}}

/-- The links at scale `t`: `|v_x - v_y| ≤ t`. -/
def near (v : Fin m → ℝ) (t : ℝ) (x y : Fin m) : Prop :=
  |v x - v y| ≤ t

/-- **Definition `def:posl`**, the weight `u_t`.  For `e ∈ PO_t`, `u_t(e)` is the rank of the
cluster of `e` at scale `t` among the clusters of its component, `1` for the lowest: one more
than the number of clusters of the component that contain an element `y` with `v_y < v_e`
outside the cluster of `e` (these are the clusters below that of `e`,
`lt_sub_of_not_sameCluster`).  For `e ∉ PO_t`, `u_t(e) = m + 1`. -/
noncomputable def u (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) : Fin m → ℕ :=
  clusterRank M (PO M v t) (near v t) fun y e => v y < v e

/-- **Definition `def:posl`**, `N(t) = M^{u_t}`. -/
noncomputable def N (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) : Matroid (Fin m) :=
  minBases M fun e => (u M v t e : ℝ)

/-- `PO_G = {f : f ∉ cl{g : (g, f) ∉ G}}`, the set `PO` read from a relation `G ⊆ E × E`. -/
def POG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Set (Fin m) :=
  {f | f ∉ M.closure {g | (g, f) ∉ G}}

/-- The links read from `G`: `(x, y) ∈ G` and `(y, x) ∈ G`. -/
def linkG (G : Finset (Fin m × Fin m)) (x y : Fin m) : Prop :=
  (x, y) ∈ G ∧ (y, x) ∈ G

/-- The weight `u_G`: `clusterRank` for `PO_G`, the links `linkG G` within components, and the
order of the clusters read from `G`, the cluster of `y` lying below that of `e` when
`(y, e) ∉ G`. -/
noncomputable def uG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Fin m → ℕ :=
  clusterRank M (POG M G) (linkG G) fun y e => (y, e) ∉ G

/-- The matroid `N_G = M^{u_G}` that Definition `def:posl` assigns to a relation `G`. -/
noncomputable def NG (M : Matroid (Fin m)) (G : Finset (Fin m × Fin m)) : Matroid (Fin m) :=
  minBases M fun e => (uG M G e : ℝ)

/-- `G_t = {(e, f) ∈ E × E : v_f - v_e ≤ t}`. -/
noncomputable def Gt (v : Fin m → ℝ) (t : ℝ) : Finset (Fin m × Fin m) :=
  univ.filter fun p => v p.2 - v p.1 ≤ t

/-- The levels `{0} ∪ {|v_e - v_f| : e, f ∈ E}` of Proposition `prop:posl`. -/
noncomputable def levels (v : Fin m → ℝ) : Finset ℝ :=
  insert 0 ((univ : Finset (Fin m × Fin m)).image fun p => |v p.1 - v p.2|)

theorem mem_PO {v : Fin m → ℝ} {t : ℝ} {f : Fin m} :
    f ∈ PO M v t ↔ f ∉ M.closure {g | v g < v f - t} :=
  Iff.rfl

theorem mem_POG {G : Finset (Fin m × Fin m)} {f : Fin m} :
    f ∈ POG M G ↔ f ∉ M.closure {g | (g, f) ∉ G} :=
  Iff.rfl

@[simp] theorem mem_Gt {v : Fin m → ℝ} {t : ℝ} {p : Fin m × Fin m} :
    p ∈ Gt v t ↔ v p.2 - v p.1 ≤ t := by
  simp [Gt]

theorem linkG_comm {G : Finset (Fin m × Fin m)} (a b : Fin m) : linkG G a b → linkG G b a :=
  And.symm

theorem zero_mem_levels (v : Fin m → ℝ) : (0 : ℝ) ∈ levels v :=
  mem_insert_self _ _

theorem abs_sub_mem_levels (v : Fin m → ℝ) (e f : Fin m) : |v e - v f| ∈ levels v :=
  mem_insert_of_mem (mem_image.2 ⟨(e, f), mem_univ _, rfl⟩)

/-! ### Clusters -/

section Generic

variable {P : Set (Fin m)} {J : Fin m → Fin m → Prop} {L : Fin m → Fin m → Prop}
  {x y z e : Fin m}

theorem mem_cluster : y ∈ cluster M P J x ↔ SameCluster M P J x y := by
  simp [cluster]

theorem mem_lowerSet :
    y ∈ lowerSet M P J L e ↔ y ∈ P ∧ connRel M y e ∧ ¬SameCluster M P J y e ∧ L y e := by
  simp [lowerSet]

theorem SameCluster.refl (hx : x ∈ P) : SameCluster M P J x x :=
  ⟨hx, .refl⟩

theorem SameCluster.of_link (hx : x ∈ P) (hy : y ∈ P) (hxy : connRel M x y) (h : J x y) :
    SameCluster M P J x y :=
  ⟨hx, .single ⟨hx, hy, hxy, h⟩⟩

theorem SameCluster.mem_left (h : SameCluster M P J x y) : x ∈ P :=
  h.1

theorem SameCluster.mem_right (h : SameCluster M P J x y) : y ∈ P := by
  obtain ⟨hx, h⟩ := h
  obtain rfl | ⟨c, -, hc⟩ := h.cases_tail
  · exact hx
  · exact hc.2.1

/-- A cluster lies in one component. -/
theorem SameCluster.conn (h : SameCluster M P J x y) : connRel M x y := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact Conn.connRel_refl M x
  | tail _ hl ih => exact Conn.connRel_trans ih hl.2.2.1

theorem SameCluster.trans (h₁ : SameCluster M P J x y) (h₂ : SameCluster M P J y z) :
    SameCluster M P J x z :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

theorem SameCluster.symm (hJ : ∀ a b, J a b → J b a) (h : SameCluster M P J x y) :
    SameCluster M P J y x := by
  refine ⟨h.mem_right, ?_⟩
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact .refl
  | tail _ hl ih => exact ih.head ⟨hl.2.1, hl.1, Conn.connRel_symm hl.2.2.1, hJ _ _ hl.2.2.2⟩

theorem clusterRank_of_mem (he : e ∈ P) :
    clusterRank M P J L e = #((lowerSet M P J L e).image (cluster M P J)) + 1 :=
  if_pos he

theorem clusterRank_of_notMem (he : e ∉ P) : clusterRank M P J L e = m + 1 :=
  if_neg he

theorem one_le_clusterRank : 1 ≤ clusterRank M P J L e := by
  unfold clusterRank
  split_ifs <;> omega

theorem clusterRank_le_of_mem (he : e ∈ P) : clusterRank M P J L e ≤ m := by
  rw [clusterRank_of_mem he]
  have h : lowerSet M P J L e ⊆ univ.erase e := fun y hy =>
    mem_erase.2 ⟨fun hye => (mem_lowerSet.1 hy).2.2.1 (by rw [hye]; exact .refl he), mem_univ y⟩
  have h' : #((lowerSet M P J L e).image (cluster M P J)) ≤ #(univ.erase e) :=
    card_image_le.trans (card_le_card h)
  rw [card_erase_of_mem (mem_univ e), card_univ, Fintype.card_fin] at h'
  have := e.pos
  omega

/-- `clusterRank` is at most `m` exactly on `P`. -/
theorem clusterRank_le_iff : clusterRank M P J L e ≤ m ↔ e ∈ P := by
  refine ⟨fun h => ?_, clusterRank_le_of_mem⟩
  by_contra he
  rw [clusterRank_of_notMem he] at h
  omega

/-- `clusterRank` depends on `L y e` only for `y, e ∈ P` in one component and in different
clusters. -/
theorem clusterRank_congr {L' : Fin m → Fin m → Prop}
    (h : ∀ y e, y ∈ P → e ∈ P → connRel M y e → ¬SameCluster M P J y e → (L y e ↔ L' y e)) :
    clusterRank M P J L = clusterRank M P J L' := by
  funext e
  by_cases he : e ∈ P
  · have hL : lowerSet M P J L e = lowerSet M P J L' e := by
      ext y
      simp only [mem_lowerSet]
      exact and_congr_right fun hy => and_congr_right fun hye => and_congr_right fun hn =>
        h y e hy he hye hn
    rw [clusterRank_of_mem he, clusterRank_of_mem he, hL]
  · rw [clusterRank_of_notMem he, clusterRank_of_notMem he]

end Generic

/-! ### The facts stated in Definition `def:posl` -/

section Values

variable {P : Set (Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y z x' y' : Fin m}

theorem near_comm (a b : Fin m) : near v t a b → near v t b a := by
  rw [near, near, abs_sub_comm]
  exact id

theorem near_of_eq (ht : 0 ≤ t) {a b : Fin m} (h : v a = v b) : near v t a b := by
  rwa [near, h, sub_self, abs_zero]

/-- For `t ≥ 0` the links are reflexive on `P`, so the clusters are the classes of the transitive
closure of the links. -/
theorem sameCluster_iff_transGen (ht : 0 ≤ t) :
    SameCluster M P (near v t) x y ↔ Relation.TransGen (Link M P (near v t)) x y := by
  refine ⟨fun ⟨hx, h⟩ => ?_, fun h => ⟨?_, h.to_reflTransGen⟩⟩
  · exact Relation.TransGen.head' ⟨hx, hx, Conn.connRel_refl M x, near_of_eq ht rfl⟩ h
  · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 h
    exact hb.1

/-- **Clusters are intervals** of the sorted values of `P ∩ K`: an element of `P` in the
component, whose value lies between the values of two elements of a cluster, lies in that
cluster. -/
theorem SameCluster.of_le_of_le (ht : 0 ≤ t) (h : SameCluster M P (near v t) x z) (hy : y ∈ P)
    (hxy : connRel M x y) (h₁ : v x ≤ v y) (h₂ : v y ≤ v z) : SameCluster M P (near v t) x y := by
  obtain ⟨hx, hxz⟩ := h
  induction hxz with
  | refl => exact .of_link hx hy hxy (near_of_eq ht (le_antisymm h₁ h₂))
  | @tail w z hxw hwz ih =>
    rcases le_or_gt (v y) (v w) with hyw | hwy
    · exact ih hyw
    · refine ⟨hx, hxw.tail ⟨hwz.1, hy,
        Conn.connRel_trans (Conn.connRel_symm (SameCluster.conn ⟨hx, hxw⟩)) hxy, ?_⟩⟩
      have hwz' := abs_le.1 hwz.2.2.2
      rw [near, abs_le]
      constructor <;> linarith [hwz'.1, hwz'.2]

/-- Every cut `c` with `v_x ≤ c < v_z` between two elements of a cluster is crossed by a link of
the cluster. -/
theorem SameCluster.exists_link (h : SameCluster M P (near v t) x z) {c : ℝ} (hxc : v x ≤ c)
    (hcz : c < v z) : ∃ a b, SameCluster M P (near v t) x a ∧ SameCluster M P (near v t) x b ∧
      v a ≤ c ∧ c < v b ∧ v b - v a ≤ t := by
  obtain ⟨hx, hxz⟩ := h
  induction hxz with
  | refl => exact absurd (hxc.trans_lt hcz) (lt_irrefl _)
  | @tail w z hxw hwz ih =>
    rcases lt_or_ge c (v w) with hcw | hwc
    · exact ih hcw
    · exact ⟨w, z, ⟨hx, hxw⟩, ⟨hx, hxw.tail hwz⟩, hwc, hcz, by
        linarith [(abs_le.1 hwz.2.2.2).1]⟩

/-- **Consecutive values inside a cluster differ by at most `t`**: if `x` and `z` lie in one
cluster, `v_x < v_z`, and no element of the cluster has a value strictly between, then
`v_z - v_x ≤ t`. -/
theorem SameCluster.sub_le (h : SameCluster M P (near v t) x z) (hxz : v x < v z)
    (hgap : ∀ y, SameCluster M P (near v t) x y → v x < v y → v z ≤ v y) : v z - v x ≤ t := by
  obtain ⟨a, b, -, hb, ha, hb', hab⟩ := h.exists_link le_rfl hxz
  linarith [hgap b hb hb']

/-- **Two clusters of a component differ by more than `t`**: elements `x'`, `y'` of the
clusters of `x` and `y`, which lie in one component and in different clusters, have
`|v_{x'} - v_{y'}| > t`. -/
theorem lt_abs_sub (hxy : connRel M x y) (h : ¬SameCluster M P (near v t) x y)
    (hx : SameCluster M P (near v t) x x') (hy : SameCluster M P (near v t) y y') :
    t < |v x' - v y'| := by
  refine lt_of_not_ge fun hle => h ?_
  refine hx.trans ((SameCluster.of_link hx.mem_right hy.mem_right ?_ hle).trans
    (hy.symm near_comm))
  exact Conn.connRel_trans (Conn.connRel_symm hx.conn) (Conn.connRel_trans hxy hy.conn)

/-- **The clusters of a component are ordered**: if `x` and `y` lie in one component and in
different clusters and `v_x < v_y`, every element of the cluster of `y` exceeds every element
of the cluster of `x` by more than `t`. -/
theorem lt_sub_of_not_sameCluster (ht : 0 ≤ t) (hxy : connRel M x y)
    (h : ¬SameCluster M P (near v t) x y) (hlt : v x < v y)
    (hx : SameCluster M P (near v t) x x') (hy : SameCluster M P (near v t) y y') :
    t < v y' - v x' := by
  have hx'y : connRel M x' y := Conn.connRel_trans (Conn.connRel_symm hx.conn) hxy
  have h₁ : v x' < v y := lt_of_not_ge fun hle =>
    h (hx.of_le_of_le ht hy.mem_left hxy hlt.le hle |>.trans (.refl hy.mem_left))
  have h₂ : v x' < v y' := lt_of_not_ge fun hle => h <| hx.trans <|
    ((hy.symm near_comm).of_le_of_le ht hx.mem_right
      (Conn.connRel_trans (Conn.connRel_symm hy.conn) (Conn.connRel_symm hx'y)) hle
      h₁.le).symm near_comm |>.trans (hy.symm near_comm)
  have h₃ := lt_abs_sub hxy h hx hy
  rwa [abs_sub_comm, abs_of_pos (sub_pos.2 h₂)] at h₃

/-! ### `u_t` is the rank of the cluster -/

/-- The clusters below `x` are those below any `y` of the cluster of `x`. -/
theorem lowerSet_eq (ht : 0 ≤ t) (h : SameCluster M P (near v t) x y) :
    lowerSet M P (near v t) (fun a b => v a < v b) x =
      lowerSet M P (near v t) (fun a b => v a < v b) y := by
  have key : ∀ a b, SameCluster M P (near v t) a b →
      lowerSet M P (near v t) (fun a b => v a < v b) a ⊆
        lowerSet M P (near v t) (fun a b => v a < v b) b := by
    intro a b hab z hz
    obtain ⟨hzP, hza, hn, hlt⟩ := mem_lowerSet.1 hz
    refine mem_lowerSet.2 ⟨hzP, Conn.connRel_trans hza hab.conn,
      fun hzb => hn (hzb.trans (hab.symm near_comm)), ?_⟩
    linarith [lt_sub_of_not_sameCluster ht hza hn hlt (.refl hzP) hab]
  exact (key x y h).antisymm (key y x (h.symm near_comm))

theorem image_lowerSet_ssubset (ht : 0 ≤ t) (hx : x ∈ P) (hxy : connRel M x y)
    (h : ¬SameCluster M P (near v t) x y) (hlt : v x < v y) :
    (lowerSet M P (near v t) (fun a b => v a < v b) x).image (cluster M P (near v t)) ⊂
      (lowerSet M P (near v t) (fun a b => v a < v b) y).image (cluster M P (near v t)) := by
  refine (ssubset_iff_of_subset (image_subset_image fun z hz => ?_)).2
    ⟨cluster M P (near v t) x, mem_image_of_mem _
      (mem_lowerSet.2 ⟨hx, hxy, h, hlt⟩), fun hmem => ?_⟩
  · obtain ⟨hzP, hzx, hn, hzlt⟩ := mem_lowerSet.1 hz
    refine mem_lowerSet.2 ⟨hzP, Conn.connRel_trans hzx hxy, fun hzy => ?_, hzlt.trans hlt⟩
    linarith [lt_sub_of_not_sameCluster ht hzx hn hzlt hzy (.refl hx)]
  · obtain ⟨z, hz, hzx⟩ := mem_image.1 hmem
    have hxz : x ∈ cluster M P (near v t) z := by
      rw [hzx]
      exact mem_cluster.2 (.refl hx)
    exact (mem_lowerSet.1 hz).2.2.1 (mem_cluster.1 hxz)

theorem clusterRank_eq_of_sameCluster (ht : 0 ≤ t) (h : SameCluster M P (near v t) x y) :
    clusterRank M P (near v t) (fun a b => v a < v b) x =
      clusterRank M P (near v t) (fun a b => v a < v b) y := by
  rw [clusterRank_of_mem h.mem_left, clusterRank_of_mem h.mem_right, lowerSet_eq ht h]

theorem clusterRank_lt_of_lt (ht : 0 ≤ t) (hx : x ∈ P) (hy : y ∈ P) (hxy : connRel M x y)
    (h : ¬SameCluster M P (near v t) x y) (hlt : v x < v y) :
    clusterRank M P (near v t) (fun a b => v a < v b) x <
      clusterRank M P (near v t) (fun a b => v a < v b) y := by
  rw [clusterRank_of_mem hx, clusterRank_of_mem hy]
  exact Nat.add_lt_add_right (card_lt_card (image_lowerSet_ssubset ht hx hxy h hlt)) 1

theorem clusterRank_le_iff_of_mem (ht : 0 ≤ t) (hx : x ∈ P) (hy : y ∈ P) (hxy : connRel M x y) :
    clusterRank M P (near v t) (fun a b => v a < v b) x ≤
      clusterRank M P (near v t) (fun a b => v a < v b) y ↔
      SameCluster M P (near v t) x y ∨ v x < v y := by
  refine ⟨fun hle => ?_, ?_⟩
  · by_contra! hcon
    obtain ⟨hn, hyx⟩ := hcon
    rcases hyx.lt_or_eq with hyx | hyx
    · exact (clusterRank_lt_of_lt ht hy hx (Conn.connRel_symm hxy)
        (fun h' => hn (h'.symm near_comm)) hyx).not_ge hle
    · exact hn (.of_link hx hy hxy (near_of_eq ht hyx.symm))
  · rintro (h | h)
    · exact (clusterRank_eq_of_sameCluster ht h).le
    · by_cases hs : SameCluster M P (near v t) x y
      · exact (clusterRank_eq_of_sameCluster ht hs).le
      · exact (clusterRank_lt_of_lt ht hx hy hxy hs h).le

theorem clusterRank_eq_iff_of_mem (ht : 0 ≤ t) (hx : x ∈ P) (hy : y ∈ P) (hxy : connRel M x y) :
    clusterRank M P (near v t) (fun a b => v a < v b) x =
      clusterRank M P (near v t) (fun a b => v a < v b) y ↔ SameCluster M P (near v t) x y := by
  refine ⟨fun heq => ?_, clusterRank_eq_of_sameCluster ht⟩
  by_contra hn
  rcases lt_trichotomy (v x) (v y) with hlt | heq' | hgt
  · exact (clusterRank_lt_of_lt ht hx hy hxy hn hlt).ne heq
  · exact hn (.of_link hx hy hxy (near_of_eq ht heq'))
  · exact (clusterRank_lt_of_lt ht hy hx (Conn.connRel_symm hxy)
      (fun h' => hn (h'.symm near_comm)) hgt).ne heq.symm

theorem clusterRank_lt_iff_of_mem (ht : 0 ≤ t) (hx : x ∈ P) (hy : y ∈ P) (hxy : connRel M x y) :
    clusterRank M P (near v t) (fun a b => v a < v b) x <
      clusterRank M P (near v t) (fun a b => v a < v b) y ↔
      ¬SameCluster M P (near v t) x y ∧ v x < v y := by
  rw [lt_iff_le_and_ne, clusterRank_le_iff_of_mem ht hx hy hxy, Ne,
    clusterRank_eq_iff_of_mem ht hx hy hxy]
  tauto

/-- At scale `0` a cluster has one value. -/
theorem SameCluster.eq_of_scale_zero (h : SameCluster M P (near v 0) x y) : v x = v y := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => rfl
  | tail _ hl ih =>
    have h' := hl.2.2.2
    rw [near, abs_nonpos_iff, sub_eq_zero] at h'
    exact ih.trans h'

/-- Clusters grow with `P` and `t`. -/
theorem SameCluster.mono {P' : Set (Fin m)} {t' : ℝ} (hP : P ⊆ P') (htt' : t ≤ t')
    (h : SameCluster M P (near v t) x y) : SameCluster M P' (near v t') x y := by
  refine ⟨hP h.1, ?_⟩
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail ⟨hP hab.1, hP hab.2.1, hab.2.2.1, hab.2.2.2.trans htt'⟩

end Values

/-! ### The weight `u_t` -/

section Weight

variable {v : Fin m → ℝ} {t : ℝ} {x y e : Fin m}

theorem u_of_notMem (he : e ∉ PO M v t) : u M v t e = m + 1 :=
  clusterRank_of_notMem he

theorem one_le_u : 1 ≤ u M v t e :=
  one_le_clusterRank

/-- `u_t(e) ≤ m` exactly for `e ∈ PO_t`. -/
theorem u_le_iff_mem : u M v t e ≤ m ↔ e ∈ PO M v t :=
  clusterRank_le_iff

theorem u_le_succ : u M v t e ≤ m + 1 := by
  by_cases he : e ∈ PO M v t
  · exact (u_le_iff_mem.2 he).trans (Nat.le_succ m)
  · rw [u_of_notMem he]

theorem u_eq_u_of_sameCluster (ht : 0 ≤ t) (h : SameCluster M (PO M v t) (near v t) x y) :
    u M v t x = u M v t y :=
  clusterRank_eq_of_sameCluster ht h

/-- For `x, y ∈ PO_t` in one component, `u_t(x) ≤ u_t(y)` iff `x` and `y` share a cluster or
`v_x < v_y`. -/
theorem u_le_u_iff (ht : 0 ≤ t) (hx : x ∈ PO M v t) (hy : y ∈ PO M v t) (hxy : connRel M x y) :
    u M v t x ≤ u M v t y ↔ SameCluster M (PO M v t) (near v t) x y ∨ v x < v y :=
  clusterRank_le_iff_of_mem ht hx hy hxy

/-- For `x, y ∈ PO_t` in one component, `u_t(x) = u_t(y)` iff `x` and `y` share a cluster. -/
theorem u_eq_u_iff (ht : 0 ≤ t) (hx : x ∈ PO M v t) (hy : y ∈ PO M v t) (hxy : connRel M x y) :
    u M v t x = u M v t y ↔ SameCluster M (PO M v t) (near v t) x y :=
  clusterRank_eq_iff_of_mem ht hx hy hxy

/-- `u_t(x) < u_t(y)` for `x`, `y` in one component iff `x ∈ PO_t ∌ y`, or `x, y ∈ PO_t` lie in
different clusters with `v_x < v_y`. -/
theorem u_lt_u_iff (ht : 0 ≤ t) (hxy : connRel M x y) :
    u M v t x < u M v t y ↔ (x ∈ PO M v t ∧ y ∉ PO M v t) ∨
      (x ∈ PO M v t ∧ y ∈ PO M v t ∧ ¬SameCluster M (PO M v t) (near v t) x y ∧ v x < v y) := by
  by_cases hx : x ∈ PO M v t
  · by_cases hy : y ∈ PO M v t
    · rw [show u M v t x < u M v t y ↔ _ from clusterRank_lt_iff_of_mem ht hx hy hxy]
      simp [hx, hy]
    · refine iff_of_true ?_ (.inl ⟨hx, hy⟩)
      rw [u_of_notMem hy]
      exact Nat.lt_succ_of_le (u_le_iff_mem.2 hx)
  · refine iff_of_false ?_ (by simp [hx])
    rw [u_of_notMem hx, not_lt]
    exact u_le_succ

open Classical in
/-- The clusters at scale `t` of the component of `e`. -/
noncomputable def clusters (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) (e : Fin m) :
    Finset (Finset (Fin m)) :=
  (univ.filter fun y => y ∈ PO M v t ∧ connRel M y e).image (cluster M (PO M v t) (near v t))

/-- **`u_t(e)` is the rank of the cluster of `e`**: for `e ∈ PO_t`, `u_t(e) - 1` is the number of
clusters of the component of `e` lying below the cluster of `e`, all of whose values are smaller
than all values of the cluster of `e`. -/
theorem u_eq_card_add_one (ht : 0 ≤ t) (he : e ∈ PO M v t) :
    u M v t e = #((clusters M v t e).filter fun C =>
      ∀ a ∈ C, ∀ b ∈ cluster M (PO M v t) (near v t) e, v a < v b) + 1 := by
  rw [u, clusterRank_of_mem he]
  congr 2
  ext C
  simp only [clusters, mem_image, mem_filter, mem_univ, true_and, mem_lowerSet]
  constructor
  · rintro ⟨y, ⟨hy, hye, hn, hlt⟩, rfl⟩
    refine ⟨⟨y, ⟨hy, hye⟩, rfl⟩, fun a ha b hb => ?_⟩
    linarith [lt_sub_of_not_sameCluster ht hye hn hlt (mem_cluster.1 ha) (mem_cluster.1 hb)]
  · rintro ⟨⟨y, ⟨hy, hye⟩, rfl⟩, hbelow⟩
    refine ⟨y, ⟨hy, hye, fun h => ?_, hbelow y (mem_cluster.2 (.refl hy)) e
      (mem_cluster.2 (.refl he))⟩, rfl⟩
    exact lt_irrefl _ (hbelow e (mem_cluster.2 h) e (mem_cluster.2 (.refl he)))

end Weight

/-! ### `PO_t` -/

section PO

variable {v : Fin m → ℝ} {t t' : ℝ} {B : Finset (Fin m)} {e f : Fin m}

/-- Induction on the value of `v`. -/
theorem value_induction (v : Fin m → ℝ) {p : Fin m → Prop}
    (h : ∀ e, (∀ g, v g < v e → p g) → p e) (e : Fin m) : p e := by
  induction hn : #(univ.filter fun x => v x < v e) using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    refine h e fun g hg => ih _ ?_ g rfl
    rw [← hn]
    refine card_lt_card ((ssubset_iff_of_subset fun x hx => ?_).2 ⟨g, ?_, ?_⟩)
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.trans hg
    · simpa using hg
    · simp

theorem PO_mono (h : t ≤ t') : PO M v t ⊆ PO M v t' := fun f hf hcl =>
  hf (M.closure_subset_closure (fun g (hg : v g < v f - t') => show v g < v f - t by linarith) hcl)

/-- The elements of a minimum base of `v` lie in `PO_0 ⊆ PO_t`. -/
theorem subset_PO_of_isMinBase (hE : M.E = Set.univ) (hB : IsMinBase M v B) (ht : 0 ≤ t) :
    (B : Set (Fin m)) ⊆ PO M v t := by
  intro f hf
  refine PO_mono ht ?_
  show f ∉ M.closure {g | v g < v f - 0}
  rw [sub_zero, ← (hB.isBasis_lt hE (v f)).closure_eq_closure]
  intro hcl
  refine hB.1.indep.notMem_closure_sdiff_of_mem hf (M.closure_subset_closure ?_ hcl)
  rintro g ⟨hgB, hg⟩
  refine ⟨hgB, fun hgf => ?_⟩
  rw [Set.mem_singleton_iff.1 hgf] at hg
  exact lt_irrefl (v f) hg

/-- `PO_0` is the set of elements of minimum bases of `v`. -/
theorem mem_PO_zero_iff (hE : M.E = Set.univ) : f ∈ PO M v 0 ↔ ∃ B, IsMinBase M v B ∧ f ∈ B := by
  refine ⟨fun hf => ?_, fun ⟨B, hB, hfB⟩ => subset_PO_of_isMinBase hE hB le_rfl hfB⟩
  obtain ⟨B, hB⟩ := exists_isMinBase M v
  by_cases hfB : f ∈ B
  · exact ⟨B, hB, hfB⟩
  have hC := hB.1.fundCircuit_isCircuit (by simp [hE]) (by simpa using hfB)
  obtain ⟨g, hgC, hgf, hg⟩ : ∃ g ∈ M.fundCircuit f ↑B, g ≠ f ∧ ¬v g < v f := by
    by_contra! hcon
    refine hf (M.closure_subset_closure (fun g hg => ?_)
      (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit f ↑B)))
    show v g < v f - 0
    rw [sub_zero]
    exact hcon g hg.1 hg.2
  have hgB := Pos.mem_of_mem_fundCircuit hgC hgf
  refine ⟨insert f (B.erase g), (hB.isMinBase_exchange_iff hE hfB hgB).2
    ⟨hgC, le_antisymm (Conn.le_of_mem_fundCircuit hB hfB hgC) (not_lt.1 hg)⟩, mem_insert_self f _⟩

/-- `PO_t` spans every element within its component. -/
theorem mem_closure_PO (hE : M.E = Set.univ) (ht : 0 ≤ t) (e : Fin m) :
    e ∈ M.closure (PO M v t ∩ ↑(Conn.comp M e)) := by
  obtain ⟨B, hB⟩ := exists_isMinBase M v
  have he : e ∈ M.closure ↑B := by
    rw [hB.1.closure_eq, hE]
    trivial
  exact M.closure_subset_closure (Set.inter_subset_inter_left _ (subset_PO_of_isMinBase hE hB ht))
    (Conn.mem_closure_iff_comp.1 he)

/-- A minimum base of `u_t` lies in `PO_t`. -/
theorem subset_PO_of_isMinBase_u (hE : M.E = Set.univ) (ht : 0 ≤ t)
    (hB : IsMinBase M (fun e => (u M v t e : ℝ)) B) : (B : Set (Fin m)) ⊆ PO M v t := by
  have hspan : PO M v t ⊆ M.closure (↑B ∩ PO M v t) := by
    intro e he
    have h := hB.subset_closure_le hE m (show (u M v t e : ℝ) ≤ m by
      exact_mod_cast u_le_iff_mem.2 he)
    refine M.closure_subset_closure (Set.inter_subset_inter_right _ fun g hg => ?_) h
    exact u_le_iff_mem.1 (by exact_mod_cast hg)
  intro f hfB
  by_contra hf
  have h := M.closure_subset_closure_of_subset_closure hspan
    (M.closure_subset_closure Set.inter_subset_left (mem_closure_PO hE ht f))
  refine hB.1.indep.notMem_closure_sdiff_of_mem hfB (M.closure_subset_closure ?_ h)
  refine fun g hg => ⟨hg.1, fun hgf => hf ?_⟩
  rw [← Set.mem_singleton_iff.1 hgf]
  exact hg.2

/-- `N(t) = M^{u_t}`: its bases are the minimum bases of `u_t`. -/
theorem isBase_N_iff (hE : M.E = Set.univ) :
    (N M v t).IsBase ↑B ↔ IsMinBase M (fun e => (u M v t e : ℝ)) B :=
  isBase_minBases_iff hE

/-- A base of `N(t)` lies in `PO_t`. -/
theorem subset_PO_of_isBase_N (hE : M.E = Set.univ) (ht : 0 ≤ t) (hB : (N M v t).IsBase ↑B) :
    (B : Set (Fin m)) ⊆ PO M v t :=
  subset_PO_of_isMinBase_u hE ht ((isBase_N_iff hE).1 hB)

/-- A base of `M^v` lies in `PO_0 ⊆ PO_t`. -/
theorem subset_PO_of_isBase_minBases (hE : M.E = Set.univ) (ht : 0 ≤ t)
    (hB : (minBases M v).IsBase ↑B) : (B : Set (Fin m)) ⊆ PO M v t :=
  subset_PO_of_isMinBase hE ((isBase_minBases_iff hE).1 hB) ht

/-- An element of a circuit with a second element is not a loop. -/
theorem notMem_closure_empty {C : Set (Fin m)} (hC : M.IsCircuit C) {g g' : Fin m} (hg : g ∈ C)
    (hg' : g' ∈ C) (hne : g ≠ g') : g ∉ M.closure ∅ := fun hcl => by
  have hC' := (Matroid.singleton_isCircuit.2 hcl).eq_of_subset_isCircuit hC
    (Set.singleton_subset_iff.2 hg)
  rw [← hC'] at hg'
  exact hne (Set.mem_singleton_iff.1 hg').symm

end PO

/-! ### Proposition `prop:posl` -/

section Admissible

variable {v : Fin m → ℝ} {t t' : ℝ} {B : Finset (Fin m)}

/-- Two weights with the same minimum bases have the same matroid `M^w`. -/
theorem minBases_ext (hE : M.E = Set.univ) {w w' : Fin m → ℝ}
    (h : ∀ B, IsMinBase M w B ↔ IsMinBase M w' B) : minBases M w = minBases M w' :=
  Matroid.ext_isBase (by rw [Conn.minBases_ground, Conn.minBases_ground]) fun X _ => by
    obtain ⟨B, rfl⟩ := exists_finset X
    rw [isBase_minBases_iff hE, isBase_minBases_iff hE, h]

/-- **Proposition `prop:posl`, (F3)**: `P_t ⊆ Bases(N(t))`. -/
theorem isBase_N_of_mem_Pos (hE : M.E = Set.univ) (hB : B ∈ Pos M v t) :
    (N M v t).IsBase ↑B := by
  have ht : 0 ≤ t := Pos.theta_nonneg.trans hB.2
  have h4 := ((Pos.tfae_pos hE hB.1 ht).out 0 3).1 hB.2
  -- Step 1: `B ⊆ PO_t`
  have hBPO : ∀ f ∈ B, f ∈ PO M v t := by
    intro f hf hcl
    refine hB.1.indep.notMem_closure_sdiff_of_mem hf (M.closure_subset_closure_of_subset_closure
      (fun g (hg : v g < v f - t) => M.closure_subset_closure ?_ (h4 g)) hcl)
    rintro x ⟨hxB, hx⟩
    refine ⟨hxB, fun hxf => ?_⟩
    rw [Set.mem_singleton_iff.1 hxf, Set.mem_setOf_eq] at hx
    linarith
  -- Step 2: no exchange improves `u_t`
  rw [N, isBase_minBases_iff hE]
  refine Conn.isMinBase_of_forall_fundCircuit hB.1 fun e he f hf => ?_
  obtain rfl | hfe := eq_or_ne f e
  · exact le_rfl
  have hfPO := hBPO f (Pos.mem_of_mem_fundCircuit hf hfe)
  show (u M v t f : ℝ) ≤ u M v t e
  rw [Nat.cast_le]
  by_cases hePO : e ∈ PO M v t
  · have hfe' : connRel M f e :=
      Conn.connRel_symm (Conn.mem_comp.1 (Conn.fundCircuit_subset_comp hB.1 e hf))
    refine (u_le_u_iff ht hfPO hePO hfe').2 ?_
    rcases lt_or_ge (v f) (v e) with hlt | hge
    · exact .inr hlt
    · refine .inl (.of_link hfPO hePO hfe' ?_)
      have := (Pos.theta_le_iff.1 hB.2).2 e he f hf
      rw [near, abs_le]
      constructor <;> linarith
  · rw [u_of_notMem hePO]
    exact u_le_succ

/-- **Proposition `prop:posl`, (F1)**: `N(0) = M^v`. -/
theorem N_zero (hE : M.E = Set.univ) : N M v 0 = minBases M v := by
  refine minBases_ext hE fun B => ⟨fun hB => ?_, fun hB => ?_⟩
  · have hBPO := subset_PO_of_isMinBase_u hE le_rfl hB
    refine isMinBase_of_forall_mem_closure hB.1 (value_induction v fun e ih => ?_)
    by_cases heB : e ∈ B
    · exact M.mem_closure_of_mem' ⟨heB, le_refl (v e)⟩ (by simp [hE])
    by_cases he : e ∈ PO M v 0
    · have hC := hB.1.fundCircuit_isCircuit (by simp [hE]) (by simpa using heB)
      refine M.closure_subset_closure (fun f hf => ?_)
        (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit e ↑B))
      have hfB := Pos.mem_of_mem_fundCircuit hf.1 hf.2
      have hle : u M v 0 f ≤ u M v 0 e := by
        exact_mod_cast Conn.le_of_mem_fundCircuit hB heB hf.1
      have hfe : connRel M f e :=
        Conn.connRel_symm (Conn.mem_comp.1 (Conn.fundCircuit_subset_comp hB.1 e hf.1))
      refine ⟨hfB, ?_⟩
      rcases (u_le_u_iff le_rfl (hBPO hfB) he hfe).1 hle with h | h
      · exact h.eq_of_scale_zero.le
      · exact h.le
    · have hcl : e ∈ M.closure {g | v g < v e - 0} := not_not.1 he
      refine M.closure_subset_closure_of_subset_closure (fun g (hg : v g < v e - 0) => ?_) hcl
      exact M.closure_subset_closure (Set.inter_subset_inter_right _
        fun x (hx : v x ≤ v g) => show v x ≤ v e by linarith) (ih g (by linarith))
  · have hB' : B ∈ Pos M v 0 := (Pos.mem_pos_zero hE).2 ((isBase_minBases_iff hE).2 hB)
    exact (isBase_minBases_iff hE).1 (isBase_N_of_mem_Pos hE hB')

/-- **Proposition `prop:posl`, (F2)**: every base of `N(t)` is a base of `N(t')` for
`0 ≤ t ≤ t'`. -/
theorem isBase_N_mono (hE : M.E = Set.univ) (ht : 0 ≤ t) (htt' : t ≤ t')
    (hB : (N M v t).IsBase ↑B) : (N M v t').IsBase ↑B := by
  rw [N, isBase_minBases_iff hE] at hB ⊢
  have ht' : 0 ≤ t' := ht.trans htt'
  have hBPO := subset_PO_of_isMinBase_u hE ht hB
  refine Conn.isMinBase_of_forall_fundCircuit hB.1 fun e he f hf => ?_
  obtain rfl | hfe := eq_or_ne f e
  · exact le_rfl
  have hfPO : f ∈ PO M v t := hBPO (Pos.mem_of_mem_fundCircuit hf hfe)
  have hfe' : connRel M f e :=
    Conn.connRel_symm (Conn.mem_comp.1 (Conn.fundCircuit_subset_comp hB.1 e hf))
  show (u M v t' f : ℝ) ≤ u M v t' e
  rw [Nat.cast_le]
  by_cases he' : e ∈ PO M v t'
  swap
  · rw [u_of_notMem he']
    exact u_le_succ
  have hfPO' := PO_mono htt' hfPO
  refine (u_le_u_iff ht' hfPO' he' hfe').2 ?_
  -- Case `e ∈ PO_t`: the order of `u_t` persists
  by_cases heT : e ∈ PO M v t
  · have hle : u M v t f ≤ u M v t e := by exact_mod_cast Conn.le_of_mem_fundCircuit hB he hf
    exact ((u_le_u_iff ht hfPO heT hfe').1 hle).imp_left (SameCluster.mono (PO_mono htt') htt')
  -- Case `v_f ≤ v_e`
  rcases le_or_gt (v f) (v e) with hfe2 | hef
  · rcases hfe2.lt_or_eq with h | h
    · exact .inr h
    · exact .inl (.of_link hfPO' he' hfe' (near_of_eq ht' h))
  -- Case `e ∈ PO_{t'} \ PO_t` and `v_e < v_f`: every element of the component of `e` below
  -- `v_e - t` is spanned by elements of `B` whose `u_t` is at most that of some `x ∈ PO_t` of
  -- the component with `v_x < v_e - t`
  have hspan : ∀ g, connRel M e g → v g < v e - t → g ∈ M.closure
      {h | h ∈ B ∧ ∃ x ∈ PO M v t, connRel M e x ∧ v x < v e - t ∧ u M v t h ≤ u M v t x} := by
    refine value_induction v fun g ih hg hgv => ?_
    by_cases hgB : g ∈ B
    · refine M.mem_closure_of_mem' ?_ (by simp [hE])
      exact ⟨hgB, g, hBPO hgB, hg, hgv, le_rfl⟩
    by_cases hgPO : g ∈ PO M v t
    · have hC := hB.1.fundCircuit_isCircuit (by simp [hE]) (by simpa using hgB)
      refine M.closure_subset_closure (fun h hh => ?_)
        (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit g ↑B))
      refine ⟨Pos.mem_of_mem_fundCircuit hh.1 hh.2, g, hgPO, hg, hgv, ?_⟩
      exact_mod_cast Conn.le_of_mem_fundCircuit hB hgB hh.1
    · have hcl : g ∈ M.closure {h | v h < v g - t} := not_not.1 hgPO
      rw [Conn.mem_closure_iff_comp] at hcl
      refine M.closure_subset_closure_of_subset_closure (fun h hh => ?_) hcl
      have hh' : v h < v g - t := hh.1
      exact ih h (by linarith) (Conn.connRel_trans hg (Conn.mem_comp.1 hh.2)) (by linarith)
  have heZ : e ∈ M.closure
      {h | h ∈ B ∧ ∃ x ∈ PO M v t, connRel M e x ∧ v x < v e - t ∧ u M v t h ≤ u M v t x} := by
    have hcl : e ∈ M.closure {g | v g < v e - t} := not_not.1 heT
    rw [Conn.mem_closure_iff_comp] at hcl
    exact M.closure_subset_closure_of_subset_closure
      (fun g hg => hspan g (Conn.mem_comp.1 hg.2) hg.1) hcl
  obtain ⟨-, x, hxPO, hex, hxv, hfx⟩ := (Set.mem_insert_iff.1
    (fundCircuit_subset_insert_of_mem_closure (fun h hh => hh.1) heZ hf)).resolve_left hfe
  -- `f` shares a cluster with `x` at scale `t`, and `e` lies between them
  have hsc : SameCluster M (PO M v t) (near v t) f x := by
    rcases (u_le_u_iff ht hfPO hxPO (Conn.connRel_trans hfe' hex)).1 hfx with h | h
    · exact h
    · exact absurd h (by linarith)
  have hsc' := (hsc.mono (PO_mono htt') htt').symm near_comm
  exact .inl ((hsc'.symm near_comm).trans
    (hsc'.of_le_of_le ht' he' (Conn.connRel_symm hex) (by linarith) hef.le))

/-- **Proposition `prop:posl`, (F4)**: if `v_f - v_e ≤ t` for all `e, f`, then `N(t) = M`. -/
theorem N_eq_self (hE : M.E = Set.univ) (h : ∀ e f, v f - v e ≤ t) : N M v t = M := by
  refine minBases_eq_self hE fun e f hef => ?_
  have ht : 0 ≤ t := by linarith [h e e]
  obtain rfl | hne := eq_or_ne e f
  · rfl
  obtain ⟨C, hC, heC, hfC⟩ := hef.resolve_left hne
  -- the elements of a circuit with two elements are not loops, so they lie in `PO_t`
  have hPO : ∀ g g', g ∈ C → g' ∈ C → g ≠ g' → g ∈ PO M v t := by
    intro g g' hg hg' hgg' hcl
    have hempty : {x | v x < v g - t} = (∅ : Set (Fin m)) :=
      Set.eq_empty_of_forall_notMem fun x (hx : v x < v g - t) => by linarith [h x g]
    rw [hempty] at hcl
    exact notMem_closure_empty hC hg hg' hgg' hcl
  have he := hPO e f heC hfC hne
  have hf := hPO f e hfC heC hne.symm
  have heq : u M v t e = u M v t f := u_eq_u_of_sameCluster ht (.of_link he hf hef (by
    rw [near, abs_le]
    constructor <;> linarith [h e f, h f e]))
  show (u M v t e : ℝ) = u M v t f
  rw [heq]

theorem PO_eq_of_levels (ht : 0 ≤ t) (htt' : t ≤ t') (h : ∀ x ∈ levels v, ¬(t < x ∧ x ≤ t')) :
    PO M v t = PO M v t' := by
  refine (PO_mono htt').antisymm fun f hf hcl => hf ?_
  have hset : {g | v g < v f - t'} = {g | v g < v f - t} := by
    ext g
    simp only [Set.mem_setOf_eq]
    refine ⟨fun hg => by linarith, fun hg => lt_of_not_ge fun hg' =>
      h |v f - v g| (abs_sub_mem_levels v f g) ?_⟩
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  rwa [hset]

theorem near_eq_of_levels (htt' : t ≤ t') (h : ∀ x ∈ levels v, ¬(t < x ∧ x ≤ t')) :
    near v t = near v t' := by
  funext a b
  exact propext ⟨fun hab => le_trans hab htt', fun hab => le_of_not_gt fun hn =>
    h _ (abs_sub_mem_levels v a b) ⟨hn, hab⟩⟩

/-- **Proposition `prop:posl`, (F5)**: `N` is constant on every interval `[t, t']`, `t ≥ 0`, with
no level `{0} ∪ {|v_e - v_f|}` in `(t, t']`. -/
theorem N_eq_N_of_levels (ht : 0 ≤ t) (htt' : t ≤ t') (h : ∀ x ∈ levels v, ¬(t < x ∧ x ≤ t')) :
    N M v t = N M v t' := by
  unfold N u
  rw [PO_eq_of_levels ht htt' h, near_eq_of_levels htt' h]

/-- `PO_t = PO_{G_t}`: `v_g < v_f - t` iff `(g, f) ∉ G_t`. -/
theorem PO_eq_POG (v : Fin m → ℝ) (t : ℝ) : PO M v t = POG M (Gt v t) := by
  ext f
  have hset : {g | v g < v f - t} = {g | (g, f) ∉ Gt v t} := by
    ext g
    simp only [Gt, mem_filter, mem_univ, true_and, not_le, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  simp only [PO, POG, Set.mem_setOf_eq, hset]

/-- The links at scale `t` are read from `G_t`: `|v_x - v_y| ≤ t` iff `(x, y), (y, x) ∈ G_t`. -/
theorem near_eq_linkG (v : Fin m → ℝ) (t : ℝ) : near v t = linkG (Gt v t) := by
  funext x y
  refine propext ?_
  simp only [near, linkG, Gt, mem_filter, mem_univ, true_and, abs_sub_le_iff]
  exact and_comm

/-- The order of two clusters of a component is read from `G_t`: for `y, e ∈ PO_t` in one
component and in different clusters, `v_y < v_e` iff `(y, e) ∉ G_t`. -/
theorem lt_iff_notMem_Gt (ht : 0 ≤ t) {y e : Fin m} (hy : y ∈ PO M v t) (he : e ∈ PO M v t)
    (hye : connRel M y e) (hn : ¬SameCluster M (PO M v t) (near v t) y e) :
    v y < v e ↔ (y, e) ∉ Gt v t := by
  have h := lt_abs_sub hye hn (.refl hy) (.refl he)
  simp only [Gt, mem_filter, mem_univ, true_and, not_le]
  refine ⟨fun hlt => ?_, fun h' => by linarith⟩
  rwa [abs_sub_comm, abs_of_pos (sub_pos.2 hlt)] at h

/-- `u_t = u_{G_t}` for `t ≥ 0`. -/
theorem u_eq_uG (ht : 0 ≤ t) : u M v t = uG M (Gt v t) := by
  unfold u uG
  rw [← PO_eq_POG, ← near_eq_linkG]
  exact clusterRank_congr fun y e hy he hye hn => lt_iff_notMem_Gt ht hy he hye hn

/-- **Proposition `prop:posl`, determined by `G_t`**: `N(t) = N_{G_t}` for `t ≥ 0`. -/
theorem N_eq_NG (ht : 0 ≤ t) : N M v t = NG M (Gt v t) := by
  rw [N, NG, u_eq_uG ht]

/-- `N(t)` depends only on `G_t`: if `G_t(v) = G_{t'}(v')`, then `N_v(t) = N_{v'}(t')`. -/
theorem N_eq_of_Gt_eq {v' : Fin m → ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (h : Gt v t = Gt v' t') :
    N M v t = N M v' t' := by
  rw [N_eq_NG ht, N_eq_NG ht', h]

/-- At the full relation `G = E × E`, `N_G = M` (Lemma `lem:observer`, Step 5): `PO_G` is the
set of non-loops, and no cluster lies below another, so `u_G` is constant on every component. -/
theorem NG_univ (hE : M.E = Set.univ) : NG M univ = M := by
  refine minBases_eq_self hE fun e f hef => ?_
  obtain rfl | hne := eq_or_ne e f
  · rfl
  obtain ⟨C, hC, heC, hfC⟩ := hef.resolve_left hne
  have h1 : ∀ g g', g ∈ C → g' ∈ C → g ≠ g' → uG M univ g = 1 := by
    intro g g' hg hg' hgg'
    have hgPO : g ∈ POG M univ := fun hcl => by
      have hempty : {x | (x, g) ∉ (univ : Finset (Fin m × Fin m))} = (∅ : Set (Fin m)) := by
        simp
      rw [hempty] at hcl
      exact notMem_closure_empty hC hg hg' hgg' hcl
    have hL : lowerSet M (POG M univ) (linkG univ) (fun y e => (y, e) ∉ univ) g = ∅ := by
      ext y
      simp [mem_lowerSet]
    rw [uG, clusterRank_of_mem hgPO, hL, image_empty, card_empty]
  show (uG M univ e : ℝ) = uG M univ f
  rw [h1 e f heC hfC hne, h1 f e hfC heC hne.symm]

/-- **Proposition `prop:posl`, admissibility**: if `M` has a rainbow base, the family `N(t)` of
Definition `def:posl` satisfies (F1) to (F5).  The paper states it for `v` with `ν₀ < k`, the
standing hypothesis of Definition `def:admissible`; it holds for every `v`. -/
theorem isAdmissible (hE : M.E = Set.univ) {blk : Fin m → Fin k}
    (hM : ∃ B, IsRainbowBase M blk B) (v : Fin m → ℝ) : IsAdmissible M blk v (N M v) where
  ground _ _ := Conn.minBases_ground M _
  F1 := N_zero hE
  F2 _ _ ht htt' _ hB := isBase_N_mono hE ht htt' hB
  F3 _ _ _ hB := isBase_N_of_mem_Pos hE hB
  F4 := by
    refine ⟨(levels v).max' ⟨0, zero_mem_levels v⟩, le_max' _ 0 (zero_mem_levels v),
      fun t ht => ?_⟩
    rw [N_eq_self hE fun e f => ?_]
    · exact hM
    · calc v f - v e ≤ |v f - v e| := le_abs_self _
        _ ≤ (levels v).max' ⟨0, zero_mem_levels v⟩ := le_max' _ _ (abs_sub_mem_levels v f e)
        _ ≤ t := ht
  F5 := ⟨levels v, zero_mem_levels v, fun _ _ ht htt' h => N_eq_N_of_levels ht htt' h⟩

/-- **Proposition `prop:posl`** (first two sentences).  Let `M` have a rainbow base.  For every
`v` (in particular for every `v` with `ν₀ < k`), the family `N(t)` of Definition `def:posl` is
admissible, it is constant on every interval `[t, t']`, `t ≥ 0`, with no level
`{0} ∪ {|v_e - v_f| : e, f ∈ E}` in `(t, t']`, and it is determined by `G_t`: `N(t) = N_{G_t}`
for `t ≥ 0`. -/
theorem prop_posl (hE : M.E = Set.univ) {blk : Fin m → Fin k} (hM : ∃ B, IsRainbowBase M blk B)
    (v : Fin m → ℝ) :
    IsAdmissible M blk v (N M v) ∧
      (∀ t t', 0 ≤ t → t ≤ t' → (∀ x ∈ levels v, ¬(t < x ∧ x ≤ t')) → N M v t = N M v t') ∧
      ∀ t, 0 ≤ t → N M v t = NG M (Gt v t) :=
  ⟨isAdmissible hE hM v, fun _ _ ht htt' h => N_eq_N_of_levels ht htt' h, fun _ ht => N_eq_NG ht⟩

end Admissible

end SignedTropical.Rainbow.POSL
