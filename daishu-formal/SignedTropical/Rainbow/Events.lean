import SignedTropical.Rainbow.POSL
import SignedTropical.Integral
import SignedTropical.BoolAlg.Rel

/-!
# Event levels of the PO-SL family

`greedy_intersection.tex`, Lemma `lem:events`.  `M : Matroid (Fin m)`, `v : Fin m → ℝ`, `t ≥ 0`.
The family `N(t)` of Definition `def:posl` is read from `PO_t`, the clusters and the order of the
clusters.  Each of them changes at one value of `t`, and these values lie in a list of at most
`2m` levels computed from `v` without comparisons.

* **Entry times** (`entry`, `mem_PO_iff`): for a nonloop `x`, with `D^x_g = max(v_x - v_g, 0)`
  (`dx`), the gap sum `t_x = C_φ(D^x)` of `φ(S) = [x ∈ cl(E - S)]` satisfies
  `x ∈ PO_t ⟺ t_x ≤ t`.  This is the general fact `gapSum_antitone`: for an antitone `φ` with
  `¬φ(E)`, `φ(G_t(D))` holds exactly for `t` below the gap sum.
* **Merge times** (`bott`, `sameCluster_iff`): for nonloops `a, b` of one component
  (`Kr M a b`) put `W_aa = t_a` and `W_ab = max(t_a, t_b, |v_a - v_b|)`; the Floyd–Warshall
  algorithm over `(min, max)` (`fwV`) gives `T`, and `x`, `y` lie in one cluster at `t` iff
  `Kr M x y` and `T_xy ≤ t`.  The algorithm commutes with thresholds (`thr_fwV`): at every `t`,
  `[T ≤ t]` is Warshall's algorithm (`BoolAlg.warshallV`) run on `[W ≤ t]`, so
  `T_ab ≤ t` iff a chain of links at scale `t` joins `a` and `b` (`fwV_le_iff`).
* **The levels** (`lev`): `t_x` (`0` at a loop) and `ρ_x = min_{y < x, Kr M x y} T_xy`
  (`rho`; `0` if there is no such `y`), `2m` values.  **Covering** (`bott_inLev`): every `T_xy`
  is one of them, or `0`.  Let `h = T_xy`, `C` the cluster of `x` at `h`, and assume no element
  of `C` enters at `h`.  The relation `T < h` splits `C` into classes, `x` and `y` in different
  ones; for a class `P` avoiding the least element of `C`, its least element `z` has `ρ_z = h`.
* **The order** (`uval`, `ord_iff`): with `U_xy = max(t_x, t_y, min(T_xy, v_y - v_x))`, which is
  again one of the levels (`uval_inLev`), for `Kr M x y` the order bit of Step 1 of Lemma
  `lem:observer`, `x ∈ PO_t ∧ (y ∉ PO_t ∨ (x, y in different clusters ∧ v_y - v_x > t))`, is
  `t_x ≤ t < U_xy`.

So the bits `[t_x ≤ t]`, `[T_xy ≤ t]`, `[U_xy ≤ t]` describe `N(t)` at every `t ≥ 0`, and each
of them changes only at a level: `N(t)` is constant between consecutive levels.
-/

open Finset

namespace SignedTropical.Rainbow.Events

open SignedTropical SignedTropical.Rainbow SignedTropical.Rainbow.POSL SignedTropical.BoolAlg

variable {m : ℕ}

/-! ### The gap sum of an antitone threshold -/

section Antitone

variable {D : Fin m → ℝ}

/-- The threshold sets increase. -/
theorem threshSet_mono (hD : ∀ e, 0 ≤ D e) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    threshSet D i ⊆ threshSet D j := fun e he => by
  simp only [threshSet, mem_filter, mem_univ, true_and] at he ⊢
  exact he.trans (sortedVal_mono hD hij hj)

open Classical in
/-- **The gap sum of an antitone threshold.**  For `D ≥ 0` and `φ` antitone with `¬φ(E)`, the gap
sum of `[φ]` is a sorted value `s_j`, and `φ(G_t(D))` holds exactly for `t < s_j`, `t ≥ 0`. -/
theorem gapSum_antitone (hD : ∀ e, 0 ≤ D e) {φ : Finset (Fin m) → Prop}
    (hφ : ∀ S S', S ⊆ S' → φ S' → φ S) (hE : ¬φ univ) :
    ∃ j ≤ m, gapSum (fun S => if φ S then 1 else 0) D = sortedVal D j ∧
      ∀ t, 0 ≤ t → (φ (Integral.sublevel D t) ↔ t < sortedVal D j) := by
  have hex : ∃ k, ¬φ (threshSet D k) :=
    ⟨m, by rwa [Integral.threshSet_eq_sublevel, Integral.sublevel_eq_univ hD le_rfl]⟩
  set j := Nat.find hex with hjdef
  have hj : j ≤ m := Nat.find_min' hex
    (by rwa [Integral.threshSet_eq_sublevel, Integral.sublevel_eq_univ hD le_rfl])
  have hlt : ∀ k < j, φ (threshSet D k) := fun k hk => not_not.1 (Nat.find_min hex hk)
  have hge : ∀ k, j ≤ k → k ≤ m → ¬φ (threshSet D k) := fun k hjk hkm h =>
    Nat.find_spec hex (hφ _ _ (threshSet_mono hD hjk hkm) h)
  refine ⟨j, hj, ?_, fun t ht => ⟨fun hφt => ?_, fun htj => ?_⟩⟩
  · have hterm : ∀ k ∈ range m, (sortedVal D (k + 1) - sortedVal D k) *
        (if φ (threshSet D k) then (1 : ℝ) else 0) =
        if k < j then sortedVal D (k + 1) - sortedVal D k else 0 := by
      intro k hk
      by_cases hkj : k < j
      · rw [if_pos (hlt k hkj), if_pos hkj, mul_one]
      · rw [if_neg (hge k (not_lt.1 hkj) (mem_range.1 hk).le), if_neg hkj, mul_zero]
    rw [gapSum, sum_congr rfl hterm, ← sum_filter, show (range m).filter (· < j) = range j by
      ext k; simp only [mem_filter, mem_range]; omega, sum_range_sub, sortedVal_zero, sub_zero]
  · by_contra hle
    refine Nat.find_spec hex (hφ _ _ (fun e he => ?_) hφt)
    simp only [threshSet, mem_filter, mem_univ, true_and] at he
    exact Integral.mem_sublevel.2 (he.trans (not_lt.1 hle))
  · have hj1 : 1 ≤ j := by
      by_contra h0
      rw [show j = 0 by omega, sortedVal_zero] at htj
      linarith
    refine hφ _ _ (fun e he => ?_) (hlt (j - 1) (by omega))
    obtain ⟨i, hi1, him, hie⟩ := exists_sortedVal_eq D e
    have hDe : D e ≤ t := Integral.mem_sublevel.1 he
    have hij : i ≤ j - 1 := by
      by_contra h
      have := sortedVal_mono hD (show j ≤ i by omega) him
      linarith
    simp only [threshSet, mem_filter, mem_univ, true_and]
    exact hie ▸ sortedVal_mono hD hij (by omega)

end Antitone

/-! ### Entry times -/

section Entry

variable {M : Matroid (Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y : Fin m}

/-- `D^x_g = max(v_x - v_g, 0)`. -/
noncomputable def dx (v : Fin m → ℝ) (x g : Fin m) : ℝ := max (v x - v g) 0

theorem dx_nonneg (v : Fin m → ℝ) (x g : Fin m) : 0 ≤ dx v x g := le_max_right _ _

open Classical in
/-- **The entry time** `t_x = C_φ(D^x)` of `φ(S) = [x ∈ cl(E - S)]` (`mem_PO_iff`). -/
noncomputable def entry (M : Matroid (Fin m)) (v : Fin m → ℝ) (x : Fin m) : ℝ :=
  gapSum (fun S => if x ∈ M.closure ((univ \ S : Finset (Fin m)) : Set (Fin m)) then 1 else 0)
    (dx v x)

/-- The complement of the sublevel set of `D^x` at `t ≥ 0` is `{g : v_g < v_x - t}`. -/
theorem coe_compl_sublevel_dx (ht : 0 ≤ t) :
    (((univ \ Integral.sublevel (dx v x) t : Finset (Fin m))) : Set (Fin m)) =
      {g | v g < v x - t} := by
  ext g
  simp only [coe_sdiff, coe_univ, Set.mem_sdiff, Set.mem_univ, true_and, mem_coe,
    Integral.mem_sublevel, dx, Set.mem_setOf_eq, max_le_iff, not_and_or, not_le]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    left
    linarith

open Classical in
/-- **Entry times**: for a nonloop `x`, `0 ≤ t_x`, and `x ∈ PO_t ⟺ t_x ≤ t` for `t ≥ 0`. -/
theorem entry_spec (hx : x ∉ M.closure ∅) :
    0 ≤ entry M v x ∧ ∀ t, 0 ≤ t → (x ∈ PO M v t ↔ entry M v x ≤ t) := by
  obtain ⟨j, hj, heq, hiff⟩ := gapSum_antitone (D := dx v x) (dx_nonneg v x)
    (φ := fun S => x ∈ M.closure ((univ \ S : Finset (Fin m)) : Set (Fin m)))
    (fun S S' h hS' => M.closure_subset_closure (coe_subset.2 (sdiff_subset_sdiff
      (Finset.Subset.refl _) h)) hS')
    (by simpa using hx)
  have he : entry M v x = sortedVal (dx v x) j := heq
  refine ⟨?_, fun t ht => ?_⟩
  · rw [he, ← sortedVal_zero (dx v x)]
    exact sortedVal_mono (dx_nonneg v x) (Nat.zero_le j) hj
  · have h := hiff t ht
    rw [coe_compl_sublevel_dx ht] at h
    rw [mem_PO, he, h, not_lt]

/-- A loop lies in no `PO_t`. -/
theorem notMem_PO_of_loop (hx : x ∈ M.closure ∅) : x ∉ PO M v t := fun h =>
  h (M.closure_subset_closure (Set.empty_subset _) hx)

theorem entry_nonneg (hx : x ∉ M.closure ∅) : 0 ≤ entry M v x := (entry_spec hx).1

theorem mem_PO_iff (hx : x ∉ M.closure ∅) (ht : 0 ≤ t) : x ∈ PO M v t ↔ entry M v x ≤ t :=
  (entry_spec hx).2 t ht

end Entry

/-! ### Merge times: Floyd–Warshall over `(min, max)` -/

section FW

variable (K : Fin m → Fin m → Prop)

open Classical in
/-- One round of the Floyd–Warshall algorithm over `(min, max)` with pivot `c`, on the entries
`(a, b)` with `K a c` and `K c b`. -/
noncomputable def fwStep (c : Fin m) (T : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun a b => if K a c ∧ K c b then min (T a b) (max (T a c) (T c b)) else T a b

/-- The Floyd–Warshall algorithm over `(min, max)`: one round for each pivot `0, …, m - 1`. -/
noncomputable def fwV (W : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  (List.finRange m).foldl (fun T c => fwStep K c T) W

open Classical in
/-- The bits `[K a b ∧ T_ab ≤ t]` of a matrix at `t`. -/
noncomputable def thr (t : ℝ) (T : Fin m → Fin m → ℝ) : Fin m → Fin m → Bool :=
  fun a b => decide (K a b ∧ T a b ≤ t)

variable {K}

/-- **A round commutes with thresholds**: for transitive `K`, the bits of `fwStep c T` at `t`
are one round of Warshall's algorithm on the bits of `T`. -/
theorem thr_fwStep (hK : ∀ a b c, K a b → K b c → K a c) (t : ℝ) (c : Fin m)
    (T : Fin m → Fin m → ℝ) : thr K t (fwStep K c T) = warshallStep c (thr K t T) := by
  classical
  funext a b
  rw [Bool.eq_iff_iff]
  simp only [thr, fwStep, warshallStep, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h : K a c ∧ K c b
  · rw [if_pos h, min_le_iff, max_le_iff]
    have hab : K a b := hK a c b h.1 h.2
    tauto
  · rw [if_neg h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨h₁, h₂⟩)
      · exact h'
      · exact absurd ⟨h₁.1, h₂.1⟩ h

theorem thr_foldl (hK : ∀ a b c, K a b → K b c → K a c) (t : ℝ) :
    ∀ (l : List (Fin m)) (T : Fin m → Fin m → ℝ),
      thr K t (l.foldl (fun T c => fwStep K c T) T) =
        l.foldl (fun R c => warshallStep c R) (thr K t T)
  | [], _ => rfl
  | c :: l, T => by
    simp only [List.foldl_cons]
    rw [thr_foldl hK t l, thr_fwStep hK]

/-- **The algorithm commutes with thresholds**: the bits of `fwV K W` at `t` are Warshall's
algorithm on the bits of `W`. -/
theorem thr_fwV (hK : ∀ a b c, K a b → K b c → K a c) (t : ℝ) (W : Fin m → Fin m → ℝ) :
    thr K t (fwV K W) = warshallV (thr K t W) :=
  thr_foldl hK t _ W

/-- **Bottlenecks**: for `K a b`, `fwV K W a b ≤ t` iff a chain of entries `K` with `W ≤ t`
leads from `a` to `b`. -/
theorem fwV_le_iff (hK : ∀ a b c, K a b → K b c → K a c) (W : Fin m → Fin m → ℝ) {a b : Fin m}
    (hab : K a b) {t : ℝ} :
    fwV K W a b ≤ t ↔ Relation.TransGen (fun a b => K a b ∧ W a b ≤ t) a b := by
  classical
  have h := congrFun (congrFun (thr_fwV hK t W) a) b
  have hR : (fun a b => thr K t W a b = true) = fun a b => K a b ∧ W a b ≤ t := by
    funext a b
    simp [thr]
  rw [← hR, ← warshallV_eq_true_iff, ← h]
  simp [thr, hab]

theorem foldl_fwStep_congr (hK : ∀ a b c, K a b → K b c → K a c) :
    ∀ (l : List (Fin m)) {T T' : Fin m → Fin m → ℝ}, (∀ a b, K a b → T a b = T' a b) →
      ∀ a b, K a b → l.foldl (fun T c => fwStep K c T) T a b =
        l.foldl (fun T c => fwStep K c T) T' a b
  | [], _, _, h => h
  | c :: l, T, T', h => by
    simp only [List.foldl_cons]
    refine foldl_fwStep_congr hK l fun a b hab => ?_
    classical
    simp only [fwStep]
    split_ifs with hc
    · rw [h a b hab, h a c hc.1, h c b hc.2]
    · exact h a b hab

/-- The algorithm reads only the entries `K`: two matrices that agree there give the same values
there. -/
theorem fwV_congr (hK : ∀ a b c, K a b → K b c → K a c) {W W' : Fin m → Fin m → ℝ}
    (h : ∀ a b, K a b → W a b = W' a b) {a b : Fin m} (hab : K a b) :
    fwV K W a b = fwV K W' a b :=
  foldl_fwStep_congr hK _ h a b hab

theorem foldl_fwStep_of_not (hK : ∀ a b c, K a b → K b c → K a c) {a b : Fin m} (hab : ¬K a b) :
    ∀ (l : List (Fin m)) (T : Fin m → Fin m → ℝ), l.foldl (fun T c => fwStep K c T) T a b = T a b
  | [], _ => rfl
  | c :: l, T => by
    classical
    simp only [List.foldl_cons]
    rw [foldl_fwStep_of_not hK hab l, fwStep, if_neg fun hc => hab (hK a c b hc.1 hc.2)]

/-- The entries outside `K` are not changed. -/
theorem fwV_of_not (hK : ∀ a b c, K a b → K b c → K a c) (W : Fin m → Fin m → ℝ) {a b : Fin m}
    (hab : ¬K a b) : fwV K W a b = W a b :=
  foldl_fwStep_of_not hK hab _ W

end FW

/-! ### Merge times of the clusters -/

section Merge

variable {M : Matroid (Fin m)} {v : Fin m → ℝ} {t : ℝ} {a b c x y z : Fin m}

/-- `Kr M a b`: `a` and `b` are nonloops of one component. -/
def Kr (M : Matroid (Fin m)) (a b : Fin m) : Prop :=
  connRel M a b ∧ a ∉ M.closure ∅ ∧ b ∉ M.closure ∅

theorem Kr.symm (h : Kr M a b) : Kr M b a := ⟨Conn.connRel_symm h.1, h.2.2, h.2.1⟩

theorem Kr.trans (h₁ : Kr M a b) (h₂ : Kr M b c) : Kr M a c :=
  ⟨Conn.connRel_trans h₁.1 h₂.1, h₁.2.1, h₂.2.2⟩

theorem kr_trans : ∀ a b c, Kr M a b → Kr M b c → Kr M a c := fun _ _ _ h₁ h₂ => h₁.trans h₂

theorem Kr.refl (h : a ∉ M.closure ∅) : Kr M a a := ⟨Conn.connRel_refl M a, h, h⟩

/-- Two distinct elements of one component are nonloops. -/
theorem kr_of_connRel (h : connRel M a b) (hne : a ≠ b) : Kr M a b := by
  obtain rfl | ⟨C, hC, ha, hb⟩ := h
  · exact absurd rfl hne
  exact ⟨Or.inr ⟨C, hC, ha, hb⟩, notMem_closure_empty hC ha hb hne,
    notMem_closure_empty hC hb ha (Ne.symm hne)⟩

/-- The weights: `W_aa = t_a` and `W_ab = max(t_a, t_b, |v_a - v_b|)`. -/
noncomputable def wgt (M : Matroid (Fin m)) (v : Fin m → ℝ) (a b : Fin m) : ℝ :=
  if a = b then entry M v a else max (max (entry M v a) (entry M v b)) |v a - v b|

/-- **The merge times** `T`: the Floyd–Warshall algorithm over `(min, max)` on `W`, within the
components. -/
noncomputable def bott (M : Matroid (Fin m)) (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fwV (Kr M) (wgt M v)

theorem wgt_comm (a b : Fin m) : wgt M v a b = wgt M v b a := by
  unfold wgt
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm (entry M v a), abs_sub_comm]

theorem entry_le_wgt (a b : Fin m) : entry M v a ≤ wgt M v a b := by
  unfold wgt
  split_ifs
  · exact le_rfl
  · exact (le_max_left _ _).trans (le_max_left _ _)

/-- **The links at scale `t`** are the entries `K` with `W ≤ t`. -/
theorem link_iff (ht : 0 ≤ t) :
    Link M (PO M v t) (near v t) a b ↔ Kr M a b ∧ wgt M v a b ≤ t := by
  constructor
  · rintro ⟨ha, hb, hab, hn⟩
    have ha' : a ∉ M.closure ∅ := fun h => notMem_PO_of_loop h ha
    have hb' : b ∉ M.closure ∅ := fun h => notMem_PO_of_loop h hb
    rw [mem_PO_iff ha' ht] at ha
    rw [mem_PO_iff hb' ht] at hb
    refine ⟨⟨hab, ha', hb'⟩, ?_⟩
    unfold wgt
    split_ifs
    · exact ha
    · exact max_le (max_le ha hb) hn
  · rintro ⟨⟨hab, ha', hb'⟩, hw⟩
    unfold wgt at hw
    split_ifs at hw with h
    · subst h
      exact ⟨(mem_PO_iff ha' ht).2 hw, (mem_PO_iff ha' ht).2 hw, hab, near_of_eq ht rfl⟩
    · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (max_le_iff.1 hw).imp_left max_le_iff.1
      exact ⟨(mem_PO_iff ha' ht).2 h₁, (mem_PO_iff hb' ht).2 h₂, hab, h₃⟩

theorem bott_le_iff (hxy : Kr M x y) :
    bott M v x y ≤ t ↔ Relation.TransGen (fun a b => Kr M a b ∧ wgt M v a b ≤ t) x y :=
  fwV_le_iff kr_trans _ hxy

/-- **Clusters from merge times**: at `t ≥ 0`, `x` and `y` lie in one cluster iff `Kr M x y` and
`T_xy ≤ t`. -/
theorem sameCluster_iff (ht : 0 ≤ t) :
    SameCluster M (PO M v t) (near v t) x y ↔ Kr M x y ∧ bott M v x y ≤ t := by
  have hR : Link M (PO M v t) (near v t) = fun a b => Kr M a b ∧ wgt M v a b ≤ t := by
    funext a b
    exact propext (link_iff ht)
  rw [sameCluster_iff_transGen ht, hR]
  constructor
  · intro h
    have hK : Kr M x y := by
      induction h with
      | single hab => exact hab.1
      | tail _ hbc ih => exact ih.trans hbc.1
    exact ⟨hK, (bott_le_iff hK).2 h⟩
  · rintro ⟨hK, h⟩
    exact (bott_le_iff hK).1 h

theorem transGen_symm {r : Fin m → Fin m → Prop} (hr : ∀ a b, r a b → r b a) {a b : Fin m}
    (h : Relation.TransGen r a b) : Relation.TransGen r b a := by
  induction h with
  | single h => exact .single (hr _ _ h)
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

theorem bott_comm (hxy : Kr M x y) : bott M v x y = bott M v y x := by
  have hs : ∀ t a b, (Kr M a b ∧ wgt M v a b ≤ t) → (Kr M b a ∧ wgt M v b a ≤ t) :=
    fun t a b h => ⟨h.1.symm, wgt_comm (M := M) (v := v) a b ▸ h.2⟩
  exact le_antisymm
    ((bott_le_iff hxy).2 (transGen_symm (hs _) ((bott_le_iff hxy.symm).1 le_rfl)))
    ((bott_le_iff hxy.symm).2 (transGen_symm (hs _) ((bott_le_iff hxy).1 le_rfl)))

/-- **The ultrametric inequality** `T_ac ≤ max(T_ab, T_bc)`. -/
theorem bott_le_max (hab : Kr M a b) (hbc : Kr M b c) :
    bott M v a c ≤ max (bott M v a b) (bott M v b c) :=
  (bott_le_iff (hab.trans hbc)).2
    (((bott_le_iff hab).1 (le_max_left _ _)).trans ((bott_le_iff hbc).1 (le_max_right _ _)))

theorem entry_le_bott (hxy : Kr M x y) : entry M v x ≤ bott M v x y := by
  obtain ⟨z, hz, -⟩ := Relation.TransGen.head'_iff.1 ((bott_le_iff (v := v) hxy).1 le_rfl)
  exact (entry_le_wgt x z).trans hz.2

theorem entry_le_bott_right (hxy : Kr M x y) : entry M v y ≤ bott M v x y :=
  (bott_comm hxy) ▸ entry_le_bott hxy.symm

theorem bott_self (hx : x ∉ M.closure ∅) : bott M v x x = entry M v x :=
  le_antisymm ((bott_le_iff (Kr.refl hx)).2 (.single ⟨Kr.refl hx, by simp [wgt]⟩))
    (entry_le_bott (Kr.refl hx))

theorem bott_le_wgt (hxy : Kr M x y) : bott M v x y ≤ wgt M v x y :=
  (bott_le_iff hxy).2 (.single ⟨hxy, le_rfl⟩)

end Merge

/-! ### The levels and the covering lemma -/

section Levels

variable {M : Matroid (Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y z : Fin m}

/-- The minimum of a list of reals, `0` for the empty list. -/
noncomputable def listMin : List ℝ → ℝ
  | [] => 0
  | a :: l => l.foldl min a

theorem foldl_min_spec : ∀ (l : List ℝ) (a : ℝ),
    l.foldl min a ∈ a :: l ∧ ∀ b ∈ a :: l, l.foldl min a ≤ b
  | [], a => by simp
  | c :: l, a => by
    obtain ⟨h₁, h₂⟩ := foldl_min_spec l (min a c)
    simp only [List.foldl_cons]
    refine ⟨?_, fun b hb => ?_⟩
    · rcases List.mem_cons.1 h₁ with h | h
      · rw [h]
        rcases min_choice a c with h' | h' <;> rw [h'] <;> simp
      · simp [h]
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact (h₂ _ List.mem_cons_self).trans (min_le_left _ _)
      rcases List.mem_cons.1 hb with rfl | hb
      · exact (h₂ _ List.mem_cons_self).trans (min_le_right _ _)
      · exact h₂ b (List.mem_cons_of_mem _ hb)

/-- A member of a list below all its members is the minimum. -/
theorem listMin_eq {l : List ℝ} {h : ℝ} (hmem : h ∈ l) (hle : ∀ a ∈ l, h ≤ a) :
    listMin l = h := by
  cases l with
  | nil => simp at hmem
  | cons a l =>
    obtain ⟨h₁, h₂⟩ := foldl_min_spec l a
    exact le_antisymm (h₂ h hmem) (hle _ h₁)

open Classical in
/-- The elements `y < x` with `Kr M x y`, in increasing order. -/
noncomputable def lower (M : Matroid (Fin m)) (x : Fin m) : List (Fin m) :=
  (List.finRange m).filter fun y => decide (y < x ∧ Kr M x y)

theorem mem_lower : y ∈ lower M x ↔ y < x ∧ Kr M x y := by
  simp [lower]

/-- `ρ_x = min_{y < x, Kr M x y} T_xy`, and `0` if there is no such `y`. -/
noncomputable def rho (M : Matroid (Fin m)) (v : Fin m → ℝ) (x : Fin m) : ℝ :=
  listMin ((lower M x).map (bott M v x))

open Classical in
/-- The entry times, `0` at a loop. -/
noncomputable def tz (M : Matroid (Fin m)) (v : Fin m → ℝ) (x : Fin m) : ℝ :=
  if x ∈ M.closure ∅ then 0 else entry M v x

/-- **The levels** `t_0, …, t_{m-1}, ρ_0, …, ρ_{m-1}`. -/
noncomputable def lev (M : Matroid (Fin m)) (v : Fin m → ℝ) : Fin (m + m) → ℝ :=
  Fin.append (tz M v) (rho M v)

/-- `q` is `0` or one of the levels `Λ`. -/
def InLev {L : ℕ} (Λ : Fin L → ℝ) (q : ℝ) : Prop :=
  q = 0 ∨ ∃ i, Λ i = q

theorem entry_inLev (hx : x ∉ M.closure ∅) : InLev (lev M v) (entry M v x) :=
  Or.inr ⟨Fin.castAdd m x, by simp [lev, tz, hx]⟩

theorem tz_inLev (x : Fin m) : InLev (lev M v) (tz M v x) :=
  Or.inr ⟨Fin.castAdd m x, by simp [lev]⟩

theorem rho_inLev (x : Fin m) : InLev (lev M v) (rho M v x) :=
  Or.inr ⟨Fin.natAdd m x, Fin.append_right _ _ x⟩

/-- **The covering lemma**: every merge time `T_xy` is a level, or `0`.  With `h = T_xy`, either
an element of the cluster `C` of `x` at `h` enters at `h`, or the relation `T < h` splits `C`
into classes, `x` and `y` in different ones; the least element `z` of a class avoiding the least
element of `C` has `ρ_z = h`. -/
theorem bott_inLev (hxy : Kr M x y) : InLev (lev M v) (bott M v x y) := by
  classical
  set h := bott M v x y with hh
  set C := univ.filter fun z => Kr M x z ∧ bott M v x z ≤ h with hC
  have memC : ∀ {z}, z ∈ C ↔ Kr M x z ∧ bott M v x z ≤ h := by simp [hC]
  by_cases hA : ∃ z ∈ C, entry M v z = h
  · obtain ⟨z, hz, hez⟩ := hA
    rw [← hez]
    exact entry_inLev (memC.1 hz).1.2.2
  push Not at hA
  have hlt : ∀ z ∈ C, entry M v z < h := fun z hz =>
    lt_of_le_of_ne ((entry_le_bott_right (memC.1 hz).1).trans (memC.1 hz).2) (hA z hz)
  have hxC : x ∈ C :=
    memC.2 ⟨Kr.refl hxy.2.1, by rw [bott_self hxy.2.1]; exact entry_le_bott hxy⟩
  have hyC : y ∈ C := memC.2 ⟨hxy, le_rfl⟩
  have hCne : C.Nonempty := ⟨x, hxC⟩
  set z₀ := C.min' hCne with hz₀
  have hz₀C : z₀ ∈ C := min'_mem C hCne
  -- one of `x`, `y` lies outside the class of `z₀`
  obtain ⟨w, hwC, hw⟩ : ∃ w ∈ C, h ≤ bott M v z₀ w := by
    by_contra hcon
    push Not at hcon
    have hb' : bott M v x y ≤ max (bott M v x z₀) (bott M v z₀ y) :=
      bott_le_max (memC.1 hz₀C).1 ((memC.1 hz₀C).1.symm.trans hxy)
    rw [bott_comm (memC.1 hz₀C).1] at hb'
    exact lt_irrefl h (hb'.trans_lt (max_lt (hcon x hxC) (hcon y hyC)))
  set P := C.filter fun z => bott M v w z < h with hP
  have memP : ∀ {z}, z ∈ P ↔ z ∈ C ∧ bott M v w z < h := by simp [hP]
  have hwP : w ∈ P := memP.2 ⟨hwC, by rw [bott_self (memC.1 hwC).1.2.2]; exact hlt w hwC⟩
  set z := P.min' ⟨w, hwP⟩ with hz
  have hzP : z ∈ P := min'_mem P _
  have hzC : z ∈ C := (memP.1 hzP).1
  have hKxz : Kr M x z := (memC.1 hzC).1
  have hKwz : Kr M w z := (memC.1 hwC).1.symm.trans hKxz
  have hz₀P : z₀ ∉ P := fun hP' => by
    have := (memP.1 hP').2
    rw [← bott_comm ((memC.1 hz₀C).1.symm.trans (memC.1 hwC).1)] at this
    exact absurd hw (not_le.2 this)
  have hz₀z : z₀ < z := lt_of_le_of_ne (min'_le C z hzC) (fun he => hz₀P (he ▸ hzP))
  have hKzz₀ : Kr M z z₀ := hKxz.symm.trans (memC.1 hz₀C).1
  -- every `y' < z` of the component has `T_zy' ≥ h`
  have hge : ∀ y' ∈ lower M z, h ≤ bott M v z y' := by
    intro y' hy'
    obtain ⟨hyz, hKzy⟩ := mem_lower.1 hy'
    by_contra hcon
    push Not at hcon
    have hy'C : y' ∈ C := memC.2 ⟨hKxz.trans hKzy, (bott_le_max hKxz hKzy).trans
      (max_le (memC.1 hzC).2 hcon.le)⟩
    have hy'P : y' ∈ P := memP.2 ⟨hy'C, (bott_le_max hKwz hKzy).trans_lt
      (max_lt (memP.1 hzP).2 hcon)⟩
    exact absurd (min'_le P y' hy'P) (not_le.2 hyz)
  refine Or.inr ⟨Fin.natAdd m z, ?_⟩
  rw [lev, Fin.append_right]
  refine listMin_eq (List.mem_map.2 ⟨z₀, mem_lower.2 ⟨hz₀z, hKzz₀⟩, ?_⟩) ?_
  · refine le_antisymm ?_ (hge z₀ (mem_lower.2 ⟨hz₀z, hKzz₀⟩))
    have := bott_le_max (v := v) hKxz.symm (memC.1 hz₀C).1
    rw [← bott_comm hKxz] at this
    exact this.trans (max_le (memC.1 hzC).2 (memC.1 hz₀C).2)
  · intro a ha
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 ha
    exact hge y' hy'

/-- `U_xy = max(t_x, t_y, min(T_xy, v_y - v_x))`. -/
noncomputable def uval (M : Matroid (Fin m)) (v : Fin m → ℝ) (x y : Fin m) : ℝ :=
  max (max (entry M v x) (entry M v y)) (min (bott M v x y) (v y - v x))

/-- **`U_xy` is a level**, or `0`. -/
theorem uval_inLev (hxy : Kr M x y) : InLev (lev M v) (uval M v x y) := by
  by_cases h₁ : min (bott M v x y) (v y - v x) ≤ max (entry M v x) (entry M v y)
  · rw [uval, max_eq_left h₁]
    rcases le_total (entry M v x) (entry M v y) with h | h
    · rw [max_eq_right h]; exact entry_inLev hxy.2.2
    · rw [max_eq_left h]; exact entry_inLev hxy.2.1
  · push Not at h₁
    rw [uval, max_eq_right h₁.le]
    by_cases h₂ : bott M v x y ≤ v y - v x
    · rw [min_eq_left h₂]; exact bott_inLev hxy
    · exfalso
      push Not at h₂
      rw [min_eq_right h₂.le] at h₁
      have ha : 0 ≤ max (entry M v x) (entry M v y) := le_max_of_le_left (entry_nonneg hxy.2.1)
      have hne : x ≠ y := by
        rintro rfl
        rw [sub_self] at h₁
        linarith
      have hw := bott_le_wgt (v := v) hxy
      rw [wgt, if_neg hne, abs_sub_comm, abs_of_pos (by linarith), max_eq_right h₁.le] at hw
      linarith

/-- **The order bit**: for `Kr M x y` and `t ≥ 0`,
`x ∈ PO_t ∧ (y ∉ PO_t ∨ (x, y in different clusters ∧ v_y - v_x > t))` iff `t_x ≤ t < U_xy`. -/
theorem ord_iff (ht : 0 ≤ t) (hxy : Kr M x y) :
    (x ∈ PO M v t ∧ (y ∉ PO M v t ∨
        (¬SameCluster M (PO M v t) (near v t) x y ∧ ¬(v y - v x ≤ t)))) ↔
      entry M v x ≤ t ∧ ¬uval M v x y ≤ t := by
  rw [mem_PO_iff hxy.2.1 ht, mem_PO_iff hxy.2.2 ht, sameCluster_iff ht, uval]
  simp only [not_le, not_and, hxy, true_implies, lt_max_iff, lt_min_iff]
  constructor
  · rintro ⟨hx, hy | ⟨hc, hd⟩⟩
    · exact ⟨hx, Or.inl (Or.inr hy)⟩
    · exact ⟨hx, Or.inr ⟨hc, hd⟩⟩
  · rintro ⟨hx, (h | h) | h⟩
    · exact absurd hx (not_le.2 h)
    · exact ⟨hx, Or.inl h⟩
    · exact ⟨hx, Or.inr h⟩

theorem tz_nonneg (x : Fin m) : 0 ≤ tz M v x := by
  unfold tz
  split_ifs with h
  · exact le_rfl
  · exact entry_nonneg h

theorem rho_nonneg (x : Fin m) : 0 ≤ rho M v x := by
  unfold rho
  cases hl : lower M x with
  | nil => simp [listMin]
  | cons y l =>
    have hmem := (foldl_min_spec (l.map (bott M v x)) (bott M v x y)).1
    simp only [List.map_cons, listMin]
    rw [← List.map_cons] at hmem
    obtain ⟨y', hy', he⟩ := List.mem_map.1 hmem
    rw [← he]
    have hK : Kr M x y' := (mem_lower.1 (hl ▸ hy')).2
    exact (entry_nonneg hK.2.1).trans (entry_le_bott hK)

/-- The levels are nonnegative. -/
theorem lev_nonneg (i : Fin (m + m)) : 0 ≤ lev M v i := by
  refine Fin.addCases (fun x => ?_) (fun x => ?_) i
  · rw [lev, Fin.append_left]; exact tz_nonneg x
  · rw [lev, Fin.append_right]; exact rho_nonneg x

/-- A value `InLev` is one of the sorted values `s_0 = 0, s_1, …` of the levels. -/
theorem InLev.exists_sortedVal {L : ℕ} {Λ : Fin L → ℝ} {q : ℝ} (h : InLev Λ q) :
    ∃ i ≤ L, sortedVal Λ i = q := by
  rcases h with rfl | ⟨i, rfl⟩
  · exact ⟨0, Nat.zero_le _, sortedVal_zero Λ⟩
  · obtain ⟨j, -, hj, hje⟩ := exists_sortedVal_eq Λ i
    exact ⟨j, hj, hje⟩

end Levels

/-! ### The event bits -/

section Bits

variable {M : Matroid (Fin m)} {v : Fin m → ℝ} {t : ℝ} {x y : Fin m}

/-- The number of event bits: `m` entry bits, `m²` merge bits and `m²` order bits. -/
def qn (m : ℕ) : ℕ := m + (m * m + m * m)

/-- The index of the entry bit of `x`. -/
def qT (x : Fin m) : Fin (qn m) := Fin.castAdd (m * m + m * m) x

/-- The index of the merge bit of `(x, y)`. -/
def qB (x y : Fin m) : Fin (qn m) := Fin.natAdd m (Fin.castAdd (m * m) (finProdFinEquiv (x, y)))

/-- The index of the order bit of `(x, y)`. -/
def qU (x y : Fin m) : Fin (qn m) := Fin.natAdd m (Fin.natAdd (m * m) (finProdFinEquiv (x, y)))

open Classical in
/-- The merge value of a pair: `T_xy` for `Kr M x y`, and `0` otherwise. -/
noncomputable def bq (M : Matroid (Fin m)) (v : Fin m → ℝ) (x y : Fin m) : ℝ :=
  if Kr M x y then bott M v x y else 0

open Classical in
/-- The order value of a pair: `U_xy` for `Kr M x y`, and `0` otherwise. -/
noncomputable def uq (M : Matroid (Fin m)) (v : Fin m → ℝ) (x y : Fin m) : ℝ :=
  if Kr M x y then uval M v x y else 0

/-- **The query values**: the entry times, the merge values and the order values. -/
noncomputable def Qv (M : Matroid (Fin m)) (v : Fin m → ℝ) : Fin (qn m) → ℝ :=
  Fin.append (tz M v) (Fin.append (fun i => bq M v (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2) fun i => uq M v (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm i).2)

@[simp] theorem Qv_qT (x : Fin m) : Qv M v (qT x) = tz M v x := by
  simp [Qv, qT]

@[simp] theorem Qv_qB (x y : Fin m) : Qv M v (qB x y) = bq M v x y := by
  rw [Qv, qB, Fin.append_right, Fin.append_left, Equiv.symm_apply_apply]

@[simp] theorem Qv_qU (x y : Fin m) : Qv M v (qU x y) = uq M v x y := by
  rw [Qv, qU, Fin.append_right, Fin.append_right, Equiv.symm_apply_apply]

/-- **Every query value is a level**, or `0`. -/
theorem Qv_inLev (j : Fin (qn m)) : InLev (lev M v) (Qv M v j) := by
  classical
  refine Fin.addCases (fun x => ?_) (fun i => ?_) j
  · rw [show (Fin.castAdd (m * m + m * m) x : Fin (qn m)) = qT x from rfl, Qv_qT]
    exact tz_inLev x
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · obtain ⟨⟨x, y⟩, rfl⟩ := finProdFinEquiv.surjective i
      rw [show Fin.natAdd m (Fin.castAdd (m * m) (finProdFinEquiv (x, y))) = qB x y from rfl,
        Qv_qB, bq]
      split_ifs with h
      · exact bott_inLev h
      · exact Or.inl rfl
    · obtain ⟨⟨x, y⟩, rfl⟩ := finProdFinEquiv.surjective i
      rw [show Fin.natAdd m (Fin.natAdd (m * m) (finProdFinEquiv (x, y))) = qU x y from rfl,
        Qv_qU, uq]
      split_ifs with h
      · exact uval_inLev h
      · exact Or.inl rfl

end Bits

end SignedTropical.Rainbow.Events
