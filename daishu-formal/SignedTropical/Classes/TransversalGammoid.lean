import SignedTropical.Classes.Transversal
import SignedTropical.Classes.Dual

/-!
# Gammoids

`greedy_intersection.tex`, Corollary `cor:transversal`(2): gammoids, with explicit Boolean rank
circuits and signed tropical circuits, through the theorem of Ingleton and Piff and the transversal
matroids of `Classes/Transversal.lean`.

A digraph on the vertices `Fin v` is a set `arcs` of pairs `(u, w)`, the arcs `u → w`; `S` is a
set of vertices, the sources.

1. **Linkage** (`IsLinked arcs S X`): pairwise vertex-disjoint directed paths, one from a vertex
   of `S` to each `x ∈ X`.  `IsLinked.exists_avoid`: the paths can be shortened so that they meet
   `S` only at their first vertices.
2. **The theorem of Ingleton and Piff** (`dual_indep_iff_isLinked`): `X` is linked from `S` iff
   it is independent in the dual of the transversal matroid of the family `ipFamily arcs S`,
   `A_w = {w} ∪ {u : u → w}` for `w ∉ S` and `A_w = ∅` for `w ∈ S`.  The bases of that
   transversal matroid are the partial transversals with `|V \ S|` elements (`card_of_isBase`,
   `isBase_of_card`).  If such a base misses `X`, the inverse `g` of its transversal map gives
   the paths `g^l(x) → ⋯ → g(x) → x` (`isLinked_of_isBase`); conversely the vertices of the paths
   other than their last ones and the vertices outside `S` on no path form such a base
   (`exists_isBase_of_isLinked`).
3. **The gammoid** (`gammoid arcs S ι`) on `Fin m`, the elements placed at distinct vertices by
   `ι : Fin m ↪ Fin v`: the dual matroid of item 2 pulled back along `ι`.  Its independent sets
   are the sets `X` with `ι(X)` linked from `S` (`gammoid_indep`), and its ground set is `univ`
   (`gammoid_ground`).
4. **Circuits** (`gammoidCircuit`, `gammoidCircuit_spec`): the rank circuit of the transversal
   matroid of item 2 (`rankCircuit`, with at most `v + a` incidences, `a = |arcs|`,
   `sum_card_ipFamily_le`), its dual (`dualRankCircuit` of `Classes/Dual.lean`), and the vertex
   bits read from the input (`vertexB`).  `gammoid_rankCircuit`: a Boolean rank circuit with at
   most `48 (v+1)(v+a+1)²(2v+a+1) ≤ 48 (v+1)⁷` gates; `theoremA_gammoid`: a signed tropical
   circuit for `h_M` with at most `160 (m+1)(v+1)(v+a+1)²(2v+a+1) ≤ 160 (v+1)⁸` gates.
-/

open Finset SignedTropical.BoolAlg SignedTropical.Rainbow.MI

namespace SignedTropical.Classes.Transversal

section Linkage

variable {v : ℕ} {arcs : Finset (Fin v × Fin v)} {S : Finset (Fin v)}

/-- `X` is **linked from `S`** in the digraph on the vertices `Fin v` with the arcs `arcs`:
there are pairwise vertex-disjoint directed paths, one for each `x ∈ X`, each from a vertex of
`S` to `x`.  The path of `x` is `path x 0 → path x 1 → ⋯ → path x (len x)`, and it may be the
single vertex `x ∈ S`; the second condition says that the paths are vertex-disjoint and that the
vertices of each path are distinct. -/
def IsLinked (arcs : Finset (Fin v × Fin v)) (S X : Finset (Fin v)) : Prop :=
  ∃ (len : Fin v → ℕ) (path : Fin v → ℕ → Fin v),
    (∀ x ∈ X, path x 0 ∈ S ∧ path x (len x) = x ∧
      ∀ i < len x, (path x i, path x (i + 1)) ∈ arcs) ∧
    ∀ x ∈ X, ∀ y ∈ X, ∀ i ≤ len x, ∀ j ≤ len y, path x i = path y j → x = y ∧ i = j

/-- A linkage can be shortened so that every path meets `S` only at its first vertex. -/
theorem IsLinked.exists_avoid {X : Finset (Fin v)} (h : IsLinked arcs S X) :
    ∃ (len : Fin v → ℕ) (path : Fin v → ℕ → Fin v),
      (∀ x ∈ X, path x 0 ∈ S ∧ path x (len x) = x ∧
        (∀ i < len x, (path x i, path x (i + 1)) ∈ arcs) ∧
        ∀ i, 0 < i → i ≤ len x → path x i ∉ S) ∧
      ∀ x ∈ X, ∀ y ∈ X, ∀ i ≤ len x, ∀ j ≤ len y, path x i = path y j → x = y ∧ i = j := by
  classical
  obtain ⟨len, path, hp, hd⟩ := h
  obtain ⟨t, htle, htS, htmax⟩ : ∃ t : Fin v → ℕ, (∀ x, t x ≤ len x) ∧
      (∀ x ∈ X, path x (t x) ∈ S) ∧ ∀ x i, t x < i → i ≤ len x → path x i ∉ S :=
    ⟨fun x => Nat.findGreatest (fun i => path x i ∈ S) (len x), fun x => Nat.findGreatest_le _,
      fun x hx => Nat.findGreatest_spec (P := fun i => path x i ∈ S) (Nat.zero_le _) (hp x hx).1,
      fun x i hi hil hS => absurd (Nat.le_findGreatest (P := fun i => path x i ∈ S) hil hS)
        (by beta_reduce at hi; omega)⟩
  refine ⟨fun x => len x - t x, fun x i => path x (t x + i), fun x hx => ?_,
    fun x hx y hy i hi j hj h => ?_⟩
  · have := htle x
    refine ⟨by simpa using htS x hx, by simpa [Nat.add_sub_cancel' (htle x)] using (hp x hx).2.1,
      fun i hi => ?_, fun i hi hil => ?_⟩
    · beta_reduce at hi
      simpa [Nat.add_assoc] using (hp x hx).2.2 (t x + i) (by omega)
    · beta_reduce at hil ⊢
      exact htmax x (t x + i) (by omega) (by omega)
  · have := htle x
    have := htle y
    beta_reduce at hi hj h ⊢
    obtain ⟨rfl, hij⟩ := hd x hx y hy (t x + i) (by omega) (t y + j) (by omega) h
    exact ⟨rfl, by omega⟩

/-- The family of Ingleton and Piff on the vertices: `A_w = {w} ∪ {u : u → w}` for `w ∉ S`, and
`A_w = ∅` for `w ∈ S`. -/
def ipFamily (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v)) (w : Fin v) :
    Finset (Fin v) :=
  if w ∈ S then ∅ else insert w ((arcs.filter fun q => q.2 = w).image Prod.fst)

/-- `u ∈ A_w` iff `w ∉ S`, and `u = w` or `u → w` is an arc. -/
theorem mem_ipFamily {w u : Fin v} :
    u ∈ ipFamily arcs S w ↔ w ∉ S ∧ (u = w ∨ (u, w) ∈ arcs) := by
  unfold ipFamily
  split_ifs with h
  · simp [h]
  · simp only [mem_insert, mem_image, mem_filter, h, not_false_eq_true, true_and]
    constructor
    · rintro (rfl | ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩)
      exacts [.inl rfl, .inr hab]
    · rintro (rfl | hu)
      exacts [.inl rfl, .inr ⟨(u, w), ⟨hu, rfl⟩, rfl⟩]

/-- For a family on the vertices, a set `B` of vertices is a partial transversal iff some map
`f`, injective on `B`, has `b ∈ A_{f b}` for every `b ∈ B`. -/
theorem isPartialTransversal_iff {F : Fin v → Finset (Fin v)} {B : Finset (Fin v)} :
    IsPartialTransversal F ↑B ↔ ∃ f : Fin v → Fin v, Set.InjOn f ↑B ∧ ∀ b ∈ B, b ∈ F (f b) := by
  classical
  constructor
  · rintro ⟨φ, hφ, hmem⟩
    refine ⟨fun b => if h : b ∈ B then φ ⟨b, h⟩ else b, fun b hb b' hb' h => ?_,
      fun b hb => ?_⟩
    · simp only [mem_coe] at hb hb'
      simp only [dif_pos hb, dif_pos hb'] at h
      exact congrArg Subtype.val (hφ h)
    · simpa [dif_pos hb] using hmem ⟨b, hb⟩
  · rintro ⟨f, hf, hmem⟩
    exact ⟨fun b => f b, fun b b' h => Subtype.ext (hf b.2 b'.2 h), fun b => hmem b b.2⟩

/-- A partial transversal of `ipFamily` has at most `|V \ S|` elements. -/
theorem card_le_of_isPartialTransversal {B : Finset (Fin v)}
    (hB : IsPartialTransversal (ipFamily arcs S) ↑B) : B.card ≤ (univ \ S).card := by
  obtain ⟨f, hf, hmem⟩ := isPartialTransversal_iff.1 hB
  rw [← card_image_of_injOn hf]
  refine card_le_card fun w hw => ?_
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
  exact mem_sdiff.2 ⟨mem_univ _, (mem_ipFamily.1 (hmem b hb)).1⟩

/-- `V \ S` is a partial transversal of `ipFamily`. -/
theorem isPartialTransversal_compl : IsPartialTransversal (ipFamily arcs S) ↑(univ \ S) :=
  isPartialTransversal_iff.2 ⟨id, Set.injOn_id _,
    fun _ hb => mem_ipFamily.2 ⟨(mem_sdiff.1 hb).2, .inl rfl⟩⟩

/-- A base of the transversal matroid of `ipFamily` has `|V \ S|` elements. -/
theorem card_of_isBase {B : Finset (Fin v)}
    (hB : (transversal (ipFamily arcs S)).IsBase ↑B) : B.card = (univ \ S).card := by
  refine le_antisymm (card_le_of_isPartialTransversal hB.indep) ?_
  rw [card_base _ hB, ← rk_univ _ transversal_ground]
  exact card_le_rk _ isPartialTransversal_compl (subset_univ _)

/-- A partial transversal of `ipFamily` with `|V \ S|` elements is a base. -/
theorem isBase_of_card {B : Finset (Fin v)} (hB : IsPartialTransversal (ipFamily arcs S) ↑B)
    (hc : (univ \ S).card ≤ B.card) : (transversal (ipFamily arcs S)).IsBase ↑B := by
  refine Matroid.Indep.isBase_of_forall_insert hB fun e he hind => ?_
  have heB : e ∉ B := fun h => he.2 (mem_coe.2 h)
  have := card_le_of_isPartialTransversal (arcs := arcs) (S := S) (B := insert e B)
    (by rwa [coe_insert])
  rw [card_insert_of_notMem heB] at this
  omega

/-- **Ingleton and Piff, from a base.**  If a base `B` of the transversal matroid of `ipFamily`
misses `X`, then `X` is linked from `S`: with `g` the inverse of a transversal map of `B` onto
`V \ S`, the path of `x ∈ X` is `g^l(x) → ⋯ → g(x) → x`, `l` the least index with
`g^l(x) ∈ S`. -/
theorem isLinked_of_isBase {X B : Finset (Fin v)} (hB : (transversal (ipFamily arcs S)).IsBase ↑B)
    (hXB : Disjoint X B) : IsLinked arcs S X := by
  classical
  obtain ⟨f, hf, hmem⟩ := isPartialTransversal_iff.1 hB.indep
  -- `f` maps `B` onto `V \ S`
  have himage : B.image f = univ \ S := by
    refine eq_of_subset_of_card_le (fun w hw => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
      exact mem_sdiff.2 ⟨mem_univ _, (mem_ipFamily.1 (hmem b hb)).1⟩
    · rw [card_image_of_injOn hf, card_of_isBase hB]
  have hg : ∀ w, ∃ b, w ∉ S → b ∈ B ∧ f b = w := fun w => by
    by_cases hw : w ∈ S
    · exact ⟨w, fun h => absurd hw h⟩
    · obtain ⟨b, hb, hbw⟩ := mem_image.1 (himage ▸ mem_sdiff.2 ⟨mem_univ w, hw⟩ : w ∈ B.image f)
      exact ⟨b, fun _ => ⟨hb, hbw⟩⟩
  choose g hg using hg
  have hgB : ∀ w, w ∉ S → g w ∈ B := fun w hw => (hg w hw).1
  have hgA : ∀ w, w ∉ S → g w = w ∨ (g w, w) ∈ arcs := fun w hw => by
    have := (mem_ipFamily.1 (hmem _ (hg w hw).1)).2
    rwa [(hg w hw).2] at this
  have hginj : ∀ w w', w ∉ S → w' ∉ S → g w = g w' → w = w' := fun w w' hw hw' h => by
    rw [← (hg w hw).2, ← (hg w' hw').2, h]
  have hXB' : ∀ x ∈ X, x ∉ B := fun x hx hxB => disjoint_left.1 hXB hx hxB
  -- cancellation along the orbits of `g` from `X`
  have key : ∀ i j (x y : Fin v), x ∈ X → y ∈ X → (∀ k < i, g^[k] x ∉ S) →
      (∀ k < j, g^[k] y ∉ S) → g^[i] x = g^[j] y → i = j ∧ x = y := by
    intro i
    induction i with
    | zero =>
      intro j x y hx hy _ hj h
      cases j with
      | zero => exact ⟨rfl, h⟩
      | succ j =>
        rw [Function.iterate_zero_apply, Function.iterate_succ_apply'] at h
        exact absurd (h ▸ hgB _ (hj j (Nat.lt_succ_self j))) (hXB' x hx)
    | succ i ih =>
      intro j x y hx hy hi hj h
      cases j with
      | zero =>
        rw [Function.iterate_succ_apply', Function.iterate_zero_apply] at h
        exact absurd (h ▸ hgB _ (hi i (Nat.lt_succ_self i))) (hXB' y hy)
      | succ j =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
        obtain ⟨rfl, rfl⟩ := ih j x y hx hy (fun k hk => hi k (Nat.lt_succ_of_lt hk))
          (fun k hk => hj k (Nat.lt_succ_of_lt hk))
          (hginj _ _ (hi i (Nat.lt_succ_self i)) (hj j (Nat.lt_succ_self j)) h)
        exact ⟨rfl, rfl⟩
  -- every orbit from `X` reaches `S`
  have hreach : ∀ x ∈ X, ∃ i, g^[i] x ∈ S := fun x hx => by
    by_contra hne
    push Not at hne
    exact not_injective_infinite_finite (fun i => g^[i] x)
      fun i j h => (key i j x x hx hx (fun k _ => hne k) (fun k _ => hne k) h).1
  obtain ⟨len, hlenS, hlenmin⟩ : ∃ len : Fin v → ℕ, (∀ x ∈ X, g^[len x] x ∈ S) ∧
      ∀ x k, k < len x → g^[k] x ∉ S :=
    ⟨fun x => sInf {i | g^[i] x ∈ S}, fun x hx => Nat.sInf_mem (hreach x hx),
      fun _ _ hk => Nat.notMem_of_lt_sInf hk⟩
  refine ⟨len, fun x k => g^[len x - k] x, fun x hx => ⟨?_, ?_, fun k hk => ?_⟩,
    fun x hx y hy i hi j hj h => ?_⟩
  · simpa using hlenS x hx
  · simp
  · beta_reduce
    have hk' : len x - k = len x - (k + 1) + 1 := by omega
    have hw := hlenmin x (len x - (k + 1)) (by omega)
    rw [hk', Function.iterate_succ_apply']
    refine (hgA _ hw).resolve_left fun hfix => ?_
    have := key (len x - (k + 1) + 1) (len x - (k + 1)) x x hx hx
      (fun k' hk'' => hlenmin x k' (by omega)) (fun k' hk'' => hlenmin x k' (by omega))
      (by rw [Function.iterate_succ_apply', hfix])
    omega
  · beta_reduce at hi hj h
    obtain ⟨h1, rfl⟩ := key _ _ x y hx hy (fun k hk => hlenmin x k (by omega))
      (fun k hk => hlenmin y k (by omega)) h
    exact ⟨rfl, by omega⟩

/-- **Ingleton and Piff, to a base.**  If `X` is linked from `S`, some base of the transversal
matroid of `ipFamily` misses `X`: the vertices of the paths other than their last ones, sent to
their successors, and the vertices outside `S` on no path, sent to themselves. -/
theorem exists_isBase_of_isLinked {X : Finset (Fin v)} (h : IsLinked arcs S X) :
    ∃ B : Finset (Fin v), (transversal (ipFamily arcs S)).IsBase ↑B ∧ Disjoint X B := by
  classical
  obtain ⟨len, path, hp, hd⟩ := h.exists_avoid
  -- `On u`: `u` is a vertex of a path other than its last one
  let On : Fin v → Prop := fun u => ∃ q : Fin v × ℕ, q.1 ∈ X ∧ q.2 < len q.1 ∧ path q.1 q.2 = u
  let B := univ.filter fun u => On u ∨ (u ∉ S ∧ ∀ x ∈ X, ∀ i ≤ len x, path x i ≠ u)
  let f : Fin v → Fin v := fun u => if hu : On u then path hu.choose.1 (hu.choose.2 + 1) else u
  -- on a path, `f` is the successor
  have hfOn : ∀ x ∈ X, ∀ i < len x, f (path x i) = path x (i + 1) := by
    intro x hx i hi
    have hu : On (path x i) := ⟨(x, i), hx, hi, rfl⟩
    simp only [f, dif_pos hu]
    obtain ⟨hq1, hq2, hq3⟩ := hu.choose_spec
    obtain ⟨h1, h2⟩ := hd _ hq1 x hx _ hq2.le i hi.le hq3
    rw [h1, h2]
  have hfOff : ∀ u, ¬On u → f u = u := fun u hu => by simp only [f, dif_neg hu]
  -- `b ∈ A_{f b}` on `B`
  have hmem : ∀ b ∈ B, b ∈ ipFamily arcs S (f b) := by
    intro b hb
    by_cases hu : On b
    · obtain ⟨⟨x, i⟩, hx, hi, rfl⟩ := hu
      rw [hfOn x hx i hi]
      exact mem_ipFamily.2
        ⟨(hp x hx).2.2.2 (i + 1) (Nat.succ_pos i) hi, .inr ((hp x hx).2.2.1 i hi)⟩
    · have hbS := ((mem_filter.1 hb).2.resolve_left hu).1
      rw [hfOff b hu]
      exact mem_ipFamily.2 ⟨hbS, .inl rfl⟩
  -- `f` is injective on `B`
  have hinj : Set.InjOn f ↑B := by
    intro b hb b' hb' hbb'
    have hb₁ := (mem_filter.1 (mem_coe.1 hb)).2
    have hb₁' := (mem_filter.1 (mem_coe.1 hb')).2
    by_cases hu : On b <;> by_cases hu' : On b'
    · obtain ⟨⟨x, i⟩, hx, hi, rfl⟩ := hu
      obtain ⟨⟨y, j⟩, hy, hj, rfl⟩ := hu'
      rw [hfOn x hx i hi, hfOn y hy j hj] at hbb'
      obtain ⟨rfl, hij⟩ := hd x hx y hy (i + 1) hi (j + 1) hj hbb'
      rw [Nat.succ_injective hij]
    · obtain ⟨⟨x, i⟩, hx, hi, rfl⟩ := hu
      rw [hfOn x hx i hi, hfOff b' hu'] at hbb'
      exact absurd hbb' ((hb₁'.resolve_left hu').2 x hx (i + 1) hi)
    · obtain ⟨⟨y, j⟩, hy, hj, rfl⟩ := hu'
      rw [hfOff b hu, hfOn y hy j hj] at hbb'
      exact absurd hbb'.symm ((hb₁.resolve_left hu).2 y hy (j + 1) hj)
    · rwa [hfOff b hu, hfOff b' hu'] at hbb'
  -- `f` maps `B` onto `V \ S`
  have hcover : univ \ S ⊆ B.image f := by
    intro w hw
    have hwS := (mem_sdiff.1 hw).2
    by_cases hon : ∃ x ∈ X, ∃ i ≤ len x, path x i = w
    · obtain ⟨x, hx, i, hi, rfl⟩ := hon
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 :=
        Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun h => hwS (h ▸ (hp x hx).1))
      exact mem_image.2 ⟨path x i, mem_filter.2 ⟨mem_univ _, .inl ⟨(x, i), hx, hi, rfl⟩⟩,
        hfOn x hx i hi⟩
    · push Not at hon
      have hu : ¬On w := fun ⟨q, hq, hql, hqw⟩ => hon q.1 hq q.2 hql.le hqw
      exact mem_image.2 ⟨w, mem_filter.2 ⟨mem_univ _, .inr ⟨hwS, hon⟩⟩, hfOff w hu⟩
  refine ⟨B, isBase_of_card (isPartialTransversal_iff.2 ⟨f, hinj, hmem⟩) ?_, ?_⟩
  · exact (card_le_card hcover).trans (card_image_le)
  · refine disjoint_left.2 fun x hx hxB => ?_
    rcases (mem_filter.1 hxB).2 with ⟨⟨y, i⟩, hy, hi, hyx⟩ | ⟨-, hoff⟩
    · have := hd y hy x hx i hi.le (len x) le_rfl (hyx.trans (hp x hx).2.1.symm)
      obtain ⟨rfl, rfl⟩ := this
      exact lt_irrefl _ hi
    · exact hoff x hx (len x) le_rfl (hp x hx).2.1

/-- **The theorem of Ingleton and Piff.**  A set of vertices is independent in the dual of the
transversal matroid of `ipFamily arcs S` if and only if it is linked from `S`. -/
theorem dual_indep_iff_isLinked {X : Finset (Fin v)} :
    (transversal (ipFamily arcs S))✶.Indep ↑X ↔ IsLinked arcs S X := by
  rw [Matroid.dual_indep_iff_exists']
  constructor
  · rintro ⟨-, B₀, hB₀, hdisj⟩
    obtain ⟨B, rfl⟩ := exists_finset B₀
    exact isLinked_of_isBase hB₀ (disjoint_coe.1 hdisj)
  · intro h
    obtain ⟨B, hB, hdisj⟩ := exists_isBase_of_isLinked h
    exact ⟨Set.subset_univ _, ↑B, hB, disjoint_coe.2 hdisj⟩

/-- The incidences of `ipFamily` number at most `v + |arcs|`. -/
theorem sum_card_ipFamily_le : ∑ w, (ipFamily arcs S w).card ≤ v + arcs.card := by
  calc ∑ w, (ipFamily arcs S w).card ≤ ∑ w, ((arcs.filter fun q => q.2 = w).card + 1) := by
        refine sum_le_sum fun w _ => ?_
        unfold ipFamily
        split_ifs
        · simp
        · exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)
    _ = v + arcs.card := by
        rw [sum_add_distrib, ← card_eq_sum_card_fiberwise fun q _ => mem_univ q.2]
        simp [add_comm]

end Linkage

/-! ### Gammoids and their circuits -/

section Gammoid

variable {v m : ℕ} {arcs : Finset (Fin v × Fin v)} {S : Finset (Fin v)} {ι : Fin m ↪ Fin v}

/-- **The gammoid** of the digraph with the arcs `arcs` on the vertices `Fin v` and the sources
`S`, on the elements `Fin m` placed at distinct vertices by `ι`: a set `X` of elements is
independent iff `ι(X)` is linked from `S` (`gammoid_indep`).  It is the dual of the transversal
matroid of `ipFamily arcs S` (Ingleton and Piff), pulled back along `ι`. -/
def gammoid (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v)) (ι : Fin m ↪ Fin v) :
    Matroid (Fin m) :=
  (transversal (ipFamily arcs S))✶.comap ι

@[simp] theorem gammoid_ground : (gammoid arcs S ι).E = Set.univ := rfl

/-- **The independent sets of the gammoid** are the sets `X` with `ι(X)` linked from `S`. -/
theorem gammoid_indep {X : Finset (Fin m)} :
    (gammoid arcs S ι).Indep ↑X ↔ IsLinked arcs S (X.map ι) := by
  rw [gammoid, Matroid.comap_indep_iff, ← dual_indep_iff_isLinked, coe_map,
    and_iff_left ι.injective.injOn]

/-- The vertex bits read by the gammoid circuit: vertex `u` reads the input bit of the element
at `u`, and the constant `false` if no element is at `u`. -/
noncomputable def vertexB (ι : Fin m ↪ Fin v) (s : Fin m → Arg m) (u : Fin v) : Arg m :=
  if h : ∃ e, ι e = u then s h.choose else .const

/-- The rank circuit of the strict gammoid on the vertices: the dual circuit (`dualRankCircuit`
of `Classes/Dual.lean`) of the rank circuit of the transversal matroid of `ipFamily arcs S`. -/
noncomputable def strictGammoidCircuit (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v)) :
    Circuit BoolOp v :=
  dualRankCircuit (rankCircuit (incCol (ipFamily arcs S)) (incBlk (ipFamily arcs S)))
    (rank (transversal (ipFamily arcs S)))

/-- **The rank circuit of the gammoid**: the circuit of the strict gammoid on the vertex bits. -/
noncomputable def gammoidCircuit (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v))
    (ι : Fin m ↪ Fin v) : Circuit BoolOp m :=
  circuitOf fun s => runB (strictGammoidCircuit arcs S) (vertexB ι s)

/-- **The rank circuit of the gammoid** has `v · roundCost p (oracleCost v p) + popCost p + v + 1
+ 11 (v+1)⌈log₂(v+1)⌉` gates, `p` the number of incidences of `ipFamily`, and outputs the rank
of `X` in binary for every set `X` of elements. -/
theorem gammoidCircuit_spec {p : ℕ} (hp : ∑ w, (ipFamily arcs S w).card = p) :
    (gammoidCircuit arcs S ι).size =
        v * roundCost p (oracleCost v p) + popCost p + v + 1 + 11 * (v + 1) * Nat.size v ∧
      ∀ X : Finset (Fin m), (bitsVal ((gammoidCircuit arcs S ι).eval boolInterp (indicator X)) :
        ℕ∞) = (gammoid arcs S ι).eRk ↑X := by
  subst hp
  have hT := presents_incidence (ipFamily arcs S)
  have h := (runB_num (n := m) (strictGammoidCircuit arcs S)).pre (R := vecR m) (g := vertexB ι)
    (G := fun x u => if h : ∃ e, ι e = u then x h.choose else false) fun gs s T hs u => by
      beta_reduce
      unfold vertexB
      split_ifs with hu
      · exact hs hu.choose
      · exact den_const gs
  obtain ⟨hs, -, he⟩ := circuitOf_num h
  refine ⟨?_, fun X => ?_⟩
  · rw [gammoidCircuit, hs, strictGammoidCircuit, dualRankCircuit_size, (rankCircuit_spec hT).1]
  · have hG : (fun u => if h : ∃ e, ι e = u then indicator X h.choose else false) =
        indicator (X.map ι) := by
      funext u
      by_cases hu : ∃ e, ι e = u
      · rw [dif_pos hu]
        simp only [indicator, mem_map]
        refine decide_eq_decide.2 ⟨fun h => ⟨_, h, hu.choose_spec⟩, ?_⟩
        rintro ⟨a, ha, hau⟩
        rwa [ι.injective (hau.trans hu.choose_spec.symm)] at ha
      · rw [dif_neg hu]
        simp only [indicator, mem_map]
        exact (decide_eq_false fun ⟨a, _, hau⟩ => hu ⟨a, hau⟩).symm
    rw [gammoidCircuit, he, hG, strictGammoidCircuit,
      dualRankCircuit_rank _ transversal_ground (rankCircuit_eRk hT), gammoid, Matroid.eRk_comap,
      coe_map]

/-- The gammoid circuit has at most `48 (v+1)(v+a+1)²(2v+a+1)` gates when `p ≤ v + a`. -/
theorem gammoidCost_le {p a : ℕ} (hp : p ≤ v + a) :
    v * roundCost p (oracleCost v p) + popCost p + v + 1 + 11 * (v + 1) * Nat.size v ≤
      48 * (v + 1) * (v + a + 1) ^ 2 * (2 * v + a + 1) := by
  have h1 := rankCost_le v v p
  have h2 : 36 * (v + 1) * (p + 1) ^ 2 * (p + v + 1) ≤
      36 * (v + 1) * (v + a + 1) ^ 2 * (2 * v + a + 1) := by
    gcongr 36 * (v + 1) * ?_ ^ 2 * ?_ <;> omega
  obtain ⟨T, hT⟩ : ∃ T, (v + a + 1) ^ 2 * (2 * v + a + 1) = T := ⟨_, rfl⟩
  have hvT : v + 1 ≤ T :=
    hT ▸ (by omega : v + 1 ≤ 2 * v + a + 1).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have h4 : 11 * (v + 1) * Nat.size v ≤ 11 * (v + 1) * v := Nat.mul_le_mul_left _ (size_le_self v)
  have h5 : (v + 1) * (v + 1) ≤ (v + 1) * T := Nat.mul_le_mul_left _ hvT
  rw [show 48 * (v + 1) * (v + a + 1) ^ 2 * (2 * v + a + 1) = 48 * (v + 1) * T by
    rw [← hT]; ring]
  rw [show 36 * (v + 1) * (v + a + 1) ^ 2 * (2 * v + a + 1) = 36 * (v + 1) * T by
    rw [← hT]; ring] at h2
  nlinarith

/-- With at most `v²` arcs, `(v+1)(v+a+1)²(2v+a+1) ≤ (v+1)⁷`. -/
theorem ipBound_le (arcs : Finset (Fin v × Fin v)) :
    (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1) ≤ (v + 1) ^ 7 := by
  have ha : arcs.card ≤ v * v := by simpa using card_le_univ arcs
  calc (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1)
      ≤ (v + 1) * ((v + 1) ^ 2) ^ 2 * (v + 1) ^ 2 := by gcongr <;> nlinarith
    _ = (v + 1) ^ 7 := by ring

/-- **Corollary `cor:transversal`(2), gammoids, Boolean rank circuits.**  Let `M` be the gammoid of a
digraph with `v` vertices and `a` arcs, sources `S` and `m` elements placed at distinct vertices.
A Boolean circuit of size at most `48 (v+1)(v+a+1)²(2v+a+1) ≤ 48 (v+1)⁷` outputs `r(X)` in binary
for every set `X` of elements. -/
theorem gammoid_rankCircuit (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v))
    (ι : Fin m ↪ Fin v) :
    ∃ B : Circuit BoolOp m,
      B.size ≤ 48 * (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1) ∧
        B.size ≤ 48 * (v + 1) ^ 7 ∧
        ∀ X : Finset (Fin m), (bitsVal (B.eval boolInterp (indicator X)) : ℕ∞) =
          (gammoid arcs S ι).eRk ↑X := by
  obtain ⟨hs, he⟩ := gammoidCircuit_spec (arcs := arcs) (S := S) (ι := ι) rfl
  have h1 := hs.trans_le (gammoidCost_le sum_card_ipFamily_le)
  refine ⟨gammoidCircuit arcs S ι, h1, h1.trans ?_, he⟩
  have := Nat.mul_le_mul_left 48 (ipBound_le arcs)
  calc 48 * (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1)
      = 48 * ((v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1)) := by ring
    _ ≤ 48 * (v + 1) ^ 7 := this

/-- The size of Theorem A for the gammoid circuit: `3 m s + m L + 9 m² + 4 m + 4 L + 1 ≤
160 (m+1) U` when `s ≤ 48 U`, `L ≤ m` and `m + 1 ≤ U`. -/
theorem theoremA_gammoidCost_le {s L U : ℕ} (hs : s ≤ 48 * U) (hL : L ≤ m) (hU : m + 1 ≤ U) :
    3 * m * s + m * L + 9 * m ^ 2 + 4 * m + 4 * L + 1 ≤ 160 * (m + 1) * U := by
  have h1 := Nat.mul_le_mul_left (3 * m) hs
  have h2 := Nat.mul_le_mul_left m hL
  have h3 := Nat.mul_le_mul_left m hU
  nlinarith

/-- **Corollary `cor:transversal`(2), gammoids, signed tropical circuits.**  Let `M` be the gammoid of a
digraph with `v` vertices and `a` arcs, sources `S` and `m` elements placed at distinct vertices.
Then `h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size at
most `160 (m+1)(v+1)(v+a+1)²(2v+a+1) ≤ 160 (v+1)⁸`. -/
theorem theoremA_gammoid (arcs : Finset (Fin v × Fin v)) (S : Finset (Fin v))
    (ι : Fin m ↪ Fin v) :
    ∃ C : Circuit STOp m,
      C.size ≤ 160 * (m + 1) * (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1) ∧
        C.size ≤ 160 * (v + 1) ^ 8 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (gammoid arcs S ι) w] := by
  obtain ⟨B, hB, -, he⟩ := gammoid_rankCircuit arcs S ι
  obtain ⟨C, hC, heval⟩ := theoremA (gammoid arcs S ι) gammoid_ground B he
  have hmv : m ≤ v := by simpa using Fintype.card_le_of_embedding ι
  obtain ⟨U, hU⟩ : ∃ U, (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1) = U :=
    ⟨_, rfl⟩
  have hmU : m + 1 ≤ U := by
    rw [← hU]
    have h1 : 1 ≤ (v + arcs.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ 2 * v + arcs.card + 1 := by omega
    calc m + 1 ≤ (v + 1) * 1 * 1 := by omega
      _ ≤ (v + 1) * (v + arcs.card + 1) ^ 2 * (2 * v + arcs.card + 1) := by gcongr
  have hBU : B.size ≤ 48 * U := hB.trans_eq (by rw [← hU]; ring)
  have hCU := hC.trans (theoremA_gammoidCost_le hBU
    ((size_le_self _).trans (rank_le_card _)) hmU)
  have hU7 : U ≤ (v + 1) ^ 7 := hU ▸ ipBound_le arcs
  refine ⟨C, hCU.trans_eq (by rw [← hU]; ring), hCU.trans ?_, heval⟩
  calc 160 * (m + 1) * U ≤ 160 * (v + 1) * (v + 1) ^ 7 := by gcongr
    _ = 160 * (v + 1) ^ 8 := by ring

end Gammoid

end SignedTropical.Classes.Transversal
