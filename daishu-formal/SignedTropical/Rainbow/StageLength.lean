import SignedTropical.Rainbow.Potential

/-!
# The stage length

`greedy_intersection.tex`, Section 4.6, Theorem `thm:stagelength`: stage `r` of the PO-SL schedule
ends after at most `1 + (r - 1) k m` updates.  `M : Matroid (Fin m)` has ground set `univ` (`hE`),
rank `k` (`hk`) and a rainbow base (`hM`).  At a state `v` of stage `r < k`, `S = S₀ = Av(M^v)`,
`ρ = |S| - (k - r) = r_{M^v}(E_S)` (Lemma `lem:avoidable`(2)), `a` is the PO-SL update and
`v' = v - a_blk`.

* `card_inter_eq_rk`: a base `B` of `M^v` meeting `r` blocks has `|B ∩ E_S| = ρ`.
* `exists_pair`, **the crossing pair**: for every such `B`, some `x ∈ E_S` and `z ∉ E_S`, one of
  them in `B`, have `0 < v_x - v_z ≤ δ`, `δ` the first event of Step 3 of Theorem
  `thm:potential`.
* `crossPairs_ssubset`: the pairs `(x, z)` with `x ∈ E_S`, `z ∉ E_S`, one of them in `B`, and
  `v_z < v_x` (`crossPairs`, at most `k m` of them, `card_crossPairs_le`) lose the crossing pair
  at the update and gain none: `x` moves down by `τ`, `z` by at most `τ - δ`.
* `minCross`: `Q(v)`, the least number of such pairs over the bases of `M^v` meeting `r` blocks;
  `1 ≤ Q ≤ k m` (`minCross_bounds`), and `Q(v') < Q(v)` if `ν₀` and `S₀` are the same at `v'`
  (`minCross_lt`), since such a base stays a base of `M^{v'}` (Theorem `thm:validity`(2)).
* `av_ne_of_rk_eq_zero`, **an epoch with `ρ = 0` takes one update**: if `ν(M^{v'}) = r`, then
  `Av(M^{v'}) ≠ S₀`.
* `Phi₂`, the potential `Φ₂ = 0` for `ρ = 0` and `Φ₂ = ρ k m + 1 - Q` for `ρ ≥ 1`: it grows at
  every update of the stage (`Phi₂_lt_Phi₂_stageMap`) and stays below `1 + (r - 1) k m`
  (`Phi₂_lt`).  So at most `1 + (r - 1) k m` iterates of the stage map have `ν₀ = r`
  (`lt_of_nu_iterate_eq`).
-/

open Finset

namespace SignedTropical.Rainbow.StageLength

open SignedTropical.Rainbow SignedTropical.Rainbow.Validity SignedTropical.Rainbow.Potential

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {v : Fin m → ℝ} {r : ℕ}
  {B : Finset (Fin m)}

/-! ### The bases of `M^v` meeting `r` blocks -/

/-- A base `B` of `M^v` meeting `ν₀ = r` blocks has `|B ∩ E_{S₀}| = r_{M^v}(E_{S₀})`: the blocks
it misses, `k - r` of them, are avoidable, so `B ∩ E_{S₀}` meets at least `|S₀| - (k - r)`
blocks, which is `r_{M^v}(E_{S₀})` by Lemma `lem:avoidable`(2); and `B ∩ E_{S₀}` is independent
in `M^v`. -/
theorem card_inter_eq_rk (hr : nu (minBases M v) blk = r) (hB : (minBases M v).IsBase ↑B)
    (hBr : #(blocksMet blk B) = r) :
    #(B ∩ blockSet blk (Av (minBases M v) blk)) =
      rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) := by
  set S := Av (minBases M v) blk
  set X := blockSet blk S
  have hrk : r ≤ k := hBr ▸ (card_le_univ _).trans_eq (Fintype.card_fin k)
  have h1 : #S + r = k + rk (minBases M v) X := hr ▸ Exchange.card_av_add_nu (minBases M v) blk
  have h2 : #(B ∩ X) ≤ rk (minBases M v) X :=
    card_le_rk _ (hB.indep.subset (coe_subset.2 inter_subset_left)) inter_subset_right
  -- the blocks of `S` met by `B` are met by `B ∩ X`
  have hsub : S ∩ blocksMet blk B ⊆ blocksMet blk (B ∩ X) := fun b hb => by
    obtain ⟨e, he, rfl⟩ := mem_blocksMet.1 (mem_inter.1 hb).2
    exact mem_blocksMet.2 ⟨e, mem_inter.2 ⟨he, mem_blockSet.2 (mem_inter.1 hb).1⟩, rfl⟩
  have h3 := card_le_card hsub
  have h4 := card_le_card (sdiff_subset_sdiff (subset_univ S) (subset_refl (blocksMet blk B)))
  rw [card_univ_sdiff, hBr, Fintype.card_fin] at h4
  have h5 := card_sdiff_add_card_inter S (blocksMet blk B)
  have h6 : #(blocksMet blk (B ∩ X)) ≤ #(B ∩ X) := card_image_le
  omega

/-! ### The crossing pair -/

/-- **The crossing pair.**  Let `ν₀ = r`, `S = S₀`, `B` a base of `M^v` meeting `r` blocks, and
`δ ≥ 0` with `r_{N(δ)}(E_S) > r_{M^v}(E_S)` for the PO-SL family `N`.  Then some `x ∈ E_S` and
`z ∉ E_S` in one component of `M`, one of them in `B`, have `0 < v_x - v_z ≤ δ`.

Step 5 of Theorem `thm:potential` at `B` gives `g ∈ B \ E_S` and `y ∈ E_S \ B` in one cluster `C`
at scale `δ`, `v_g < v_y`.  Let `z₂` have the least value above `v_g` in `C ∩ E_S`, and `z₁` the
largest value below `v_{z₂}` in `C \ E_S`; no value of `C` lies strictly between, so
`v_{z₂} - v_{z₁} ≤ δ`.  If `z₂ ∈ B`, take `(z₂, z₁)`.  Otherwise some `b ∈ C(B, z₂) - z₂` has
`v_{z₂} - δ ≤ v_b ≤ v_{z₂}`, as `z₂ ∈ PO_δ`, and `b ∈ C`.  If `b ∉ E_S`, then `v_b < v_{z₂}`
(`lt_of_mem_fundCircuit`): take `(z₂, b)`.  If `b ∈ E_S` and `v_b = v_{z₂}`, take `(b, z₁)`.  If
`b ∈ E_S` and `v_b < v_{z₂}`, then `v_b ≤ v_g` by the choice of `z₂`: take `(z₂, g)`.  Every
pair lies in the cluster `C`, hence in one component. -/
theorem exists_pair (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B)
    (hr : nu (minBases M v) blk = r) (hB : (minBases M v).IsBase ↑B)
    (hBr : #(blocksMet blk B) = r) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hjump : rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) <
      rk (POSL.N M v δ) (blockSet blk (Av (minBases M v) blk))) :
    ∃ x z, blk x ∈ Av (minBases M v) blk ∧ blk z ∉ Av (minBases M v) blk ∧ (x ∈ B ∨ z ∈ B) ∧
      v z < v x ∧ v x - v z ≤ δ ∧ connRel M x z := by
  set S := Av (minBases M v) blk
  have hBX := card_inter_eq_rk hr hB hBr
  have hBmin : IsMinBase M v B := (isBase_minBases_iff hE).1 hB
  obtain ⟨g, y, hgB, -, hg, hy, hgy, hlt⟩ := exists_tie_of_isBase hE hM hδ0 hB hBX hjump
  set P := POSL.PO M v δ
  set C := POSL.cluster M P (POSL.near v δ) g
  have hgC : g ∈ C := POSL.mem_cluster.2 (.refl hgy.mem_left)
  -- `z₂`: the least value above `v_g` in `C ∩ E_S`
  obtain ⟨z₂, hz₂, hz₂min⟩ := exists_min_image (C.filter fun z => blk z ∈ S ∧ v g < v z) v
    ⟨y, mem_filter.2 ⟨POSL.mem_cluster.2 hgy, hy, hlt⟩⟩
  rw [mem_filter, POSL.mem_cluster] at hz₂
  -- `z₁`: the largest value below `v_{z₂}` in `C \ E_S`
  obtain ⟨z₁, hz₁, hz₁max⟩ := exists_max_image (C.filter fun z => blk z ∉ S ∧ v z < v z₂) v
    ⟨g, mem_filter.2 ⟨hgC, hg, hz₂.2.2⟩⟩
  rw [mem_filter, POSL.mem_cluster] at hz₁
  have hgz₁ : v g ≤ v z₁ := hz₁max g (mem_filter.2 ⟨hgC, hg, hz₂.2.2⟩)
  -- no value of `C` lies strictly between `v_{z₁}` and `v_{z₂}`
  have hgap : v z₂ - v z₁ ≤ δ := by
    refine ((hz₁.1.symm POSL.near_comm).trans hz₂.1).sub_le hz₁.2.2 fun x hx hx₁ => ?_
    have hxC : x ∈ C := POSL.mem_cluster.2 (hz₁.1.trans hx)
    by_cases hxS : blk x ∈ S
    · exact hz₂min x (mem_filter.2 ⟨hxC, hxS, hgz₁.trans_lt hx₁⟩)
    · exact not_lt.1 fun hxz₂ => (hz₁max x (mem_filter.2 ⟨hxC, hxS, hxz₂⟩)).not_gt hx₁
  by_cases hz₂B : z₂ ∈ B
  · exact ⟨z₂, z₁, hz₂.2.1, hz₁.2.1, .inl hz₂B, hz₁.2.2, hgap,
      ((hz₂.1.symm POSL.near_comm).trans hz₁.1).conn⟩
  -- the window: some `b ∈ C(B, z₂) - z₂` has `v_{z₂} - δ ≤ v_b`, as `z₂ ∈ PO_δ`
  have hz₂P : z₂ ∈ P := hz₂.1.mem_right
  have hCz₂ := hBmin.1.fundCircuit_isCircuit (by simp [hE]) (by simpa using hz₂B)
  obtain ⟨b, hbC, hbz, hb⟩ : ∃ b ∈ M.fundCircuit z₂ ↑B, b ≠ z₂ ∧ v z₂ - δ ≤ v b := by
    by_contra! hcon
    exact hz₂P (M.closure_subset_closure (fun f hf => hcon f hf.1 hf.2)
      (hCz₂.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit z₂ ↑B)))
  have hbB : b ∈ B := Pos.mem_of_mem_fundCircuit hbC hbz
  have hbz₂ : v b ≤ v z₂ := Conn.le_of_mem_fundCircuit hBmin hz₂B hbC
  -- `b` lies in the cluster `C`
  have hbP : b ∈ P := POSL.subset_PO_of_isMinBase hE hBmin hδ0 (mem_coe.2 hbB)
  have hconn : connRel M z₂ b := .inr ⟨_, hCz₂, M.mem_fundCircuit z₂ ↑B, hbC⟩
  have hgb : POSL.SameCluster M P (POSL.near v δ) g b :=
    hz₂.1.trans (.of_link hz₂P hbP hconn (by rw [POSL.near, abs_le]; constructor <;> linarith))
  by_cases hbS : blk b ∈ S
  · rcases hbz₂.lt_or_eq with hbz₂ | hbz₂
    · -- `v_b ≤ v_g` by the choice of `z₂`: the pair `(z₂, g)`
      have hbg : v b ≤ v g := not_lt.1 fun hgb' =>
        (hz₂min b (mem_filter.2 ⟨POSL.mem_cluster.2 hgb, hbS, hgb'⟩)).not_gt hbz₂
      exact ⟨z₂, g, hz₂.2.1, hg, .inr hgB, hz₂.2.2, by linarith,
        (hz₂.1.symm POSL.near_comm).conn⟩
    · -- the pair `(b, z₁)`
      exact ⟨b, z₁, hbS, hz₁.2.1, .inl hbB, hbz₂ ▸ hz₁.2.2, hbz₂ ▸ hgap,
        ((hgb.symm POSL.near_comm).trans hz₁.1).conn⟩
  · -- `v_b < v_{z₂}`: the pair `(z₂, b)`
    have hbz₂' := lt_of_mem_fundCircuit hE hBmin hBX hz₂B (mem_blockSet.2 hz₂.2.1)
      (fun h => hbS (mem_blockSet.1 h)) hbC
    exact ⟨z₂, b, hz₂.2.1, hbS, .inr hbB, hbz₂', by linarith, hconn⟩

/-! ### The pairs that have not crossed -/

/-- The pairs `(x, z)` with `x ∈ E_S`, `z ∉ E_S`, one of them in `B`, and `v_z < v_x`: the pairs
of `B` that have not crossed. -/
noncomputable def crossPairs (blk : Fin m → Fin k) (S : Finset (Fin k)) (B : Finset (Fin m))
    (v : Fin m → ℝ) : Finset (Fin m × Fin m) :=
  univ.filter fun q => blk q.1 ∈ S ∧ blk q.2 ∉ S ∧ (q.1 ∈ B ∨ q.2 ∈ B) ∧ v q.2 < v q.1

theorem mem_crossPairs {S : Finset (Fin k)} {x z : Fin m} :
    (x, z) ∈ crossPairs blk S B v ↔ blk x ∈ S ∧ blk z ∉ S ∧ (x ∈ B ∨ z ∈ B) ∧ v z < v x := by
  simp [crossPairs]

/-- `|crossPairs| ≤ |B| m`: a pair has its first element in `B ∩ E_S` or its second element in
`B \ E_S`. -/
theorem card_crossPairs_le (S : Finset (Fin k)) (B : Finset (Fin m)) (v : Fin m → ℝ) :
    #(crossPairs blk S B v) ≤ #B * m := by
  have hsub : crossPairs blk S B v ⊆ (B.filter fun x => blk x ∈ S) ×ˢ (univ : Finset (Fin m)) ∪
      (univ : Finset (Fin m)) ×ˢ (B.filter fun z => blk z ∉ S) := by
    rintro ⟨x, z⟩ hq
    rw [mem_crossPairs] at hq
    rcases hq.2.2.1 with hx | hz
    · exact mem_union_left _ (mem_product.2 ⟨mem_filter.2 ⟨hx, hq.1⟩, mem_univ _⟩)
    · exact mem_union_right _ (mem_product.2 ⟨mem_univ _, mem_filter.2 ⟨hz, hq.2.1⟩⟩)
  calc #(crossPairs blk S B v)
      ≤ #(B.filter fun x => blk x ∈ S) * m + m * #(B.filter fun z => blk z ∉ S) := by
        refine (card_le_card hsub).trans ((card_union_le _ _).trans_eq ?_)
        rw [card_product, card_product, card_univ, Fintype.card_fin]
    _ = #B * m := by
        rw [mul_comm m, ← add_mul, card_filter_add_card_filter_not]

/-- **Theorem `thm:stagelength`(1).**  Let `ν₀ = r < k`, `S = S₀` and `B` a base of `M^v` meeting
`r` blocks.  Some `x ∈ E_S` and `z ∉ E_S` in one component of `M`, one of them in `B`, have
`v_x > v_z` and, after the PO-SL update, `v'_x ≤ v'_z`: the pair of `exists_pair` at the first
event `δ` crosses, as `x` moves down by `τ` and `z` by at most `τ - δ`. -/
theorem exists_crossing_pair (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M v) blk = r) (hrk : r < k)
    (hB : (minBases M v).IsBase ↑B) (hBr : #(blocksMet blk B) = r) :
    ∃ x z, blk x ∈ Av (minBases M v) blk ∧ blk z ∉ Av (minBases M v) blk ∧ (x ∈ B ∨ z ∈ B) ∧
      v z < v x ∧ connRel M x z ∧
      shift blk v (update (POSL.N M v) blk r) x ≤ shift blk v (update (POSL.N M v) blk r) z := by
  have hN := POSL.isAdmissible hE hM v
  obtain ⟨δ, hδ0, hδτ, hbefore, hevent⟩ := exists_first_event hE hk hr hrk hN
  obtain ⟨x, z, hx, hz, hxz, hlt, hδ, hc⟩ :=
    exists_pair hE hM hr hB hBr hδ0.le (rk_lt_rk hr hN hδ0.le hevent)
  have ha : update (POSL.N M v) blk r (blk z) ≤ tau (POSL.N M v) blk r - δ :=
    update_le_of_forall_notMem hr.ge hN hδτ fun t ht0 htδ => by rwa [hbefore t ht0 htδ]
  refine ⟨x, z, hx, hz, hxz, hlt, hc, ?_⟩
  simp only [shift]
  rw [update_eq_tau hr hN hx]
  linarith

/-- **Every update makes a pair cross.**  Let `ν₀ = r < k`, `S = S₀` and `B` a base of `M^v`
meeting `r` blocks.  The PO-SL update moves every element of `E_S` down by `τ` and every other
element down by at most `τ`, so no pair of `B` that has crossed crosses back; and the pair of
`exists_crossing_pair` crosses. -/
theorem crossPairs_ssubset (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M v) blk = r) (hrk : r < k)
    (hB : (minBases M v).IsBase ↑B) (hBr : #(blocksMet blk B) = r) :
    crossPairs blk (Av (minBases M v) blk) B (shift blk v (update (POSL.N M v) blk r)) ⊂
      crossPairs blk (Av (minBases M v) blk) B v := by
  have hN := POSL.isAdmissible hE hM v
  obtain ⟨x, z, hx, hz, hxz, hlt, -, hcross⟩ := exists_crossing_pair hE hk hM hr hrk hB hBr
  refine (ssubset_iff_of_subset fun q hq => ?_).2 ⟨(x, z), mem_crossPairs.2 ⟨hx, hz, hxz, hlt⟩, ?_⟩
  · obtain ⟨y, g⟩ := q
    rw [mem_crossPairs] at hq ⊢
    refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_⟩
    have h := hq.2.2.2
    simp only [shift] at h
    rw [update_eq_tau hr hN hq.1] at h
    linarith [update_le_tau (N := POSL.N M v) (blk := blk) (r := r) (b := blk g)]
  · rw [mem_crossPairs]
    rintro ⟨-, -, -, h⟩
    exact (not_le.2 h) hcross

/-! ### The least number of pairs that have not crossed -/

/-- `Q(v)`: the least number of pairs that have not crossed (`crossPairs`, with `S = Av(M^v)`),
over the bases of `M^v` meeting `ν(M^v)` blocks. -/
noncomputable def minCross (M : Matroid (Fin m)) (blk : Fin m → Fin k) (v : Fin m → ℝ) : ℕ :=
  sInf {n | ∃ B : Finset (Fin m), (minBases M v).IsBase ↑B ∧
    #(blocksMet blk B) = nu (minBases M v) blk ∧ n = #(crossPairs blk (Av (minBases M v) blk) B v)}

theorem minCross_le (hB : (minBases M v).IsBase ↑B)
    (hBr : #(blocksMet blk B) = nu (minBases M v) blk) :
    minCross M blk v ≤ #(crossPairs blk (Av (minBases M v) blk) B v) :=
  Nat.sInf_le ⟨B, hB, hBr, rfl⟩

theorem exists_minCross_eq (M : Matroid (Fin m)) (blk : Fin m → Fin k) (v : Fin m → ℝ) :
    ∃ B : Finset (Fin m), (minBases M v).IsBase ↑B ∧ #(blocksMet blk B) = nu (minBases M v) blk ∧
      minCross M blk v = #(crossPairs blk (Av (minBases M v) blk) B v) := by
  obtain ⟨B, hB, hBr⟩ := exists_isBase_card_blocksMet (minBases M v) blk
  have hne : {n | ∃ B : Finset (Fin m), (minBases M v).IsBase ↑B ∧
      #(blocksMet blk B) = nu (minBases M v) blk ∧
        n = #(crossPairs blk (Av (minBases M v) blk) B v)}.Nonempty := ⟨_, B, hB, hBr, rfl⟩
  exact Nat.sInf_mem hne

/-- `1 ≤ Q(v) ≤ k m` at a state of stage `r < k`: a base attaining `Q(v)` has a crossing pair
(`crossPairs_ssubset`), and `|crossPairs| ≤ |B| m = k m`. -/
theorem minCross_bounds (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M v) blk = r) (hrk : r < k) :
    1 ≤ minCross M blk v ∧ minCross M blk v ≤ k * m := by
  obtain ⟨B, hB, hBr, hQ⟩ := exists_minCross_eq M blk v
  rw [hr] at hBr
  have h1 := card_lt_card (crossPairs_ssubset hE hk hM hr hrk hB hBr)
  have h2 := card_crossPairs_le (blk := blk) (Av (minBases M v) blk) B v
  rw [card_of_isBase_minBases hE hB, hk] at h2
  omega

/-- **`Q` decreases inside an epoch**: if `ν₀ = r` and `S₀` are the same after the update, then
`Q(v') < Q(v)`.  A base `B` of `M^v` meeting `r` blocks that attains `Q(v)` is a base of `M^{v'}`
meeting `r` blocks (Theorem `thm:validity`(2)), and one of its pairs crosses
(`crossPairs_ssubset`). -/
theorem minCross_lt (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hr : nu (minBases M v) blk = r) (hrk : r < k)
    (hr' : nu (minBases M (shift blk v (update (POSL.N M v) blk r))) blk = r)
    (hS : Av (minBases M (shift blk v (update (POSL.N M v) blk r))) blk =
      Av (minBases M v) blk) :
    minCross M blk (shift blk v (update (POSL.N M v) blk r)) < minCross M blk v := by
  obtain ⟨B, hB, hBr, hQ⟩ := exists_minCross_eq M blk v
  rw [hr] at hBr
  have hB' := (isBase_minBases_iff hE).2
    (isMinBase_update hE hr (POSL.isAdmissible hE hM v) hB hBr)
  have h := minCross_le hB' (hBr.trans hr'.symm)
  rw [hS] at h
  rw [hQ]
  exact h.trans_lt (card_lt_card (crossPairs_ssubset hE hk hM hr hrk hB hBr))

/-! ### An epoch with `ρ = 0` -/

/-- **An epoch with `ρ = 0` takes one update.**  Let `ν₀ = r < k` and `r_{M^v}(E_{S₀}) = 0`.  If
`ν(M^{v'}) = r` after the PO-SL update, then `Av(M^{v'}) ≠ S₀`.

At the first event `δ`, `r_{N(δ)}(E_{S₀}) > 0` (Step 4 of Theorem `thm:potential`), so some
`y ∈ E_{S₀}` lies in a base of `N(δ)`, hence in `PO_δ`.  If `Av(M^{v'}) = S₀`, then
`r_{M^{v'}}(E_{S₀}) = 0` (Lemma `lem:avoidable`(2)), and a minimum base `B'` of `v'` misses
`E_{S₀}`.  Every `f ∈ C(B', y) - y` has `v'_f < v'_y` (`lt_of_mem_fundCircuit`), and
`v'_y = v_y - τ`, `v'_f ≥ v_f - (τ - δ)`; so `v_f < v_y - δ`, and `y` lies in the closure of
`{g : v_g < v_y - δ}`, against `y ∈ PO_δ`. -/
theorem av_ne_of_rk_eq_zero (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M v) blk = r) (hrk : r < k)
    (h0 : rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) = 0)
    (hr' : nu (minBases M (shift blk v (update (POSL.N M v) blk r))) blk = r) :
    Av (minBases M (shift blk v (update (POSL.N M v) blk r))) blk ≠ Av (minBases M v) blk := by
  set S := Av (minBases M v) blk
  set X := blockSet blk S
  set v' := shift blk v (update (POSL.N M v) blk r)
  have hN := POSL.isAdmissible hE hM v
  obtain ⟨δ, hδ0, hδτ, hbefore, hevent⟩ := exists_first_event hE hk hr hrk hN
  have hjump : rk (minBases M v) X < rk (POSL.N M v δ) X := rk_lt_rk hr hN hδ0.le hevent
  -- some `y ∈ X` lies in a base of `N(δ)`, so `y ∈ PO_δ`
  obtain ⟨Bδ, hBδ, hBδX⟩ := exists_isBase_card_inter_eq (POSL.N M v δ) (hN.ground δ hδ0.le) X
  obtain ⟨y, hy⟩ : (Bδ ∩ X).Nonempty := card_pos.1 (by omega)
  have hyPO : y ∈ POSL.PO M v δ :=
    POSL.subset_PO_of_isBase_N hE hδ0.le hBδ (mem_coe.2 (mem_inter.1 hy).1)
  have hyX := (mem_inter.1 hy).2
  intro hS
  -- `r_{M^{v'}}(X) = 0` (Lemma `lem:avoidable`(2)), and a minimum base `B'` of `v'` misses `X`
  have h1 : #S + r = k + rk (minBases M v') X := by
    have := Exchange.card_av_add_nu (minBases M v') blk
    rw [hS, hr'] at this
    exact this
  have h2 : #S + r = k + rk (minBases M v) X := by
    have := Exchange.card_av_add_nu (minBases M v) blk
    rw [hr] at this
    exact this
  obtain ⟨B', hB'⟩ := exists_isMinBase M v'
  have h3 : #(B' ∩ X) ≤ rk (minBases M v') X := card_le_rk (minBases M v')
    ((hB'.isBase_minBases hE).indep.subset (coe_subset.2 inter_subset_left)) inter_subset_right
  have hB'X : #(B' ∩ X) = rk (minBases M v') X := by omega
  have hnot : ∀ f ∈ B', f ∉ X := fun f hf hfX => by
    have : 0 < #(B' ∩ X) := card_pos.2 ⟨f, mem_inter.2 ⟨hf, hfX⟩⟩
    omega
  have hyB' : y ∉ B' := fun h => hnot y h hyX
  -- the elements `f ≠ y` of `C(B', y)` have `v_f < v_y - δ`
  have hC := hB'.1.fundCircuit_isCircuit (by simp [hE]) (by simpa using hyB')
  refine hyPO (M.closure_subset_closure (fun f hf => ?_)
    (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit y ↑B')))
  have hfX : f ∉ X := hnot f (Pos.mem_of_mem_fundCircuit hf.1 hf.2)
  have hlt : v' f < v' y := lt_of_mem_fundCircuit hE hB' hB'X hyB' hyX hfX hf.1
  have ha : update (POSL.N M v) blk r (blk f) ≤ tau (POSL.N M v) blk r - δ :=
    update_le_of_forall_notMem hr.ge hN hδτ fun t ht0 htδ => by
      rw [hbefore t ht0 htδ]
      exact fun h => hfX (mem_blockSet.2 h)
  show v f < v y - δ
  simp only [v', shift] at hlt
  rw [update_eq_tau hr hN (mem_blockSet.1 hyX)] at hlt
  linarith

/-! ### The potential -/

/-- The value of the potential: `0` for `ρ = 0`, and `ρ K + 1 - Q` otherwise. -/
def phiVal (ρ K Q : ℕ) : ℕ := if ρ = 0 then 0 else ρ * K + 1 - Q

/-- `phiVal ρ K Q ≤ ρ K` for `Q ≥ 1`. -/
theorem phiVal_le {ρ K Q : ℕ} (hQ1 : 1 ≤ Q) : phiVal ρ K Q ≤ ρ * K := by
  unfold phiVal
  split_ifs with hρ
  · exact Nat.zero_le _
  · omega

theorem phiVal_lt {ρ K Q r : ℕ} (hQ1 : 1 ≤ Q) (hρ : ρ + 1 ≤ r) :
    phiVal ρ K Q < 1 + (r - 1) * K := by
  have := Nat.mul_le_mul_right K (show ρ ≤ r - 1 by omega)
  have := phiVal_le (K := K) (ρ := ρ) hQ1
  omega

theorem phiVal_lt_phiVal_of_lt {ρ K Q Q' : ℕ} (hρ : ρ ≠ 0) (hQ : Q' < Q) (hQK : Q ≤ K) :
    phiVal ρ K Q < phiVal ρ K Q' := by
  have := Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hρ)
  unfold phiVal
  rw [if_neg hρ, if_neg hρ]
  omega

theorem phiVal_lt_phiVal_of_lt_left {ρ ρ' K Q Q' : ℕ} (hρ : ρ < ρ') (hQ1 : 1 ≤ Q)
    (hQ'K : Q' ≤ K) : phiVal ρ K Q < phiVal ρ' K Q' := by
  have h1 := phiVal_le (K := K) (ρ := ρ) hQ1
  have h2 := Nat.mul_le_mul_right K (show ρ + 1 ≤ ρ' from hρ)
  rw [add_one_mul] at h2
  have h3 : phiVal ρ' K Q' = ρ' * K + 1 - Q' := if_neg (by omega)
  omega

/-- The potential of Theorem `thm:stagelength` at a state `p` of stage `r`: with `v = w - p_blk`,
`S₀ = Av(M^v)` and `ρ = |S₀| + r - k`, `Φ₂ = 0` if `ρ = 0` and `Φ₂ = ρ k m + 1 - Q(v)`
otherwise. -/
noncomputable def Phi₂ (M : Matroid (Fin m)) (blk : Fin m → Fin k) (w : Fin m → ℝ) (r : ℕ)
    (p : Fin k → ℝ) : ℕ :=
  phiVal (#(Av (minBases M (shift blk w p)) blk) + r - k) (k * m) (minCross M blk (shift blk w p))

variable {w : Fin m → ℝ} {p : Fin k → ℝ}

/-- `Φ₂(p) < 1 + (r - 1) k m` at a state of stage `r < k`: `ρ ≤ r - 1` and `Q ≥ 1`. -/
theorem Phi₂_lt (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hr : nu (minBases M (shift blk w p)) blk = r) (hrk : r < k) :
    Phi₂ M blk w r p < 1 + (r - 1) * (k * m) := by
  obtain ⟨h1, h2⟩ := card_av_bounds hE hk hr hrk
  exact phiVal_lt (minCross_bounds hE hk hM hr hrk).1 (by omega)

/-- **The potential grows at every update within stage `r`.**  By Theorem `thm:potential`(1),
`S₀` grows or stays.  If it stays, then `ρ ≥ 1` (`av_ne_of_rk_eq_zero`) and `Q` decreases
(`minCross_lt`).  If it grows, `ρ` grows, and `Φ₂` passes from at most `ρ k m` to at least
`(ρ + 1) k m + 1 - k m`. -/
theorem Phi₂_lt_Phi₂_stageMap (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M (shift blk w p)) blk = r)
    (hrk : r < k) (hr' : nu (minBases M (shift blk w (stageMap M blk w r p))) blk = r) :
    Phi₂ M blk w r p < Phi₂ M blk w r (stageMap M blk w r p) := by
  rw [shift_stageMap] at hr'
  rw [Phi₂, Phi₂, shift_stageMap]
  set v := shift blk w p
  have hsub := av_subset_av_update hE hr (POSL.isAdmissible hE hM v) hr'
  have hb := (card_av_bounds hE hk hr hrk).1
  have hQ := minCross_bounds hE hk hM hr hrk
  have hQ' := minCross_bounds hE hk hM hr' hrk
  rcases hsub.eq_or_ssubset with heq | hss
  · rw [← heq]
    have hρ : #(Av (minBases M v) blk) + r - k ≠ 0 := fun h0 => by
      refine av_ne_of_rk_eq_zero hE hk hM hr hrk ?_ hr' heq.symm
      have := Exchange.card_av_add_nu (minBases M v) blk
      rw [hr] at this
      omega
    exact phiVal_lt_phiVal_of_lt hρ (minCross_lt hE hk hM hr hrk hr' heq.symm) hQ.2
  · have := card_lt_card hss
    exact phiVal_lt_phiVal_of_lt_left (by omega) hQ.1 hQ'.2

/-- Within stage `r`, the `n`-th iterate of a state of stage `r` has potential at least `n`. -/
theorem le_Phi₂_iterate (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k)
    (hp : r ≤ nu (minBases M (shift blk w p)) blk) (n : ℕ)
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) :
    n ≤ Phi₂ M blk w r ((stageMap M blk w r)^[n] p) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn ⊢
    have hn' : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r :=
      le_antisymm ((nu_le_nu_stageMap hE hM (le_nu_iterate hE hM hp n)).trans_eq hn)
        (le_nu_iterate hE hM hp n)
    exact (ih hn').trans_lt (Phi₂_lt_Phi₂_stageMap hE hk hM hn' hrk hn)

/-- **Theorem `thm:stagelength`**, counting form: from a state with `ν₀ ≥ r`, the iterates of the
stage-`r` map with `ν₀ = r` are those with `n < 1 + (r - 1) k m`; so at most `1 + (r - 1) k m`
updates are applied at states of stage `r`. -/
theorem lt_of_nu_iterate_eq (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k)
    (hp : r ≤ nu (minBases M (shift blk w p)) blk) {n : ℕ}
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) :
    n < 1 + (r - 1) * (k * m) :=
  (le_Phi₂_iterate hE hk hM hrk hp n hn).trans_lt (Phi₂_lt hE hk hM hn hrk)

end SignedTropical.Rainbow.StageLength
