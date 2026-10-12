import SignedTropical.Rainbow.Validity
import SignedTropical.Rainbow.POSL

/-!
# The potential and the stage bound

`greedy_intersection.tex`, Section 4.6 (Termination), Theorem `thm:potential` and its proof,
Steps 1 to 8.  `M : Matroid (Fin m)` has ground set `univ` (`hE`), rank `k` (`hk`) and a rainbow
base (`hM`); the blocks are the fibres of `blk : Fin m → Fin k`.  At a state `v` of stage `r`,
`ν₀ = ν(M^v) = r < k`, `S₀ = Av(M^v)`, the PO-SL family is `POSL.N M v` (Definition `def:posl`,
admissible by `POSL.isAdmissible`), its update is `a = update (POSL.N M v) blk r` (Definition
`def:update`, `Rainbow/Update.lean`), and `v' = v - a_blk = shift blk v a`.

* `piPairs blk S v`: `Π(v) = {(y, g) : y ∈ E_S, g ∉ E_S, v_y ≤ v_g}`, ties included;
  `card_piPairs_le`: `|Π| ≤ ⌊m² / 4⌋`.
* `potential` (Theorem `thm:potential`, items 1 to 3): `Av(M^{v'}) ⊇ S₀` if `ν(M^{v'}) = r`;
  `Π(v') ⊇ Π(v)`; `Π(v') ≠ Π(v)`, both formed with `S₀`.  Items 1 and 2 hold for every
  admissible family (`av_subset_av_update`, `piPairs_subset`); item 3 is `piPairs_ne`, through
  `exists_first_event` (Step 3), `rk_lt_rk` (Step 4), `exists_tie` (Step 5) and
  `exists_crossing` (Step 6).  Step 5 at a given base (`exists_tie_of_isBase`,
  `lt_of_mem_fundCircuit`) is also the start of Theorem `thm:stagelength`
  (`Rainbow/StageLength.lean`).
* The consequence (Step 8).  `stageMap M blk w r` is the stage-`r` update map
  `p ↦ p + a(p)`, with `a(p)` the PO-SL update at `v = w - p_blk`.  `stage_bound`: from any `p`
  with `ν₀(p) ≥ r`, after `r (⌊m² / 4⌋ + 1)` iterations `ν₀ ≥ r + 1`; `stageMap_eq_self`: an
  update at a state with `ν₀ > r` is the identity.  The paper counts the values of `S₀` and the
  sizes of `Π`; the proof here packs both counts into one potential
  `Phi = (|S₀| - (k - r)) (⌊m² / 4⌋ + 1) + |Π|`, which grows at every update of the stage
  (`Phi_lt_Phi_stageMap`) and stays below `r (⌊m² / 4⌋ + 1)` (`Phi_lt`).
-/

open Finset

namespace SignedTropical.Rainbow.Potential

open SignedTropical.Rainbow SignedTropical.Rainbow.Validity

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {v : Fin m → ℝ}
  {N : ℝ → Matroid (Fin m)} {r : ℕ}

/-! ### The pairs `Π` -/

/-- `Π = {(y, g) : y ∈ E_S, g ∉ E_S, v_y ≤ v_g}` for a set of blocks `S`: the pairs in which an
element of a raised block is at or below an element of an unraised one, ties included. -/
noncomputable def piPairs (blk : Fin m → Fin k) (S : Finset (Fin k)) (v : Fin m → ℝ) :
    Finset (Fin m × Fin m) :=
  univ.filter fun q => blk q.1 ∈ S ∧ blk q.2 ∉ S ∧ v q.1 ≤ v q.2

theorem mem_piPairs {S : Finset (Fin k)} {y g : Fin m} :
    (y, g) ∈ piPairs blk S v ↔ blk y ∈ S ∧ blk g ∉ S ∧ v y ≤ v g := by
  simp [piPairs]

/-- `|Π| ≤ |E_S| |E \ E_S| ≤ ⌊m² / 4⌋`. -/
theorem card_piPairs_le (blk : Fin m → Fin k) (S : Finset (Fin k)) (v : Fin m → ℝ) :
    #(piPairs blk S v) ≤ m ^ 2 / 4 := by
  have hsub : piPairs blk S v ⊆ blockSet blk S ×ˢ (univ \ blockSet blk S) := by
    rintro ⟨y, g⟩ hq
    rw [mem_piPairs] at hq
    simp [hq.1, hq.2.1]
  refine (card_le_card hsub).trans ?_
  rw [card_product, card_univ_sdiff, Fintype.card_fin]
  have ha : #(blockSet blk S) ≤ m := (card_le_univ _).trans_eq (Fintype.card_fin m)
  generalize #(blockSet blk S) = a at ha ⊢
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_sub_cancel_left, Nat.le_div_iff_mul_le (by norm_num)]
  have : (a : ℤ) * b * 4 ≤ ((a : ℤ) + b) ^ 2 := by nlinarith [sq_nonneg ((a : ℤ) - b)]
  exact_mod_cast this

/-! ### Items 1 and 2, for every admissible family -/

/-- **Theorem `thm:potential`(1)**, for every admissible family: if `ν(M^{v'}) = r`, then
`Av(M^{v'}) ⊇ S₀`.  A block of `S₀` is missed by a base of `M^v` meeting `r` blocks, which stays
minimum at `v'` (Theorem `thm:validity`). -/
theorem av_subset_av_update (hE : M.E = Set.univ) (hr : nu (minBases M v) blk = r)
    (hN : IsAdmissible M blk v N)
    (h : nu (minBases M (shift blk v (update N blk r))) blk = r) :
    Av (minBases M v) blk ⊆ Av (minBases M (shift blk v (update N blk r))) blk := by
  intro b hb
  obtain ⟨B, hB, hBr, hbB⟩ := (mem_Av_iff_baseMisses hr).1 hb
  exact (mem_Av_iff_baseMisses h).2
    ⟨B, (isBase_minBases_iff hE).2 (isMinBase_update hE hr hN hB hBr), hBr, hbB⟩

/-- **Theorem `thm:potential`(2)**, for every admissible family: `Π(v') ⊇ Π(v)`, both formed
with `S₀`.  Blocks of `S₀` move down by `τ`, every other block by `a_b ≤ τ`. -/
theorem piPairs_subset (hr : nu (minBases M v) blk = r) (hN : IsAdmissible M blk v N) :
    piPairs blk (Av (minBases M v) blk) v ⊆
      piPairs blk (Av (minBases M v) blk) (shift blk v (update N blk r)) := by
  rintro ⟨y, g⟩ hyg
  rw [mem_piPairs] at hyg ⊢
  refine ⟨hyg.1, hyg.2.1, ?_⟩
  simp only [shift]
  rw [update_eq_tau hr hN hyg.1]
  linarith [hyg.2.2, update_le_tau (N := N) (blk := blk) (r := r) (b := blk g)]

/-! ### Steps 3 and 4: the first event and a rank jump -/

/-- **Step 3, the first event.**  The least `t ≥ 0` at which `Av(N(t)) ≠ S₀` or
`ν(N(t)) > r` exists by (F5); it satisfies `0 < δ ≤ τ`, and `Av(N(t)) = S₀` for `0 ≤ t < δ`. -/
theorem exists_first_event (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : nu (minBases M v) blk = r) (hrk : r < k) (hN : IsAdmissible M blk v N) :
    ∃ δ, 0 < δ ∧ δ ≤ tau N blk r ∧
      (∀ t, 0 ≤ t → t < δ → Av (N t) blk = Av (minBases M v) blk) ∧
      (Av (N δ) blk ≠ Av (minBases M v) blk ∨ r < nu (N δ) blk) := by
  have hτ := (isLeast_tau hE hk hrk hN).1
  obtain ⟨⟨hδ0, hδ⟩, hleast⟩ := isLeast_sInf
    (P := fun N' => Av N' blk ≠ Av (minBases M v) blk ∨ r < nu N' blk) hN.F5
    ⟨_, hτ.1, .inr hτ.2⟩
  refine ⟨_, hδ0.lt_of_ne fun h0 => ?_, hleast ⟨hτ.1, .inr hτ.2⟩, fun t ht0 htδ => ?_, hδ⟩
  · rw [← h0, hN.F1, hr] at hδ
    simp at hδ
  · by_contra hne
    exact (hleast ⟨ht0, .inl hne⟩).not_gt htδ

/-- **Step 4, a rank jump.**  At the first event, `r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`, where
`|S₀| - r_{M^v}(E_{S₀}) = k - r` (Lemma `lem:avoidable`(2)). -/
theorem rk_lt_rk (hr : nu (minBases M v) blk = r) (hN : IsAdmissible M blk v N) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : Av (N δ) blk ≠ Av (minBases M v) blk ∨ r < nu (N δ) blk) :
    rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) <
      rk (N δ) (blockSet blk (Av (minBases M v) blk)) := by
  have h0 := Exchange.card_av_add_nu (minBases M v) blk
  have h1 := Exchange.card_add_nu_le (N δ) blk (Av (minBases M v) blk)
  rw [hr] at h0
  by_cases hlt : r < nu (N δ) blk
  · omega
  have hν : nu (N δ) blk = r := le_antisymm (not_lt.1 hlt) (hr ▸ nu_zero_le hN hδ0)
  -- `S₀ ⊆ Av(N(δ))` by (F2), so `S₀` does not attain equality in Lemma `lem:avoidable`(1)
  have hsub : Av (minBases M v) blk ⊆ Av (N δ) blk := fun b hb => by
    rw [← hN.F1] at hb hr
    exact (mem_Av_iff_baseMisses hν).2 (((mem_Av_iff_baseMisses hr).1 hb).mono hN le_rfl hδ0)
  have hstrict : #(Av (minBases M v) blk) + nu (N δ) blk ≠
      k + rk (N δ) (blockSet blk (Av (minBases M v) blk)) := fun heq =>
    hδ.resolve_right hlt (subset_antisymm (Exchange.av_subset heq) hsub)
  omega

/-! ### Steps 5 to 7 for PO-SL: a tie across `S₀`, a crossing pair, item 3 -/

/-- Some base `B` of a matroid `M'` on `E` has `|B ∩ X| = r_{M'}(X)`. -/
theorem exists_isBase_card_inter_eq (M' : Matroid (Fin m)) (hE' : M'.E = Set.univ)
    (X : Finset (Fin m)) : ∃ B : Finset (Fin m), M'.IsBase ↑B ∧ #(B ∩ X) = rk M' X := by
  obtain ⟨I, hI⟩ := M'.exists_isBasis (X : Set (Fin m)) (by rw [hE']; exact Set.subset_univ _)
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  obtain ⟨B, rfl⟩ := exists_finset B
  obtain ⟨I, rfl⟩ := exists_finset I
  refine ⟨B, hB, le_antisymm (card_le_rk _ (hB.indep.subset (coe_subset.2 inter_subset_left))
    inter_subset_right) ?_⟩
  rw [← card_eq_rk _ hI]
  exact card_le_card (subset_inter (coe_subset.1 hIB) (coe_subset.1 hI.subset))

/-- Let `B` be a minimum base of `v` with `|B ∩ X| = r_{M^v}(X)`, `y ∈ X \ B` and
`g ∈ C(B, y) \ X`.  Then `v_g < v_y`: `v_g ≤ v_y` as `B` is minimum, and if `v_g = v_y`, then
`B - g + y` is a minimum base (Lemma `lem:minbases`(3)) with `|B ∩ X| + 1` elements in `X`. -/
theorem lt_of_mem_fundCircuit (hE : M.E = Set.univ) {B X : Finset (Fin m)}
    (hBmin : IsMinBase M v B) (hBX : #(B ∩ X) = rk (minBases M v) X) {g y : Fin m}
    (hyB : y ∉ B) (hyX : y ∈ X) (hgX : g ∉ X) (hgC : g ∈ M.fundCircuit y ↑B) : v g < v y := by
  have hgB : g ∈ B := Pos.mem_of_mem_fundCircuit hgC (ne_of_mem_of_not_mem hyX hgX).symm
  refine (Conn.le_of_mem_fundCircuit hBmin hyB hgC).lt_of_ne fun heq => ?_
  have hB' := (hBmin.isMinBase_exchange_iff hE hyB hgB).2 ⟨hgC, heq⟩
  have h1 := card_le_rk (minBases M v) ((hB'.isBase_minBases hE).indep.subset
    (coe_subset.2 inter_subset_left)) (inter_subset_right (s₁ := insert y (B.erase g)) (s₂ := X))
  have h2 : insert y (B ∩ X) ⊆ insert y (B.erase g) ∩ X := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_inter.2 ⟨mem_insert_self _ _, hyX⟩
    · exact mem_inter.2 ⟨mem_insert_of_mem (mem_erase.2
        ⟨ne_of_mem_of_not_mem (mem_inter.1 hx).2 hgX, (mem_inter.1 hx).1⟩), (mem_inter.1 hx).2⟩
  have h3 := card_le_card h2
  rw [card_insert_of_notMem fun h => hyB (mem_inter.1 h).1] at h3
  omega

/-- **Step 5, a tie across `S₀`, at a given base.**  Let `δ ≥ 0` with
`r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`, where `N` is PO-SL, and let `B` be a base of `M^v` with
`|B ∩ E_{S₀}| = r_{M^v}(E_{S₀})`.  Then some `g ∈ B \ E_{S₀}` and `y ∈ E_{S₀} \ B` lie in one
cluster at scale `δ`, with `v_g < v_y`. -/
theorem exists_tie_of_isBase (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B) {δ : ℝ}
    (hδ0 : 0 ≤ δ) {B : Finset (Fin m)} (hB : (minBases M v).IsBase ↑B)
    (hBX : #(B ∩ blockSet blk (Av (minBases M v) blk)) =
      rk (minBases M v) (blockSet blk (Av (minBases M v) blk)))
    (hjump : rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) <
      rk (POSL.N M v δ) (blockSet blk (Av (minBases M v) blk))) :
    ∃ g y, g ∈ B ∧ y ∉ B ∧ blk g ∉ Av (minBases M v) blk ∧ blk y ∈ Av (minBases M v) blk ∧
      POSL.SameCluster M (POSL.PO M v δ) (POSL.near v δ) g y ∧ v g < v y := by
  set X := blockSet blk (Av (minBases M v) blk)
  have hN := POSL.isAdmissible hE hM v
  -- `B` is a base of `N(δ)`
  have hBmin : IsMinBase M v B := (isBase_minBases_iff hE).1 hB
  have hBδ : (POSL.N M v δ).IsBase ↑B := hN.F2 0 δ le_rfl hδ0 B (hN.F1 ▸ hB)
  have hNE : (POSL.N M v δ).E = Set.univ := Conn.minBases_ground M _
  -- `B ∩ X` does not span `X` in `N(δ)`
  obtain ⟨y, hyX, hy⟩ : ∃ y ∈ X, y ∉ (POSL.N M v δ).closure ↑(B ∩ X) := by
    by_contra! h
    have := card_eq_rk _ ((hBδ.indep.subset (coe_subset.2 inter_subset_left))
      |>.isBasis_of_subset_of_subset_closure (coe_subset.2 inter_subset_right) fun y hy => h y hy)
    omega
  have hyB : y ∉ B := fun hyB =>
    hy ((POSL.N M v δ).mem_closure_of_mem' (mem_coe.2 (mem_inter.2 ⟨hyB, hyX⟩)) (by simp [hNE]))
  -- the circuit of `y` in `B + y` in `N(δ)` meets some `g ∈ B \ X`
  have hC := hBδ.fundCircuit_isCircuit (by simp [hNE]) (by simpa using hyB)
  obtain ⟨g, hgC, hgy, hgX⟩ : ∃ g ∈ (POSL.N M v δ).fundCircuit y ↑B, g ≠ y ∧ g ∉ X := by
    by_contra! h
    refine hy ((POSL.N M v δ).closure_subset_closure ?_
      (hC.mem_closure_sdiff_singleton_of_mem ((POSL.N M v δ).mem_fundCircuit y ↑B)))
    rintro g ⟨hgC, hgy⟩
    have hgB : g ∈ B := by
      simpa [show g ≠ y from hgy] using (POSL.N M v δ).fundCircuit_subset_insert y ↑B hgC
    exact mem_coe.2 (mem_inter.2 ⟨hgB, h g hgC hgy⟩)
  -- Lemma `lem:minbases`(3) for `u_δ`: `g ∈ C(B, y)` and `u_δ(g) = u_δ(y)`
  have hBu : IsMinBase M (fun e => (POSL.u M v δ e : ℝ)) B := (POSL.isBase_N_iff hE).1 hBδ
  have hgC' : g ∈ (minBases M fun e => (POSL.u M v δ e : ℝ)).fundCircuit y ↑B := hgC
  rw [hBu.fundCircuit_minBases hE hyB] at hgC'
  obtain ⟨hgCM, hgu⟩ : g ∈ M.fundCircuit y ↑B ∧ (POSL.u M v δ g : ℝ) = POSL.u M v δ y := by
    simpa [hgy] using hgC'
  have hgB : g ∈ B := by
    simpa [hgy] using M.fundCircuit_subset_insert y ↑B hgCM
  -- one component and one cluster
  have hconn : connRel M g y := .inr ⟨_, hBmin.1.fundCircuit_isCircuit (by simp [hE])
    (by simpa using hyB), hgCM, M.mem_fundCircuit y ↑B⟩
  have hgPO : g ∈ POSL.PO M v δ := POSL.subset_PO_of_isBase_N hE hδ0 hBδ (mem_coe.2 hgB)
  have hgu' : POSL.u M v δ g = POSL.u M v δ y := by exact_mod_cast hgu
  have hyPO : y ∈ POSL.PO M v δ := POSL.u_le_iff_mem.1 (hgu' ▸ POSL.u_le_iff_mem.2 hgPO)
  exact ⟨g, y, hgB, hyB, fun h => hgX (mem_blockSet.2 h), mem_blockSet.1 hyX,
    (POSL.u_eq_u_iff hδ0 hgPO hyPO hconn).1 hgu',
    lt_of_mem_fundCircuit hE hBmin hBX hyB hyX hgX hgCM⟩

/-- **Step 5, a tie across `S₀`.**  Let `δ ≥ 0` with `r_{N(δ)}(E_{S₀}) > r_{M^v}(E_{S₀})`, where
`N` is PO-SL.  Then some `g ∉ E_{S₀}` and `y ∈ E_{S₀}` lie in one cluster at scale `δ`, with
`v_g < v_y`: `exists_tie_of_isBase` at a base `B` of `M^v` with
`|B ∩ E_{S₀}| = r_{M^v}(E_{S₀})`. -/
theorem exists_tie (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hjump : rk (minBases M v) (blockSet blk (Av (minBases M v) blk)) <
      rk (POSL.N M v δ) (blockSet blk (Av (minBases M v) blk))) :
    ∃ g y, blk g ∉ Av (minBases M v) blk ∧ blk y ∈ Av (minBases M v) blk ∧
      POSL.SameCluster M (POSL.PO M v δ) (POSL.near v δ) g y ∧ v g < v y := by
  obtain ⟨B, hB, hBX⟩ := exists_isBase_card_inter_eq (minBases M v) (Conn.minBases_ground M v)
    (blockSet blk (Av (minBases M v) blk))
  obtain ⟨g, y, -, -, h⟩ := exists_tie_of_isBase hE hM hδ0 hB hBX hjump
  exact ⟨g, y, h⟩

/-- **Step 6, a crossing pair.**  If `g ∉ E_S` and `y ∈ E_S` lie in one cluster at scale `δ`
and `v_g < v_y`, then the cluster contains `z₁ ∉ E_S` and `z₂ ∈ E_S` with
`0 < v_{z₂} - v_{z₁} ≤ δ`: `v_{z₁} = α` is the largest value below `v_y` outside `E_S`, and
`v_{z₂} = β` the least value above `α` in `E_S`, consecutive values of the cluster. -/
theorem exists_crossing {S : Finset (Fin k)} {δ : ℝ} {g y : Fin m} (hg : blk g ∉ S)
    (hy : blk y ∈ S) (hgy : POSL.SameCluster M (POSL.PO M v δ) (POSL.near v δ) g y)
    (hlt : v g < v y) :
    ∃ z₁ z₂, blk z₁ ∉ S ∧ blk z₂ ∈ S ∧ v z₁ < v z₂ ∧ v z₂ - v z₁ ≤ δ := by
  set C := POSL.cluster M (POSL.PO M v δ) (POSL.near v δ) g
  obtain ⟨z₁, hz₁, hz₁max⟩ := exists_max_image (C.filter fun z => blk z ∉ S ∧ v z < v y) v
    ⟨g, mem_filter.2 ⟨POSL.mem_cluster.2 (.refl hgy.mem_left), hg, hlt⟩⟩
  rw [mem_filter, POSL.mem_cluster] at hz₁
  have hyU : y ∈ C.filter fun z => blk z ∈ S ∧ v z₁ < v z :=
    mem_filter.2 ⟨POSL.mem_cluster.2 hgy, hy, hz₁.2.2⟩
  obtain ⟨z₂, hz₂, hz₂min⟩ := exists_min_image (C.filter fun z => blk z ∈ S ∧ v z₁ < v z) v
    ⟨y, hyU⟩
  rw [mem_filter, POSL.mem_cluster] at hz₂
  refine ⟨z₁, z₂, hz₁.2.1, hz₂.2.1, hz₂.2.2, ((hz₁.1.symm POSL.near_comm).trans hz₂.1).sub_le
    hz₂.2.2 fun x hx hx₁ => ?_⟩
  have hgx := POSL.mem_cluster.2 (hz₁.1.trans hx)
  by_cases hxS : blk x ∈ S
  · exact hz₂min x (mem_filter.2 ⟨hgx, hxS, hx₁⟩)
  · exact (hz₂min y hyU).trans (not_lt.1 fun hxy =>
      (hz₁max x (mem_filter.2 ⟨hgx, hxS, hxy⟩)).not_gt hx₁)

/-- **Theorem `thm:potential`(3)** (Steps 3 to 7): `Π(v') ≠ Π(v)`, both formed with `S₀`, for the
PO-SL update.  The crossing pair `z₁`, `z₂` of the first event `δ` has
`v'_{z₂} - v'_{z₁} ≤ (β - α) - τ + (τ - δ) ≤ 0`, so `(z₂, z₁) ∈ Π(v') \ Π(v)`. -/
theorem piPairs_ne (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hr : nu (minBases M v) blk = r) (hrk : r < k) :
    piPairs blk (Av (minBases M v) blk) (shift blk v (update (POSL.N M v) blk r)) ≠
      piPairs blk (Av (minBases M v) blk) v := by
  have hN := POSL.isAdmissible hE hM v
  obtain ⟨δ, hδ0, hδτ, hbefore, hevent⟩ := exists_first_event hE hk hr hrk hN
  obtain ⟨g, y, hg, hy, hgy, hlt⟩ := exists_tie hE hM hδ0.le (rk_lt_rk hr hN hδ0.le hevent)
  obtain ⟨z₁, z₂, hz₁, hz₂, h₁₂, hδ⟩ := exists_crossing hg hy hgy hlt
  -- Step 7: `a_{z₂} = τ` and `a_{z₁} ≤ τ - δ`
  have ha₂ := update_eq_tau hr hN hz₂
  have ha₁ : update (POSL.N M v) blk r (blk z₁) ≤ tau (POSL.N M v) blk r - δ :=
    update_le_of_forall_notMem hr.ge hN hδτ fun t ht0 htδ => by rwa [hbefore t ht0 htδ]
  intro heq
  have hmem : (z₂, z₁) ∈ piPairs blk (Av (minBases M v) blk)
      (shift blk v (update (POSL.N M v) blk r)) := by
    rw [mem_piPairs, shift, shift, ha₂]
    exact ⟨hz₂, hz₁, by linarith⟩
  rw [heq, mem_piPairs] at hmem
  linarith [hmem.2.2]

/-- **Theorem `thm:potential`**, items 1 to 3.  Let `M` have ground set `E`, rank `k` and a
rainbow base, let `ν₀ = ν(M^v) = r < k`, let `a` be the PO-SL update (Definitions `def:posl`
and `def:update`), `v' = v - a_blk` and `S₀ = Av(M^v)`.  Then
1. if `ν(M^{v'}) = r`, then `Av(M^{v'}) ⊇ S₀`;
2. `Π(v') ⊇ Π(v)`, both formed with `S₀`;
3. `Π(v') ≠ Π(v)`.

The consequence, the stage bound, is `stage_bound`. -/
theorem potential (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hr : nu (minBases M v) blk = r) (hrk : r < k) :
    (nu (minBases M (shift blk v (update (POSL.N M v) blk r))) blk = r →
        Av (minBases M v) blk ⊆ Av (minBases M (shift blk v (update (POSL.N M v) blk r))) blk) ∧
      piPairs blk (Av (minBases M v) blk) v ⊆
        piPairs blk (Av (minBases M v) blk) (shift blk v (update (POSL.N M v) blk r)) ∧
      piPairs blk (Av (minBases M v) blk) (shift blk v (update (POSL.N M v) blk r)) ≠
        piPairs blk (Av (minBases M v) blk) v :=
  ⟨av_subset_av_update hE hr (POSL.isAdmissible hE hM v),
    piPairs_subset hr (POSL.isAdmissible hE hM v), piPairs_ne hE hk hM hr hrk⟩

/-! ### Step 8: counting, and the stage map -/

/-- `k - r ≤ |S₀| ≤ k - 1`, by Lemma `lem:avoidable`(2) and `r_{M^v}(E) = k`. -/
theorem card_av_bounds (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : nu (minBases M v) blk = r) (hrk : r < k) :
    k ≤ #(Av (minBases M v) blk) + r ∧ #(Av (minBases M v) blk) < k := by
  have h := Exchange.card_av_add_nu (minBases M v) blk
  rw [hr] at h
  refine ⟨by omega, ((card_le_univ _).trans_eq (Fintype.card_fin k)).lt_of_ne fun heq => ?_⟩
  rw [eq_univ_of_card _ (heq.trans (Fintype.card_fin k).symm),
    show blockSet blk univ = univ by ext; simp, rk_univ _ (Conn.minBases_ground M v),
    rank_minBases hE, hk, card_univ, Fintype.card_fin] at h
  omega

/-- The stage-`r` update map `p ↦ p + a(p)`, where `a(p)` is the PO-SL update
(`update (POSL.N M v) blk r`, Definitions `def:posl` and `def:update`) at `v = w - p_blk`.  It is
the identity at a state with `ν₀ > r` (`stageMap_eq_self`), and `w - (p + a(p))_blk = v - a_blk`
(`shift_stageMap`). -/
noncomputable def stageMap (M : Matroid (Fin m)) (blk : Fin m → Fin k) (w : Fin m → ℝ) (r : ℕ)
    (p : Fin k → ℝ) : Fin k → ℝ :=
  p + update (POSL.N M (shift blk w p)) blk r

/-- The potential of Step 8 at a state `p` of stage `r`:
`Φ(p) = (|S₀| - (k - r)) (⌊m² / 4⌋ + 1) + |Π(v)|`, with `v = w - p_blk`, `S₀ = Av(M^v)` and `Π`
formed with `S₀`. -/
noncomputable def Phi (M : Matroid (Fin m)) (blk : Fin m → Fin k) (w : Fin m → ℝ) (r : ℕ)
    (p : Fin k → ℝ) : ℕ :=
  (#(Av (minBases M (shift blk w p)) blk) - (k - r)) * (m ^ 2 / 4 + 1) +
    #(piPairs blk (Av (minBases M (shift blk w p)) blk) (shift blk w p))

variable {w : Fin m → ℝ} {p : Fin k → ℝ}

theorem shift_stageMap :
    shift blk w (stageMap M blk w r p) =
      shift blk (shift blk w p) (update (POSL.N M (shift blk w p)) blk r) :=
  (shift_shift w p _).symm

/-- **An update at a state with `ν₀ > r` is the identity**, since then `τ = 0`. -/
theorem stageMap_eq_self (hE : M.E = Set.univ) (h : r < nu (minBases M (shift blk w p)) blk) :
    stageMap M blk w r p = p := by
  rw [stageMap, update_eq_zero (POSL.N_zero hE) h, add_zero]

theorem iterate_stageMap_eq_self (hE : M.E = Set.univ)
    (h : r < nu (minBases M (shift blk w p)) blk) (n : ℕ) : (stageMap M blk w r)^[n] p = p :=
  Function.iterate_fixed (stageMap_eq_self hE h) n

/-- `ν₀` does not decrease under the stage map (Theorem `thm:validity`(2)). -/
theorem nu_le_nu_stageMap (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B)
    (h : r ≤ nu (minBases M (shift blk w p)) blk) :
    nu (minBases M (shift blk w p)) blk ≤
      nu (minBases M (shift blk w (stageMap M blk w r p))) blk := by
  rw [shift_stageMap]
  exact nu_le_nu_update hE h (POSL.isAdmissible hE hM _)

theorem le_nu_iterate (hE : M.E = Set.univ) (hM : ∃ B, IsRainbowBase M blk B)
    (h : r ≤ nu (minBases M (shift blk w p)) blk) (n : ℕ) :
    r ≤ nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (nu_le_nu_stageMap hE hM ih)

/-- `Φ(p) < r (⌊m² / 4⌋ + 1)` at a state of stage `r`: `|S₀| - (k - r) ≤ r - 1` and
`|Π| ≤ ⌊m² / 4⌋`. -/
theorem Phi_lt (hE : M.E = Set.univ) (hk : rank M = k)
    (hr : nu (minBases M (shift blk w p)) blk = r) (hrk : r < k) :
    Phi M blk w r p < r * (m ^ 2 / 4 + 1) := by
  obtain ⟨h1, h2⟩ := card_av_bounds hE hk hr hrk
  have h3 := card_piPairs_le blk (Av (minBases M (shift blk w p)) blk) (shift blk w p)
  have h4 : #(Av (minBases M (shift blk w p)) blk) - (k - r) + 1 ≤ r := by omega
  calc Phi M blk w r p ≤ (#(Av (minBases M (shift blk w p)) blk) - (k - r)) * (m ^ 2 / 4 + 1) +
        m ^ 2 / 4 := Nat.add_le_add_left h3 _
    _ < (#(Av (minBases M (shift blk w p)) blk) - (k - r) + 1) * (m ^ 2 / 4 + 1) := by
        rw [add_one_mul]; omega
    _ ≤ r * (m ^ 2 / 4 + 1) := Nat.mul_le_mul_right _ h4

/-- **Step 8.**  The potential grows at every update within stage `r`: if `ν₀ = r` before and
after the update, then `Φ(p) < Φ(p + a)`.  By Theorem `thm:potential`(1), `S₀` grows or stays;
if it grows, the first term of `Φ` gains at least `⌊m² / 4⌋ + 1 > |Π(v)|`; if it stays, `Π`
grows strictly (items 2 and 3). -/
theorem Phi_lt_Phi_stageMap (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hr : nu (minBases M (shift blk w p)) blk = r)
    (hrk : r < k) (hr' : nu (minBases M (shift blk w (stageMap M blk w r p))) blk = r) :
    Phi M blk w r p < Phi M blk w r (stageMap M blk w r p) := by
  obtain ⟨h1, h2, h3⟩ := potential hE hk hM hr hrk
  rw [shift_stageMap] at hr'
  have hsub := h1 hr'
  have hb := (card_av_bounds hE hk hr hrk).1
  rw [Phi, Phi, shift_stageMap]
  rcases hsub.eq_or_ssubset with heq | hss
  · rw [← heq]
    exact Nat.add_lt_add_left (card_lt_card (h2.ssubset_of_ne h3.symm)) _
  · have hc := card_lt_card hss
    have hP := card_piPairs_le blk (Av (minBases M (shift blk w p)) blk) (shift blk w p)
    have hm : (#(Av (minBases M (shift blk w p)) blk) - (k - r) + 1) * (m ^ 2 / 4 + 1) ≤
        (#(Av (minBases M (shift blk (shift blk w p)
          (update (POSL.N M (shift blk w p)) blk r))) blk) - (k - r)) * (m ^ 2 / 4 + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [add_one_mul] at hm
    omega

/-- Within stage `r`, the `n`-th iterate of a state of stage `r` has potential at least `n`. -/
theorem le_Phi_iterate (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k)
    (hp : r ≤ nu (minBases M (shift blk w p)) blk) (n : ℕ)
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) :
    n ≤ Phi M blk w r ((stageMap M blk w r)^[n] p) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn ⊢
    have hn' : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r :=
      le_antisymm ((nu_le_nu_stageMap hE hM (le_nu_iterate hE hM hp n)).trans_eq hn)
        (le_nu_iterate hE hM hp n)
    exact (ih hn').trans_lt (Phi_lt_Phi_stageMap hE hk hM hn' hrk hn)

/-- **Theorem `thm:potential`, the stage bound**, counting form: from a state with `ν₀ ≥ r`, at
most `r (⌊m² / 4⌋ + 1)` iterates of the stage-`r` map have `ν₀ = r`, namely those with
`n < r (⌊m² / 4⌋ + 1)`; so at most `r (⌊m² / 4⌋ + 1)` updates are applied at states of
stage `r`. -/
theorem lt_of_nu_iterate_eq (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k)
    (hp : r ≤ nu (minBases M (shift blk w p)) blk) {n : ℕ}
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) :
    n < r * (m ^ 2 / 4 + 1) :=
  (le_Phi_iterate hE hk hM hrk hp n hn).trans_lt (Phi_lt hE hk hn hrk)

/-- **Theorem `thm:potential`, the stage bound.**  Let `M` have ground set `E`, rank `k` and a
rainbow base, and let `r < k`.  From any `p` with `ν₀(p) = ν(M^{w - p_blk}) ≥ r`, after
`r (⌊m² / 4⌋ + 1)` iterations of the stage-`r` update map `p ↦ p + a(p)` (`stageMap`),
`ν₀ ≥ r + 1`: stage `r` ends after at most `r (⌊m² / 4⌋ + 1)` updates.  An update at a state with
`ν₀ > r` is the identity (`stageMap_eq_self`). -/
theorem stage_bound (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hrk : r < k) (hp : r ≤ nu (minBases M (shift blk w p)) blk) :
    r + 1 ≤ nu (minBases M (shift blk w ((stageMap M blk w r)^[r * (m ^ 2 / 4 + 1)] p))) blk :=
  Nat.succ_le_of_lt <| lt_of_le_of_ne (le_nu_iterate hE hM hp _) fun h =>
    (lt_of_nu_iterate_eq hE hk hM hrk hp h.symm).false

/-- The stage bound for every number `n ≥ r (⌊m² / 4⌋ + 1)` of iterations: the later updates of
the stage are the identity. -/
theorem stage_bound_of_le (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hrk : r < k) (hp : r ≤ nu (minBases M (shift blk w p)) blk)
    {n : ℕ} (hn : r * (m ^ 2 / 4 + 1) ≤ n) :
    r + 1 ≤ nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm _ j, Function.iterate_add_apply,
    iterate_stageMap_eq_self hE (Nat.lt_of_succ_le (stage_bound hE hk hM hrk hp))]
  exact stage_bound hE hk hM hrk hp

end SignedTropical.Rainbow.Potential
