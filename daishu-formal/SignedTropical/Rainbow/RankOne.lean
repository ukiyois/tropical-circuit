import SignedTropical.Rainbow.StageLength

/-!
# Components of rank one

`greedy_intersection.tex`, Corollary `cor:rankone`: if every connected component of `M` has rank
at most one, every PO-SL update of a stage ends an epoch, and stage `r` ends after at most `r`
updates.  The assignment problem is the case of a partition matroid with unit capacities.

* `circuit_encard_le_two`: if every component has rank at most one, every circuit has at most
  two elements: a circuit lies in one component, and `|C| = r(C) + 1 ≤ 2`.
* `isCircuit_pair`: if every circuit has at most two elements, two distinct elements of one
  component form a circuit.
* `av_ne_av`: an update at `ν₀ = r < k` after which `ν₀ = r` changes `S₀`.  The crossing pair
  `(x, z)` of Theorem `thm:stagelength`(1) (`StageLength.exists_crossing_pair`) is a circuit
  `{x, z}`.  If `x ∈ B`, then `x ∈ C(B, z)` and `v_x ≤ v_z`, against `v_z < v_x`; so `z ∈ B`,
  `z ∈ C(B, x)`, and `v'_x ≤ v'_z` makes `B - z + x` a minimum base at `v'` with one more element
  in `E_{S₀}` (`Potential.lt_of_mem_fundCircuit`).
* `lt_of_nu_iterate_eq`: `|S₀|` grows at every update of the stage and stays below `k`, so at
  most `r` iterates of the stage-`r` map have `ν₀ = r`.
-/

open Finset

namespace SignedTropical.Rainbow.RankOne

open SignedTropical.Rainbow SignedTropical.Rainbow.Validity SignedTropical.Rainbow.Potential

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {v : Fin m → ℝ} {r : ℕ}

/-- **Components of rank at most one have circuits of at most two elements**: a circuit `C`
through `e` lies in the component of `e` (`Conn.isCircuit_subset_comp`), so
`|C| = r(C) + 1 ≤ r(comp e) + 1 ≤ 2`. -/
theorem circuit_encard_le_two (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1) :
    ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2 := by
  intro C hC
  obtain ⟨e, he⟩ := hC.nonempty
  have h1 : M.eRk C ≤ M.eRk ↑(Conn.comp M e) := M.eRk_mono (Conn.isCircuit_subset_comp hC he)
  have h2 : M.eRk ↑(Conn.comp M e) ≤ 1 := by
    rw [← coe_rk]
    exact_mod_cast hcomp e
  rw [← hC.eRk_add_one_eq]
  calc M.eRk C + 1 ≤ 1 + 1 := add_le_add (h1.trans h2) le_rfl
    _ = 2 := by norm_num

/-- In a matroid whose circuits have at most two elements, two distinct elements of one
component form a circuit. -/
theorem isCircuit_pair (hpar : ∀ C : Set (Fin m), M.IsCircuit C → C.encard ≤ 2) {x z : Fin m}
    (hxz : x ≠ z) (h : connRel M x z) : M.IsCircuit {x, z} := by
  rcases h with h | ⟨C, hC, hx, hz⟩
  · exact absurd h hxz
  · have hsub : ({x, z} : Set (Fin m)) ⊆ C := by
      rintro e (rfl | rfl)
      · exact hx
      · exact hz
    rwa [(Set.toFinite _).eq_of_subset_of_encard_le hsub
      ((hpar C hC).trans_eq (Set.encard_pair hxz).symm)]

/-- **One update per epoch.**  If every component of `M` has rank at most one, an update at
`ν₀ = r < k` after which `ν₀ = r` changes `S₀`. -/
theorem av_ne_av (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1)
    (hr : nu (minBases M v) blk = r) (hrk : r < k)
    (hr' : nu (minBases M (shift blk v (update (POSL.N M v) blk r))) blk = r) :
    Av (minBases M (shift blk v (update (POSL.N M v) blk r))) blk ≠ Av (minBases M v) blk := by
  set v' := shift blk v (update (POSL.N M v) blk r)
  set S := Av (minBases M v) blk
  set X := blockSet blk S
  obtain ⟨B, hB, hBr⟩ := exists_isBase_card_blocksMet (minBases M v) blk
  rw [hr] at hBr
  have hBmin : IsMinBase M v B := (isBase_minBases_iff hE).1 hB
  have hBmin' : IsMinBase M v' B := isMinBase_update hE hr (POSL.isAdmissible hE hM v) hB hBr
  obtain ⟨x, z, hx, hz, hxz, hlt, hc, hcross⟩ :=
    StageLength.exists_crossing_pair hE hk hM hr hrk hB hBr
  have hC := isCircuit_pair (circuit_encard_le_two hcomp) (fun h => by subst h; exact hz hx) hc
  -- `x ∉ B`: otherwise `z ∉ B`, `x ∈ C(B, z)` and `v_x ≤ v_z`
  have hxB : x ∉ B := fun hxB => by
    have hzB : z ∉ B := fun hzB => hC.not_indep (hBmin.1.indep.subset (by
      rintro e (rfl | rfl)
      · exact mem_coe.2 hxB
      · exact mem_coe.2 hzB))
    have hxC : x ∈ M.fundCircuit z ↑B := by
      rw [← hC.eq_fundCircuit_of_subset hBmin.1.indep (by
        rintro e (rfl | rfl)
        · exact Set.mem_insert_of_mem _ (mem_coe.2 hxB)
        · exact Set.mem_insert _ _)]
      exact Set.mem_insert _ _
    exact absurd (Conn.le_of_mem_fundCircuit hBmin hzB hxC) (not_le.2 hlt)
  have hzB : z ∈ B := hxz.resolve_left hxB
  have hzC : z ∈ M.fundCircuit x ↑B := by
    rw [← hC.eq_fundCircuit_of_subset hBmin.1.indep (by
      rintro e (rfl | rfl)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (mem_coe.2 hzB))]
    exact Set.mem_insert_of_mem _ rfl
  intro hS
  -- `|B ∩ X| = r_{M^{v'}}(X)`, both being `|S₀| + r - k` (Lemma `lem:avoidable`(2))
  have h1 : #S + r = k + rk (minBases M v') X := by
    have := Exchange.card_av_add_nu (minBases M v') blk
    rw [hS, hr'] at this
    exact this
  have h2 : #(B ∩ X) = rk (minBases M v) X := StageLength.card_inter_eq_rk hr hB hBr
  have h3 : #S + r = k + rk (minBases M v) X := by
    have := Exchange.card_av_add_nu (minBases M v) blk
    rw [hr] at this
    exact this
  have hBX : #(B ∩ X) = rk (minBases M v') X := by omega
  exact (not_le.2 (lt_of_mem_fundCircuit hE hBmin' hBX hxB (mem_blockSet.2 hx)
    (fun h => hz (mem_blockSet.1 h)) hzC)) hcross

variable {w : Fin m → ℝ} {p : Fin k → ℝ}

/-- `|S₀|` grows at every update within stage `r` (Theorem `thm:potential`(1) and `av_ne_av`). -/
theorem card_av_lt (hE : M.E = Set.univ) (hk : rank M = k) (hM : ∃ B, IsRainbowBase M blk B)
    (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1)
    (hr : nu (minBases M (shift blk w p)) blk = r) (hrk : r < k)
    (hr' : nu (minBases M (shift blk w (stageMap M blk w r p))) blk = r) :
    #(Av (minBases M (shift blk w p)) blk) <
      #(Av (minBases M (shift blk w (stageMap M blk w r p))) blk) := by
  rw [shift_stageMap] at hr' ⊢
  exact card_lt_card ((av_subset_av_update hE hr (POSL.isAdmissible hE hM _) hr').ssubset_of_ne
    (av_ne_av hE hk hM hcomp hr hrk hr').symm)

/-- Within stage `r`, the `n`-th iterate of a state of stage `r` has `|S₀| + r - k ≥ n`. -/
theorem le_card_av_iterate (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1)
    (hrk : r < k) (hp : r ≤ nu (minBases M (shift blk w p)) blk) (n : ℕ)
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) :
    n ≤ #(Av (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk) + r - k := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn ⊢
    have hn' : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r :=
      le_antisymm ((nu_le_nu_stageMap hE hM (le_nu_iterate hE hM hp n)).trans_eq hn)
        (le_nu_iterate hE hM hp n)
    have h1 := card_av_lt hE hk hM hcomp hn' hrk hn
    have h2 := (card_av_bounds hE hk hn' hrk).1
    have h3 := ih hn'
    omega

/-- **Corollary `cor:rankone`**, counting form: if every component of `M` has rank at most one,
then from a state with `ν₀ ≥ r` the iterates of the stage-`r` map with `ν₀ = r` are those with
`n < r`: stage `r` ends after at most `r` updates. -/
theorem lt_of_nu_iterate_eq (hE : M.E = Set.univ) (hk : rank M = k)
    (hM : ∃ B, IsRainbowBase M blk B) (hcomp : ∀ e, rk M (Conn.comp M e) ≤ 1)
    (hrk : r < k) (hp : r ≤ nu (minBases M (shift blk w p)) blk) {n : ℕ}
    (hn : nu (minBases M (shift blk w ((stageMap M blk w r)^[n] p))) blk = r) : n < r := by
  have h1 := le_card_av_iterate hE hk hM hcomp hrk hp n hn
  obtain ⟨h2, h3⟩ := card_av_bounds hE hk hn hrk
  omega

end SignedTropical.Rainbow.RankOne
