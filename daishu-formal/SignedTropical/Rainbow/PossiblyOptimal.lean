import SignedTropical.Rainbow.MinBases

/-!
# Possibly optimal bases

`greedy_intersection.tex`, Section 4.2: Proposition `prop:pos`, the remark after it, and
Lemma `lem:path`, for `θ` and `P_t` of Definition `def:theta` (`theta`, `Pos` in
`Rainbow/Defs.lean`).  Throughout, `M : Matroid (Fin m)` has ground set `univ`.

* `theta_le_iff`: `θ(B) ≤ t` iff `0 ≤ t` and `v_f - v_e ≤ t` whenever `e ∉ B`, `f ∈ C(B, e)`.
* `tfae_pos` (Proposition `prop:pos`): for a base `B` and `t ≥ 0`, the five conditions
  (1) `θ(B) ≤ t`; (2) `B` is a minimum base of `v - t 1_B`; (3) `v(B) - v(B') ≤ t |B ∖ B'|`
  for every base `B'`; (4) `e ∈ cl(B ∩ {g : v_g ≤ v_e + t})` for every `e`; (5) `B` is a
  minimum base of some `u` with `|u_e - v_e| ≤ t/2` for every `e`; are equivalent.
* `pos_mono`, `mem_pos_zero`, `mem_pos_iff_isBase` (the remark after the proposition):
  `P_t` grows with `t`, `P_0 = Bases(M^v)`, and `P_t = Bases(M)` once `t ≥ max v - min v`.
* `mem_pos_of_isMinBase_shift` (Lemma `lem:path`): if `y ∈ [0,s]^k`, every minimum base of
  `v - y_blk` lies in `P_s`.

Every equivalence is read through Lemma `lem:minbases`(1) (`Conn.isMinBase_iff_fundCircuit`).
-/

open Finset

namespace SignedTropical.Rainbow.Pos

open SignedTropical.Rainbow

variable {m k : ℕ} {M : Matroid (Fin m)} {v : Fin m → ℝ} {B : Finset (Fin m)} {t : ℝ}

/-- The weight `v - t 1_B`. -/
def tilt (v : Fin m → ℝ) (t : ℝ) (B : Finset (Fin m)) : Fin m → ℝ :=
  fun e => v e - if e ∈ B then t else 0

theorem tilt_zero : tilt v 0 B = v := by
  ext e
  simp [tilt]

/-- `(v - t 1_B)(S) = v(S) - t |S ∩ B|`. -/
theorem sum_tilt (S : Finset (Fin m)) :
    ∑ e ∈ S, tilt v t B e = ∑ e ∈ S, v e - t * #(S ∩ B) := by
  simp only [tilt, sum_sub_distrib, sum_ite_mem, sum_const, nsmul_eq_mul, mul_comm]

/-- `θ(B) ≤ t` iff `0 ≤ t` and every single exchange gains at most `t`. -/
theorem theta_le_iff : theta M v B ≤ t ↔
    0 ≤ t ∧ ∀ e ∉ B, ∀ f ∈ M.fundCircuit e (B : Set (Fin m)), v f - v e ≤ t := by
  unfold theta
  rw [fold_max_le]
  simp only [mem_filter, mem_product, mem_univ, true_and, and_imp, Prod.forall]
  exact and_congr_right fun _ =>
    ⟨fun h e he f hf => h e f he hf, fun h e f he hf => h e he f hf⟩

theorem theta_nonneg : 0 ≤ theta M v B :=
  (theta_le_iff.1 le_rfl).1

/-- An element of `C(B, e)` other than `e` lies in `B`. -/
theorem mem_of_mem_fundCircuit {e f : Fin m} (hf : f ∈ M.fundCircuit e (B : Set (Fin m)))
    (hfe : f ≠ e) : f ∈ B := by
  simpa [hfe] using M.fundCircuit_subset_insert e ↑B hf

/-- Items (1) and (2) of Proposition `prop:pos`. -/
theorem theta_le_iff_isMinBase (hB : M.IsBase (B : Set (Fin m))) (ht : 0 ≤ t) :
    theta M v B ≤ t ↔ IsMinBase M (tilt v t B) B := by
  rw [theta_le_iff, Conn.isMinBase_iff_fundCircuit, and_iff_right ht, and_iff_right hB]
  refine forall₂_congr fun e he => forall₂_congr fun f hf => ?_
  obtain rfl | hfe := eq_or_ne f e
  · simp [ht]
  · simp only [tilt, mem_of_mem_fundCircuit hf hfe, he, if_true, if_false, sub_zero]
    constructor <;> intro h <;> linarith

/-- **Proposition `prop:pos`.**  For a base `B` and `t ≥ 0` the following are equivalent:
(1) `θ(B) ≤ t`; (2) `B` is a minimum base for `v - t 1_B`; (3) `v(B) - v(B') ≤ t |B ∖ B'|`
for every base `B'`; (4) `e ∈ cl(B ∩ {g : v_g ≤ v_e + t})` for every `e ∈ E`; (5) `B` is a
minimum base for some `u` with `‖u - v‖_∞ ≤ t/2`. -/
theorem tfae_pos (hE : M.E = Set.univ) (hB : M.IsBase (B : Set (Fin m))) (ht : 0 ≤ t) :
    List.TFAE [theta M v B ≤ t,
      IsMinBase M (tilt v t B) B,
      ∀ B' : Finset (Fin m), M.IsBase (B' : Set (Fin m)) →
        ∑ e ∈ B, v e - ∑ e ∈ B', v e ≤ t * #(B \ B'),
      ∀ e, e ∈ M.closure (↑B ∩ {g | v g ≤ v e + t}),
      ∃ u : Fin m → ℝ, (∀ e, |u e - v e| ≤ t / 2) ∧ IsMinBase M u B] := by
  tfae_have 1 ↔ 2 := theta_le_iff_isMinBase hB ht
  tfae_have 2 → 3 := fun h B' hB' => by
    have h' := h.2 B' hB'
    rw [sum_tilt, sum_tilt, inter_self] at h'
    have hc : #(B \ B') + #(B' ∩ B) = #B := by rw [inter_comm]; exact card_sdiff_add_card_inter B B'
    have hc' : (#(B \ B') : ℝ) + #(B' ∩ B) = #B := by exact_mod_cast hc
    nlinarith
  tfae_have 3 → 1 := fun h => theta_le_iff.2 ⟨ht, fun e he f hf => by
    obtain rfl | hfe := eq_or_ne f e
    · simpa using ht
    have hfB := mem_of_mem_fundCircuit hf hfe
    have h' := h _ ((isBase_exchange_iff hE hB he hfB).2 hf)
    have hd : B \ insert e (B.erase f) = {f} := by
      ext x
      by_cases hx : x = f <;> by_cases hxe : x = e <;> simp_all
    rw [sum_exchange he hfB, hd, card_singleton, Nat.cast_one, mul_one] at h'
    linarith⟩
  tfae_have 2 ↔ 4 := by
    have key : ∀ e, e ∈ M.closure (↑B ∩ {x | tilt v t B x ≤ tilt v t B e}) ↔
        e ∈ M.closure (↑B ∩ {g | v g ≤ v e + t}) := by
      intro e
      by_cases he : e ∈ B
      · have hmem : ∀ X : Set (Fin m), e ∈ X → e ∈ M.closure (↑B ∩ X) := fun X hX =>
          M.mem_closure_of_mem' ⟨mem_coe.2 he, hX⟩ (by rw [hE]; trivial)
        exact iff_of_true (hmem _ (by show tilt v t B e ≤ tilt v t B e; exact le_rfl))
          (hmem _ (by show v e ≤ v e + t; linarith))
      · have hset : (↑B ∩ {x | tilt v t B x ≤ tilt v t B e} : Set (Fin m)) =
            ↑B ∩ {g | v g ≤ v e + t} := by
          ext x
          simp only [Set.mem_inter_iff, mem_coe, Set.mem_setOf_eq, tilt, he, if_false, sub_zero]
          refine and_congr_right fun hx => ?_
          simp only [hx, if_true]
          constructor <;> intro h <;> linarith
        rw [hset]
    exact ⟨fun h e => (key e).1 (h.mem_closure hE e),
      fun h => isMinBase_of_forall_mem_closure hB fun e => (key e).2 (h e)⟩
  tfae_have 2 → 5 := fun h => ⟨fun e => tilt v t B e + t / 2, fun e => by
      rw [abs_le]
      by_cases he : e ∈ B <;> simp only [tilt, he, if_true, if_false] <;>
        constructor <;> linarith,
    (Conn.isMinBase_congr fun e f _ => by simp only [add_le_add_iff_right]).1 h⟩
  tfae_have 5 → 1 := fun ⟨u, hu, h⟩ => theta_le_iff.2 ⟨ht, fun e he f hf => by
    have hfe := Conn.le_of_mem_fundCircuit h he hf
    have h1 := (abs_le.1 (hu f)).1
    have h2 := (abs_le.1 (hu e)).2
    linarith⟩
  tfae_finish

/-- `P_t` grows with `t`. -/
theorem pos_mono {t t' : ℝ} (h : t ≤ t') : Pos M v t ⊆ Pos M v t' :=
  fun _ hB => ⟨hB.1, hB.2.trans h⟩

/-- `P_0 = Bases(M^v)`. -/
theorem mem_pos_zero (hE : M.E = Set.univ) : B ∈ Pos M v 0 ↔ (minBases M v).IsBase ↑B := by
  rw [isBase_minBases_iff hE]
  refine ⟨fun hB => ?_, fun h => ⟨h.1, ?_⟩⟩
  · simpa [tilt_zero] using (theta_le_iff_isMinBase hB.1 le_rfl).1 hB.2
  · exact (theta_le_iff_isMinBase h.1 le_rfl).2 (by simpa [tilt_zero] using h)

/-- `P_t = Bases(M)` once `t ≥ max v - min v`, that is `v_f - v_e ≤ t` for all `e, f`. -/
theorem mem_pos_iff_isBase (ht : 0 ≤ t) (h : ∀ e f, v f - v e ≤ t) :
    B ∈ Pos M v t ↔ M.IsBase (B : Set (Fin m)) :=
  ⟨fun hB => hB.1, fun hB => ⟨hB, theta_le_iff.2 ⟨ht, fun e _ f _ => h e f⟩⟩⟩

/-- **Lemma `lem:path`.**  If `y ∈ [0,s]^k`, every minimum base of `v - y_blk` lies in `P_s`. -/
theorem mem_pos_of_isMinBase_shift {blk : Fin m → Fin k} {y : Fin k → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hy : ∀ b, 0 ≤ y b ∧ y b ≤ s) (hB : IsMinBase M (shift blk v y) B) : B ∈ Pos M v s :=
  ⟨hB.1, theta_le_iff.2 ⟨hs, fun e he f hf => by
    have h := Conn.le_of_mem_fundCircuit hB he hf
    simp only [shift] at h
    linarith [hy (blk f), hy (blk e)]⟩⟩

end SignedTropical.Rainbow.Pos
