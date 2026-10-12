import SignedTropical.Rainbow.Update
import SignedTropical.Rainbow.Exchange
import SignedTropical.Rainbow.PossiblyOptimal

/-!
# Validity of the update

`greedy_intersection.tex`, Section 4.4, Theorem `thm:validity`.  `M : Matroid (Fin m)` has
ground set `univ`, the blocks are the fibres of `blk : Fin m → Fin k`, `v = w - p_blk`,
`ν₀ = ν(M^v) = r`, `N` is an admissible family and `a = update N blk r` its update
(`Rainbow/Update.lean`).  The paper's further hypotheses `rank M = k` and `r < k` are not used.

* `validity` (Theorem `thm:validity`): `Ψ(p + a) = Ψ(p) + (k - r) τ`; every base of `M^v`
  meeting `r` blocks is a minimum base of `v - a_blk`; `ν₀` does not decrease.  The three parts
  are `psi_update`, `isMinBase_update` and `nu_le_nu_update` (the last one for every `r ≤ ν₀`).

The proof follows the paper.  Along the path `a(s)_b = (s - λ_b)₊`, `s ∈ [0, τ]` (`path`), with
`v(s) = v - a(s)_blk`:

* `sandwich` (Step 3): for `0 ≤ s < τ` and `X = E_{Av(N(s))}`, every base of `N(s)`, in
  particular every minimum base of `v(s)` (Lemma `lem:path` and (F3)), has at most
  `r_{N(s)}(X) = |Av(N(s))| - (k - r)` elements in `X` (Lemma `lem:avoidable`(2)), and an old
  base `B*` of `M^v` meeting `r` blocks attains this bound (Step 4);
* `isMinBase_path` (Steps 1, 2 and 5): `B*` is a minimum base of `v(s)` for every `s ∈ [0, τ]`.
  The paper integrates the right derivative of `φ(s) = Ψ(p + a(s))`; here the same right
  derivative bound enters as a real induction (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`):
  the set of such `s` is closed, contains `0`, and extends to the right of each of its points
  `s < τ`, because to the right of `s` the path moves `v(s)` by `-h 1_X` and `B*` has the most
  elements in `X` among the minimum bases of `v(s)`;
* `update_eq_zero_of_mem_of_mem`: a block met twice by `B*` has `λ_b ≥ τ` (the sandwich with
  equality), so that `Ψ(p + a) - Ψ(p) = Σ_b a_b - Σ_{e ∈ B*} a_{blk e} = (k - r) τ`.
-/

open Finset Filter Topology
open scoped ENNReal

namespace SignedTropical.Rainbow.Validity

open SignedTropical.Rainbow

variable {m k : ℕ} {M : Matroid (Fin m)} {blk : Fin m → Fin k} {v : Fin m → ℝ}
  {N : ℝ → Matroid (Fin m)} {r : ℕ} {B₀ : Finset (Fin m)}

/-- `(w - p_blk) - q_blk = w - (p + q)_blk`. -/
theorem shift_shift (w : Fin m → ℝ) (p q : Fin k → ℝ) :
    shift blk (shift blk w p) q = shift blk w (p + q) := by
  ext e
  simp only [shift, Pi.add_apply]
  ring

/-! ### The path -/

/-- The path `a(s)_b = (s - λ_b)₊` of the proof, computed in `[0, ∞]`; `a(τ) = a`
(`path_tau`). -/
noncomputable def path (N : ℝ → Matroid (Fin m)) (blk : Fin m → Fin k) (r : ℕ) (s : ℝ)
    (b : Fin k) : ℝ :=
  (ENNReal.ofReal s - lam N blk r b).toReal

theorem path_tau : path N blk r (tau N blk r) = update N blk r := rfl

theorem path_zero : path N blk r 0 = 0 := by
  ext b
  simp [path]

/-- `a(s) ∈ [0, s]^k`. -/
theorem path_mem {s : ℝ} (hs : 0 ≤ s) (b : Fin k) :
    0 ≤ path N blk r s b ∧ path N blk r s b ≤ s :=
  ⟨ENNReal.toReal_nonneg,
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top tsub_le_self).trans_eq (ENNReal.toReal_ofReal hs)⟩

theorem continuous_path (b : Fin k) : Continuous fun s => path N blk r s b := by
  by_cases htop : lam N blk r b = ⊤
  · simp only [path, htop, ENNReal.sub_top, ENNReal.toReal_zero]
    exact continuous_const
  obtain ⟨l, hl0, hl⟩ : ∃ l, 0 ≤ l ∧ lam N blk r b = ENNReal.ofReal l :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
  have h : (fun s => path N blk r s b) = fun s => max (s - l) 0 := by
    ext s
    rw [path, hl, ← ENNReal.ofReal_sub _ hl0, ENNReal.toReal_ofReal']
  rw [h]
  exact (continuous_id.sub continuous_const).max continuous_const

/-- To the right of `x ≥ 0`, the path moves with velocity `1` on the blocks with `λ_b ≤ x` and
stays put on the others (Step 2). -/
theorem eventually_path_eq {x : ℝ} (hx : 0 ≤ x) :
    ∀ᶠ y in 𝓝[>] x, ∀ b, path N blk r y b =
      path N blk r x b + if lam N blk r b ≤ ENNReal.ofReal x then y - x else 0 := by
  refine eventually_all.2 fun b => ?_
  by_cases hb : lam N blk r b ≤ ENNReal.ofReal x
  · filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    rw [if_pos hb, path, path,
      ENNReal.toReal_sub_of_le (hb.trans (ENNReal.ofReal_le_ofReal hy.le)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_sub_of_le hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (hx.trans hy.le),
      ENNReal.toReal_ofReal hx]
    ring
  · rw [not_le] at hb
    filter_upwards [nhdsWithin_le_nhds
      ((ENNReal.continuous_ofReal.tendsto x).eventually (eventually_lt_nhds hb))] with y hy
    rw [if_neg (not_le.2 hb), add_zero, path, path, tsub_eq_zero_of_le hy.le,
      tsub_eq_zero_of_le hb.le]

/-! ### The sandwich -/

/-- **Steps 3 and 4 of the proof, the sandwich.**  Let `B₀` be a base of `M^v` meeting `r`
blocks, `0 ≤ s < τ` and `X = E_{Av(N(s))}`.  Every base `B` of `N(s)` has
`|B ∩ X| ≤ r_{N(s)}(X) = |Av(N(s))| - (k - r) ≤ |B₀ ∩ X|`, so `B₀` attains the bound and meets
every block of `Av(N(s))` at most once. -/
theorem sandwich (hr : nu (minBases M v) blk = r) (hN : IsAdmissible M blk v N)
    (hB₀ : (minBases M v).IsBase ↑B₀) (hB₀r : #(blocksMet blk B₀) = r) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < tau N blk r) :
    (∀ B : Finset (Fin m), (N s).IsBase ↑B →
      #(B ∩ blockSet blk (Av (N s) blk)) ≤ #(B₀ ∩ blockSet blk (Av (N s) blk))) ∧
      Set.InjOn blk ↑(B₀ ∩ blockSet blk (Av (N s) blk)) := by
  set S := Av (N s) blk
  set X := blockSet blk S
  have hν : nu (N s) blk = r := nu_eq_of_lt_tau hr.ge hN hs0 hs
  have hrk : r ≤ k := hν ▸ nu_le (N s) blk
  have h1 : #S + nu (N s) blk = k + rk (N s) X := Exchange.card_av_add_nu (N s) blk
  rw [hν] at h1
  have hX (B : Finset (Fin m)) (hB : (N s).IsBase ↑B) : #(B ∩ X) ≤ rk (N s) X :=
    card_le_rk (N s) (hB.indep.subset (coe_subset.2 inter_subset_left)) inter_subset_right
  have h2 := hX B₀ (hN.F2 0 s le_rfl hs0 B₀ (hN.F1 ▸ hB₀))
  -- `B₀` meets all blocks of `S` but at most `k - r`
  have hsub : S ∩ blocksMet blk B₀ ⊆ blocksMet blk (B₀ ∩ X) := fun b hb => by
    obtain ⟨e, he, rfl⟩ := mem_blocksMet.1 (mem_inter.1 hb).2
    exact mem_blocksMet.2 ⟨e, mem_inter.2 ⟨he, mem_blockSet.2 (mem_inter.1 hb).1⟩, rfl⟩
  have h3 := card_le_card hsub
  have h4 := card_le_card (sdiff_subset_sdiff (subset_univ S) (subset_refl (blocksMet blk B₀)))
  rw [card_univ_sdiff, hB₀r, Fintype.card_fin] at h4
  have h5 := card_sdiff_add_card_inter S (blocksMet blk B₀)
  have h6 : #(blocksMet blk (B₀ ∩ X)) ≤ #(B₀ ∩ X) := card_image_le
  refine ⟨fun B hB => by have := hX B hB; omega, card_image_iff.1 ?_⟩
  change #(blocksMet blk (B₀ ∩ X)) = #(B₀ ∩ X)
  omega

/-! ### The old base stays minimum along the path -/

/-- **Steps 1, 2 and 5 of the proof.**  A base `B₀` of `M^v` meeting `r` blocks is a minimum
base of `v(s) = v - a(s)_blk` for every `s ∈ [0, τ]`. -/
theorem isMinBase_path (hE : M.E = Set.univ) (hr : nu (minBases M v) blk = r)
    (hN : IsAdmissible M blk v N) (hB₀ : (minBases M v).IsBase ↑B₀)
    (hB₀r : #(blocksMet blk B₀) = r) {s : ℝ} (hs : s ∈ Set.Icc 0 (tau N blk r)) :
    IsMinBase M (shift blk v (path N blk r s)) B₀ := by
  have hB₀M : M.IsBase (B₀ : Set (Fin m)) := isBase_of_isBase_minBases hE hB₀
  -- the weight of a base along the path
  set f : Finset (Fin m) → ℝ → ℝ := fun B s => ∑ e ∈ B, shift blk v (path N blk r s) e
  have hfc (B : Finset (Fin m)) : Continuous (f B) :=
    continuous_finsetSum _ fun e _ => continuous_const.sub (continuous_path (blk e))
  have hT : {s | IsMinBase M (shift blk v (path N blk r s)) B₀} =
      ⋂ (B : Finset (Fin m)) (_ : M.IsBase (B : Set (Fin m))), {s | f B₀ s ≤ f B s} := by
    ext s
    simp only [IsMinBase, hB₀M, true_and, Set.mem_setOf_eq, Set.mem_iInter, f]
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (s := {s | IsMinBase M
    (shift blk v (path N blk r s)) B₀}) ?_ ?_ ?_ hs
  · rw [hT]
    exact (isClosed_iInter fun B => isClosed_iInter fun _ => isClosed_le (hfc B₀) (hfc B)).inter
      isClosed_Icc
  · have h0 : shift blk v (path N blk r 0) = v := by
      ext e
      simp [shift, path_zero]
    rw [Set.mem_setOf_eq, h0]
    exact (isBase_minBases_iff hE).1 hB₀
  rintro x ⟨hxT, hx0, hxτ⟩
  rw [Set.mem_setOf_eq] at hxT
  set X := blockSet blk (Av (N x) blk)
  have hsand := (sandwich hr hN hB₀ hB₀r hx0 hxτ).1
  -- to the right of `x`, `v(y) = v(x) - (y - x) 1_X`
  have hlin : ∀ᶠ y in 𝓝[>] x, ∀ B : Finset (Fin m), f B y = f B x - (y - x) * #(B ∩ X) := by
    filter_upwards [eventually_path_eq (N := N) (blk := blk) (r := r) hx0] with y hy B
    have hsplit (e : Fin m) : shift blk v (path N blk r y) e =
        shift blk v (path N blk r x) e - if e ∈ X then y - x else 0 := by
      have hX : (lam N blk r (blk e) ≤ ENNReal.ofReal x) ↔ e ∈ X := by
        rw [mem_blockSet, mem_Av_iff_lam_le hr.ge hN hx0 hxτ]
      simp only [shift, hy, hX]
      ring
    simp only [f, hsplit, sum_sub_distrib, sum_ite_mem, sum_const, nsmul_eq_mul]
    ring
  have key (B : Finset (Fin m)) : ∀ᶠ y in 𝓝[>] x, M.IsBase (B : Set (Fin m)) → f B₀ y ≤ f B y := by
    by_cases hB : M.IsBase (B : Set (Fin m))
    · rcases (hxT.2 B hB).lt_or_eq with hlt | heq
      · exact (((hfc B₀).continuousAt.eventually_lt (hfc B).continuousAt hlt).filter_mono
          nhdsWithin_le_nhds).mono fun y hy _ => hy.le
      -- `B` is a minimum base of `v(x)`, hence a base of `N(x)`: the sandwich applies
      have hBmin : IsMinBase M (shift blk v (path N blk r x)) B :=
        ⟨hB, fun B' hB' => heq.ge.trans (hxT.2 B' hB')⟩
      have hc : (#(B ∩ X) : ℝ) ≤ #(B₀ ∩ X) := by
        exact_mod_cast hsand B (hN.F3 x hx0 B
          (Pos.mem_pos_of_isMinBase_shift hx0 (path_mem hx0) hBmin))
      filter_upwards [hlin, self_mem_nhdsWithin] with y hy (hxy : x < y) _
      have heq' : f B₀ x = f B x := heq
      rw [hy B₀, hy B, heq']
      nlinarith
    · exact Eventually.of_forall fun _ h => absurd h hB
  filter_upwards [eventually_all.2 key] with y hy
  exact ⟨hB₀M, hy⟩

/-! ### Theorem `thm:validity` -/

/-- **Theorem `thm:validity`(2).**  Every base of `M^v` meeting `r` blocks is a minimum base of
`v - a_blk`. -/
theorem isMinBase_update (hE : M.E = Set.univ) (hr : nu (minBases M v) blk = r)
    (hN : IsAdmissible M blk v N) (hB₀ : (minBases M v).IsBase ↑B₀)
    (hB₀r : #(blocksMet blk B₀) = r) : IsMinBase M (shift blk v (update N blk r)) B₀ :=
  isMinBase_path hE hr hN hB₀ hB₀r ⟨tau_nonneg, le_rfl⟩

/-- **Theorem `thm:validity`(2), last clause.**  `ν₀` does not decrease:
`ν(M^v) ≤ ν(M^{v - a_blk})`.  Stated for `r ≤ ν₀`: if `ν₀ > r`, then `a = 0`. -/
theorem nu_le_nu_update (hE : M.E = Set.univ) (hr : r ≤ nu (minBases M v) blk)
    (hN : IsAdmissible M blk v N) :
    nu (minBases M v) blk ≤ nu (minBases M (shift blk v (update N blk r))) blk := by
  obtain hr | hr := hr.lt_or_eq
  · rw [update_eq_zero hN.F1 hr, show shift blk v 0 = v from funext fun e => sub_zero (v e)]
  obtain ⟨I, hI, hcard⟩ := exists_isRainbowIndep_card_eq_nu (minBases M v) blk
  obtain ⟨B₀, hB₀, hIB, hBI⟩ := exists_isBase_of_isRainbowIndep hI hcard
  have hB₀r : #(blocksMet blk B₀) = r := by rw [hBI, hI.2.card_blocksMet, hcard, hr]
  have hB := (isBase_minBases_iff hE).2 (isMinBase_update hE hr.symm hN hB₀ hB₀r)
  exact hcard ▸ IsRainbowIndep.card_le_nu ⟨hB.indep.subset (coe_subset.2 hIB), hI.2⟩

/-- A block met twice by a base `B₀` of `M^v` meeting `r` blocks has `λ_b ≥ τ`, so `a_b = 0`:
otherwise it would be avoidable at `λ_b < τ`, against the sandwich. -/
theorem update_eq_zero_of_mem_of_mem (hr : nu (minBases M v) blk = r)
    (hN : IsAdmissible M blk v N) (hB₀ : (minBases M v).IsBase ↑B₀)
    (hB₀r : #(blocksMet blk B₀) = r) {e₁ e₂ : Fin m} (h₁ : e₁ ∈ B₀) (h₂ : e₂ ∈ B₀)
    (hne : e₁ ≠ e₂) (hblk : blk e₁ = blk e₂) : update N blk r (blk e₁) = 0 := by
  by_contra h0
  have hlt : lam N blk r (blk e₁) < ENNReal.ofReal (tau N blk r) := not_le.1 fun hge =>
    h0 (by rw [update, tsub_eq_zero_of_le hge, ENNReal.toReal_zero])
  obtain ⟨l, hl0, hl⟩ : ∃ l, 0 ≤ l ∧ lam N blk r (blk e₁) = ENNReal.ofReal l :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (hlt.trans ENNReal.ofReal_lt_top).ne).symm⟩
  have hlτ : l < tau N blk r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hl0).1 (hl ▸ hlt)
  have hmem : blk e₁ ∈ Av (N l) blk := (mem_Av_iff_lam_le hr.ge hN hl0 hlτ).2 hl.le
  exact hne ((sandwich hr hN hB₀ hB₀r hl0 hlτ).2
    (mem_coe.2 (mem_inter.2 ⟨h₁, mem_blockSet.2 hmem⟩))
    (mem_coe.2 (mem_inter.2 ⟨h₂, mem_blockSet.2 (hblk ▸ hmem)⟩)) hblk)

/-- **Theorem `thm:validity`(1).**  `Ψ(p + a) = Ψ(p) + (k - r) τ`. -/
theorem psi_update {w : Fin m → ℝ} {p : Fin k → ℝ} (hE : M.E = Set.univ)
    (hr : nu (minBases M (shift blk w p)) blk = r) (hN : IsAdmissible M blk (shift blk w p) N) :
    Psi M blk w (p + update N blk r) = Psi M blk w p + (k - r) * tau N blk r := by
  obtain ⟨B₀, hB₀, hB₀r⟩ := exists_isBase_card_blocksMet (minBases M (shift blk w p)) blk
  rw [hr] at hB₀r
  have hrk : r ≤ k := hB₀r ▸ (card_le_univ _).trans_eq (Fintype.card_fin k)
  have hmin := isMinBase_update hE hr hN hB₀ hB₀r
  have hmin0 := (isBase_minBases_iff hE).1 hB₀
  -- `Σ_{e ∈ B₀} a_{blk e}` is the sum of `a` over the blocks met by `B₀`
  have hU : ∑ e ∈ B₀, update N blk r (blk e) = ∑ b ∈ blocksMet blk B₀, update N blk r b := by
    rw [sum_comp]
    refine sum_congr rfl fun b hb => ?_
    obtain ⟨e, he, rfl⟩ := mem_image.1 hb
    by_cases h1 : #{e' ∈ B₀ | blk e' = blk e} ≤ 1
    · rw [le_antisymm h1 (card_pos.2 ⟨e, mem_filter.2 ⟨he, rfl⟩⟩), one_smul]
    · obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := one_lt_card.1 (not_le.1 h1)
      rw [mem_filter] at he₁ he₂
      have h0 := update_eq_zero_of_mem_of_mem hr hN hB₀ hB₀r he₁.1 he₂.1 hne
        (he₁.2.trans he₂.2.symm)
      rw [he₁.2] at h0
      rw [h0, smul_zero]
  -- each block missed by `B₀` is avoidable in `M^v` and receives `τ`
  have hZ : ∑ b ∈ univ \ blocksMet blk B₀, update N blk r b = (k - r) * tau N blk r := by
    rw [sum_congr rfl fun b hb => update_eq_tau hr hN ((mem_Av_iff_baseMisses hr).2
      ⟨B₀, hB₀, hB₀r, (mem_sdiff.1 hb).2⟩), sum_const, card_univ_sdiff, hB₀r, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub hrk]
  have hsum := sum_sdiff (f := update N blk r) (subset_univ (blocksMet blk B₀))
  rw [Psi, Psi, ← shift_shift, ← hmin.sum_eq, ← hmin0.sum_eq]
  simp only [Pi.add_apply, sum_add_distrib, shift, sum_sub_distrib]
  linarith

/-- **Theorem `thm:validity`.**  Let `M` have ground set `E`, `v = w - p_blk`, `ν₀ = ν(M^v) = r`,
`N` an admissible family and `a` its update.  Then
1. `Ψ(p + a) = Ψ(p) + (k - r) τ`;
2. every base of `M^v` meeting `r` blocks is a minimum base of `v - a_blk`; in particular
   `ν₀` does not decrease: `ν(M^{w - (p + a)_blk}) ≥ ν₀`.

The paper also assumes that `M` has rank `k` and `r < k`; the proof does not use them (they
make `τ` a minimum, `isLeast_tau`). -/
theorem validity {w : Fin m → ℝ} {p : Fin k → ℝ} (hE : M.E = Set.univ)
    (hr : nu (minBases M (shift blk w p)) blk = r) (hN : IsAdmissible M blk (shift blk w p) N) :
    Psi M blk w (p + update N blk r) = Psi M blk w p + (k - r) * tau N blk r ∧
      (∀ B : Finset (Fin m), (minBases M (shift blk w p)).IsBase ↑B →
        #(blocksMet blk B) = r → IsMinBase M (shift blk (shift blk w p) (update N blk r)) B) ∧
      nu (minBases M (shift blk w p)) blk ≤
        nu (minBases M (shift blk w (p + update N blk r))) blk :=
  ⟨psi_update hE hr hN, fun _ hB hBr => isMinBase_update hE hr hN hB hBr,
    shift_shift w p (update N blk r) ▸ nu_le_nu_update hE hr.ge hN⟩

end SignedTropical.Rainbow.Validity
