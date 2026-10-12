import SignedTropical.SparsePaving
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Corollary `cor:count`: most matroids need large signed circuits

`greedy_intersection.tex`, Corollary `cor:count`: for all large `m`, most matroids `M` on `m`
labeled elements have no signed tropical circuit for `h_M` of size less than `2^{m/2}/m²`.

Matroids are Mathlib's `Matroid (Fin m)` with ground set `univ`; let `N(m)` be their number.
Let `A(m)` be the number of those `M` for which a signed tropical circuit of size less than
`2^{m/2}/m²` computes `h_M` on `{0,1}^m` (at the indicator vectors of all sets).

* **Explicit form** (`corollaryD_explicit`): for `m ≥ 128`, `2^{⌊2^m/m³⌋} A(m) ≤ N(m)`.
  Every size below `2^{m/2}/m²` is at most `S = ⌊2^{m/2}/m²⌋`, and `S² m⁴ ≤ 2^m`
  (`floor_sq_mul_le`).  By `corollaryD_count` (Theorem B and the counting of Boolean
  circuits), `A(m) ≤ codeCount m s L` with `s = 15S² + 40S ≤ 55·2^m/m⁴` and
  `L = ⌈log₂(m+1)⌉ ≤ m`, and `codeCount m s L ≤ 2^{m + (2m+2)s + mL}` (`codeCount_le`).  On
  the other side `N(m) ≥ 2^a` with `m(m+1)a ≥ 2^m` (`exists_two_pow_le_ncard_matroids`, from
  `SparsePaving.two_pow_ceil_le_ncard_matroids`), and `⌊2^m/m³⌋ + m + (2m+2)s + mL ≤ a`
  (`exponent_le`).
* **Corollary `cor:count`** (`corollaryD_tendsto`): `A(m)/N(m) → 0`.  The same holds for
  circuits that compute `h_M` at every `w ∈ ℝ^m` (`corollaryD_tendsto_of_forall`), and the
  fraction of matroids for which every signed tropical circuit computing `h_M` on `{0,1}^m` has
  size at least `2^{m/2}/m²` tends to `1` (`corollaryD_most`).
* **Corollary D without the hypothesis `hN`** (`corollaryD_unconditional`).
-/

open Finset Filter Topology

namespace SignedTropical.Asymptotic

open SparsePaving

variable {m : ℕ}

/-! ### Arithmetic -/

/-- `m⁸ ≤ 2^m` for `m ≥ 64`. -/
theorem pow_eight_le_two_pow (hm : 64 ≤ m) : m ^ 8 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : 64 ^ 8 * (n + 1) ^ 8 ≤ 64 ^ 8 * (2 * n ^ 8) :=
      calc 64 ^ 8 * (n + 1) ^ 8 = (64 * (n + 1)) ^ 8 := (mul_pow ..).symm
        _ ≤ (65 * n) ^ 8 := Nat.pow_le_pow_left (by omega) 8
        _ = 65 ^ 8 * n ^ 8 := mul_pow ..
        _ ≤ 64 ^ 8 * 2 * n ^ 8 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 64 ^ 8 * (2 * n ^ 8) := by ring
    calc (n + 1) ^ 8 ≤ 2 * n ^ 8 := Nat.le_of_mul_le_mul_left h (by norm_num)
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by ring

/-- `S = ⌊2^{m/2}/m²⌋` satisfies `S² m⁴ ≤ 2^m`. -/
theorem floor_sq_mul_le (m : ℕ) : ⌊(2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2⌋₊ ^ 2 * m ^ 4 ≤ 2 ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hx : (0 : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2 := by positivity
  have hsq : ((2 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 = 2 ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    norm_num
  have : ((⌊(2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2⌋₊ ^ 2 * m ^ 4 : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    push_cast
    calc (⌊(2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2⌋₊ : ℝ) ^ 2 * (m : ℝ) ^ 4
        = ((⌊(2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2⌋₊ : ℝ) * m ^ 2) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2 * m ^ 2) ^ 2 := by gcongr; exact Nat.floor_le hx
      _ = 2 ^ m := by rw [div_mul_cancel₀ _ (by positivity), hsq]
  exact_mod_cast this

/-- For `m ≥ 128` and `s m⁴ ≤ 55·2^m`, the codes of Boolean circuits with `s` gates and `L`
outputs number at most `2^{m + (2m+2)s + mL}`. -/
theorem codeCount_le (hm : 128 ≤ m) {s : ℕ} (hs : s * m ^ 4 ≤ 55 * 2 ^ m) (L : ℕ) :
    codeCount m s L ≤ 2 ^ (m + (2 * m + 2) * s + m * L) := by
  have hs2 : 2 * s ≤ 2 ^ m := by
    refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < m ^ 4)
    have : 110 ≤ m ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hm 4)
    nlinarith [Nat.mul_le_mul_right (2 ^ m) this]
  have hm2 : 2 * (m + 1) ≤ 2 ^ m := by
    have h8 := pow_eight_le_two_pow (by omega : 64 ≤ m)
    have : m ^ 2 ≤ m ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith [Nat.mul_le_mul_right m hm]
  have hY : m + 1 + s ≤ 2 ^ m := by omega
  unfold codeCount
  rw [pow_add, pow_add, pow_mul, pow_mul]
  gcongr
  · omega
  · calc 3 * (m + 1 + s) ^ 2 ≤ 4 * (2 ^ m) ^ 2 := by gcongr; norm_num
      _ = 2 ^ (2 * m + 2) := by ring

/-- For `m ≥ 128`, `2^m ≤ m(m+1)a`, `s m⁴ ≤ 55·2^m` and `L ≤ m`:
`⌊2^m/m³⌋ + m + (2m+2)s + mL ≤ a`. -/
theorem exponent_le (hm : 128 ≤ m) {a s L : ℕ} (ha : 2 ^ m ≤ m * (m + 1) * a)
    (hs : s * m ^ 4 ≤ 55 * 2 ^ m) (hL : L ≤ m) :
    2 ^ m / m ^ 3 + (m + (2 * m + 2) * s + m * L) ≤ a := by
  have hd : m ^ 5 * (m + 1) ^ 2 ≤ 2 ^ m := by
    refine le_trans ?_ (pow_eight_le_two_pow (by omega))
    have : (m + 1) ^ 2 ≤ m ^ 3 := by nlinarith [Nat.mul_le_mul_right (m ^ 2) hm]
    calc m ^ 5 * (m + 1) ^ 2 ≤ m ^ 5 * m ^ 3 := Nat.mul_le_mul_left _ this
      _ = m ^ 8 := by ring
  have he : m * (m + 1) + 1 + 110 * (m + 1) ^ 2 ≤ m ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (m ^ 2) hm, Nat.mul_le_mul_right m hm]
  have hE := Nat.mul_div_le (2 ^ m) (m ^ 3)
  generalize 2 ^ m / m ^ 3 = E at hE ⊢
  generalize 2 ^ m = X at *
  refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < m ^ 4 * (m + 1))
  nlinarith [Nat.mul_le_mul_left (m * (m + 1)) hE, Nat.mul_le_mul_left (2 * (m + 1) ^ 2) hs,
    Nat.mul_le_mul_left (m ^ 5 * (m + 1)) hL, Nat.mul_le_mul_right X he,
    Nat.mul_le_mul_left (m ^ 3) ha]

/-! ### The number of matroids -/

/-- For `m > 0` there are at least `2^a` matroids on `Fin m` with ground set `univ`, for some
`a` with `2^m ≤ m(m+1)a`. -/
theorem exists_two_pow_le_ncard_matroids (hm : 0 < m) :
    ∃ a, 2 ^ m ≤ m * (m + 1) * a ∧ 2 ^ a ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  refine ⟨_, ?_, two_pow_ceil_le_ncard_matroids m⟩
  have hC : m.choose (m / 2) ≤ m * ⌈(m.choose (m / 2) : ℝ) / m⌉₊ := by
    have h := Nat.le_ceil ((m.choose (m / 2) : ℝ) / m)
    rw [div_le_iff₀ (by exact_mod_cast hm)] at h
    exact_mod_cast h.trans_eq (mul_comm _ _)
  calc 2 ^ m ≤ (m + 1) * m.choose (m / 2) := two_pow_le_succ_mul_choose_half m
    _ ≤ (m + 1) * (m * ⌈(m.choose (m / 2) : ℝ) / m⌉₊) := Nat.mul_le_mul_left _ hC
    _ = m * (m + 1) * ⌈(m.choose (m / 2) : ℝ) / m⌉₊ := by ring

/-! ### Corollary `cor:count` -/

/-- **Corollary `cor:count`, explicit form.**  For `m ≥ 128`, the number of matroids `M` on
`Fin m` (ground set `univ`) for which some signed tropical circuit of size less than
`2^{m/2}/m²` computes `h_M` on `{0,1}^m`, multiplied by `2^{⌊2^m/m³⌋}`, is at most the number
of all matroids on `Fin m` with ground set `univ`. -/
theorem corollaryD_explicit (hm : 128 ≤ m) :
    2 ^ (2 ^ m / m ^ 3) * Set.ncard {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∃ C : Circuit STOp m, (C.size : ℝ) < 2 ^ ((m : ℝ) / 2) / m ^ 2 ∧
        ∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
          = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]}
      ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ} := by
  set S := ⌊(2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2⌋₊
  have hs : (15 * S ^ 2 + 40 * S) * m ^ 4 ≤ 55 * 2 ^ m := by
    have hS : S ^ 2 * m ^ 4 ≤ 2 ^ m := floor_sq_mul_le m
    nlinarith [Nat.mul_le_mul_right (m ^ 4) (Nat.le_self_pow two_ne_zero S)]
  have hL : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self
  obtain ⟨a, ha, hN⟩ := exists_two_pow_le_ncard_matroids (by omega : 0 < m)
  refine le_trans (Nat.mul_le_mul_left _ ((Set.ncard_le_ncard ?_
    (finite_matroids.subset fun M hM => hM.1)).trans
      ((corollaryD_count m S).trans (codeCount_le hm hs _)))) ?_
  · rintro M ⟨hE, C, hC, hcomp⟩
    exact ⟨hE, C, Nat.le_floor hC.le, hcomp⟩
  · rw [← pow_add]
    exact (Nat.pow_le_pow_right two_pos (exponent_le hm ha hs hL)).trans hN

/-- **Corollary `cor:count`.**  The fraction of the matroids on `Fin m` (ground set `univ`) for
which some signed tropical circuit of size less than `2^{m/2}/m²` computes `h_M` on `{0,1}^m`
tends to `0` as `m → ∞`. -/
theorem corollaryD_tendsto :
    Tendsto (fun m : ℕ => (Set.ncard {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∃ C : Circuit STOp m, (C.size : ℝ) < 2 ^ ((m : ℝ) / 2) / m ^ 2 ∧
        ∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
          = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]} : ℝ) /
      Set.ncard {M : Matroid (Fin m) | M.E = Set.univ}) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun m => by positivity)
    ((eventually_ge_atTop 128).mono fun m hm => ?_) tendsto_one_div_atTop_nhds_zero_nat
  have hE : m ≤ 2 ^ (2 ^ m / m ^ 3) := by
    have h8 := pow_eight_le_two_pow (by omega : 64 ≤ m)
    have : m ≤ 2 ^ m / m ^ 3 := (Nat.le_div_iff_mul_le (by positivity)).2 (le_trans
      (by rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by norm_num)) h8)
    exact this.trans Nat.lt_two_pow_self.le
  rw [div_le_div_iff₀ (by exact_mod_cast ncard_matroids_pos)
    (by exact_mod_cast (by omega : 0 < m)), one_mul]
  exact_mod_cast (Nat.mul_le_mul_left _ hE).trans
    ((mul_comm _ _).trans_le (corollaryD_explicit hm))

/-- **Corollary `cor:count`, circuits on `ℝ^m`.**  The fraction of the matroids on `Fin m`
(ground set `univ`) for which some signed tropical circuit of size less than `2^{m/2}/m²`
computes `h_M` at every `w ∈ ℝ^m` tends to `0` as `m → ∞`. -/
theorem corollaryD_tendsto_of_forall :
    Tendsto (fun m : ℕ => (Set.ncard {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∃ C : Circuit STOp m, (C.size : ℝ) < 2 ^ ((m : ℝ) / 2) / m ^ 2 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight M w]} : ℝ) /
      Set.ncard {M : Matroid (Fin m) | M.E = Set.univ}) atTop (𝓝 0) := by
  refine squeeze_zero (fun m => by positivity) (fun m => div_le_div_of_nonneg_right
    (Nat.cast_le.2 (Set.ncard_le_ncard ?_ (finite_matroids.subset fun M hM => hM.1)))
      (Nat.cast_nonneg _)) corollaryD_tendsto
  rintro M ⟨hE, C, hC, hw⟩
  exact ⟨hE, C, hC, fun T => hw _⟩

/-- **Corollary `cor:count`, "most matroids" form.**  The fraction of the matroids `M` on
`Fin m` (ground set `univ`) for which every signed tropical circuit computing `h_M` on
`{0,1}^m` has size at least `2^{m/2}/m²` tends to `1` as `m → ∞`. -/
theorem corollaryD_most :
    Tendsto (fun m : ℕ => (Set.ncard {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∀ C : Circuit STOp m, (∀ T : Finset (Fin m),
        C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
          = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]) →
        (2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2 ≤ C.size} : ℝ) /
      Set.ncard {M : Matroid (Fin m) | M.E = Set.univ}) atTop (𝓝 1) := by
  have h := corollaryD_tendsto.const_sub 1
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun m => ?_)
  -- the matroids counted here are the complement of those counted in `corollaryD_tendsto`
  have hset : {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∀ C : Circuit STOp m, (∀ T : Finset (Fin m),
        C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
          = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]) →
        (2 : ℝ) ^ ((m : ℝ) / 2) / m ^ 2 ≤ C.size} = {M : Matroid (Fin m) | M.E = Set.univ} \
      {M : Matroid (Fin m) | M.E = Set.univ ∧
        ∃ C : Circuit STOp m, (C.size : ℝ) < 2 ^ ((m : ℝ) / 2) / m ^ 2 ∧
          ∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
            = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]} := by
    ext M
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_and, not_exists]
    exact and_congr_right fun hE => ⟨fun h _ C hC hcomp => not_lt.2 (h C hcomp) hC,
      fun h C hcomp => not_lt.1 fun hC => h hE C hC hcomp⟩
  dsimp only
  rw [hset, Set.cast_ncard_sdiff (fun M hM => hM.1) finite_matroids, sub_div,
    div_self (by exact_mod_cast ncard_matroids_pos.ne')]

/-- **Corollary `cor:count`, finite form, without the hypothesis `hN` of `corollaryD`.**  If
`codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉ < 2^{⌈C(m,⌊m/2⌋)/m⌉}`, some matroid on `Fin m` (ground
set `univ`) has no signed tropical circuit of size at most `S` computing `h_M` on `{0,1}^m`. -/
theorem corollaryD_unconditional (m S : ℕ)
    (hlt : codeCount m (15 * S ^ 2 + 40 * S) (Nat.size m) < 2 ^ ⌈(m.choose (m / 2) : ℝ) / m⌉₊) :
    ∃ M : Matroid (Fin m), M.E = Set.univ ∧ ∀ C : Circuit STOp m,
      (∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
        = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]) → S < C.size :=
  corollaryD m S _ (two_pow_ceil_le_ncard_matroids m) hlt

end SignedTropical.Asymptotic
