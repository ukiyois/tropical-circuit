import SignedTropical.Classes.Dual
import SignedTropical.Classes.Field
import Mathlib.NumberTheory.Chebyshev
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.RingTheory.Localization.Module

/-!
# Matroids represented over `ℚ`

`greedy_intersection.tex`, Corollary `cor:classes`, item 3, for matroids represented over `ℚ`
by an integer matrix `A ∈ ℤ^{r × m}` whose entries have bit length at most `b`
(`|A_{ij}| < 2^b`).  Scaling each column of a rational matrix by a common denominator of its
entries does not change the column matroid, so every matroid represented over `ℚ` has such a
representation (a remark, not formalized).

The rank over `ℚ` is the largest rank modulo a prime `p ≤ N` (`rk_rat_eq_max`):

* reduction modulo `p` never increases the rank (`linearIndepOn_rat_of_zmod`): a rational
  relation between the columns scales to an integer relation whose coefficients have no
  common factor, and it stays nontrivial modulo `p`;
* for every `S` some prime `p ≤ N` keeps a basis of `S` independent: the Gram determinant
  `D = det(A_Iᵀ A_I)` of a basis `I` is a nonzero integer (`gram_det_ne_zero`), of absolute
  value less than `2^L` with `L = 2 r (r + b) + 1` (`natAbs_det_gram_lt`), and when
  `(N+1) N^L < 2^N` some prime `p ≤ N` does not divide it (`exists_prime_not_dvd`, from
  Chebyshev's bound `2^N ≤ (N+1) lcm(1, …, N)`); then `I` stays independent modulo `p`
  (`linearIndepOn_zmod_of_not_dvd`).  `N = primeBound L ≤ 8 (L+1)²` will do.

The rank circuit (`ratRankCircuit`) runs the rank circuits of `Field.lean` over `ZMod p` for
all primes `p ≤ N` and takes the maximum with the signed-maximum gadget of `Converse.lean`.
-/

open Finset Module Submodule
open scoped Matrix

namespace SignedTropical.Classes

variable {r m : ℕ}

/-! ### A prime that does not divide a given integer -/

/-- **A small prime that does not divide `D`.**  If `0 < |D| < 2^L`, `N ≥ 1` and
`(N+1) N^L < 2^N`, then some prime `p ≤ N` does not divide `D`. -/
theorem exists_prime_not_dvd {D : ℤ} (hD : D ≠ 0) {L N : ℕ} (hDL : D.natAbs < 2 ^ L)
    (hN1 : 1 ≤ N) (hN : (N + 1) * N ^ L < 2 ^ N) :
    ∃ p, p.Prime ∧ p ≤ N ∧ ¬ (p : ℤ) ∣ D := by
  by_contra hcon
  push Not at hcon
  -- Step 1: the product of the primes `p ≤ N` divides `D`, so there are fewer than `L`
  have hdvd : ∏ p ∈ Nat.primesLE N, p ∣ D.natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primesLE hp).prime) fun p hp =>
      Int.natCast_dvd.1 (hcon p (Nat.prime_of_mem_primesLE hp) (Nat.le_of_mem_primesLE hp))
  have hprod : 2 ^ (Nat.primesLE N).card ≤ ∏ p ∈ Nat.primesLE N, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => Nat.two_le_of_mem_primesLE hp
  have hcard : (Nat.primesLE N).card < L :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1
      ((hprod.trans (Nat.le_of_dvd (Int.natAbs_pos.2 hD) hdvd)).trans_lt hDL)
  -- Step 2: `lcm(1, …, N) ≤ N^L`
  have hlcm : Nat.lcmUpto N ≤ N ^ L := by
    rw [Nat.lcmUpto_eq_prod_pow_log]
    calc ∏ p ∈ Nat.primesLE N, p ^ Nat.log p N ≤ ∏ _p ∈ Nat.primesLE N, N :=
          Finset.prod_le_prod' fun p _ => Nat.pow_log_le_self p (by omega)
      _ = N ^ (Nat.primesLE N).card := Finset.prod_const N
      _ ≤ N ^ L := Nat.pow_le_pow_right hN1 hcard.le
  -- Step 3: Chebyshev's bound `2^N ≤ (N+1) lcm(1, …, N)`
  have := (Chebyshev.two_pow_le_mul_lcmUpto N).trans (Nat.mul_le_mul_left (N + 1) hlcm)
  omega

/-- The bound on the primes: `2^{2 s + 1}` with `s = ⌈log₂(L+2)⌉`. -/
def primeBound (L : ℕ) : ℕ := 2 ^ (2 * Nat.size (L + 1) + 1)

/-- `N = primeBound L` satisfies `(N+1) N^L < 2^N`, and `N ≤ 8 (L+1)²`. -/
theorem primeBound_spec (L : ℕ) :
    1 ≤ primeBound L ∧ (primeBound L + 1) * primeBound L ^ L < 2 ^ primeBound L ∧
      primeBound L ≤ 8 * (L + 1) ^ 2 := by
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.size (L + 1) := ⟨_, rfl⟩
  have hcX : L + 1 < 2 ^ s := hs ▸ Nat.lt_size_self (L + 1)
  have hXc : 2 ^ s ≤ 2 * (L + 1) := by
    have hs0 : 0 < s := hs ▸ Nat.size_pos.2 (by omega)
    have h : 2 ^ (s - 1) ≤ L + 1 := Nat.lt_size.1 (show s - 1 < Nat.size (L + 1) by omega)
    rw [show s = s - 1 + 1 by omega, pow_succ]
    omega
  have hsX : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have hN : primeBound L = 2 * 2 ^ s * 2 ^ s := by
    rw [primeBound, ← hs, pow_succ, two_mul, pow_add]; ring
  have hN1 : 1 ≤ primeBound L := by rw [hN]; nlinarith
  refine ⟨hN1, ?_, by rw [hN]; nlinarith⟩
  -- `(N+1) N^L ≤ 2 N^{L+1} = 2^{(2s+1)(L+1)+1} < 2^N`
  have hlt : (2 * s + 1) * (L + 1) + 1 < primeBound L := by rw [hN]; nlinarith
  calc (primeBound L + 1) * primeBound L ^ L ≤ 2 * primeBound L * primeBound L ^ L :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ ((2 * s + 1) * (L + 1) + 1) := by rw [primeBound, ← hs, ← pow_mul]; ring
    _ < 2 ^ primeBound L := Nat.pow_lt_pow_right (by norm_num) hlt

/-! ### Reduction modulo a prime -/

/-- **Independence modulo `p` implies independence over `ℚ`**, for integer columns. -/
theorem linearIndepOn_rat_of_zmod (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) [Fact p.Prime]
    {I : Set (Fin m)} (h : LinearIndepOn (ZMod p) (colK (A.map (Int.cast : ℤ → ZMod p))) I) :
    LinearIndepOn ℚ (colK (A.map (Int.cast : ℤ → ℚ))) I := by
  rw [LinearIndepOn, ← LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn,
    linearIndepOn_iff']
  rw [linearIndepOn_iff'] at h
  intro t g ht hsum
  -- Step 1: an integer relation between the columns
  have hint : ∀ j, ∑ i ∈ t, g i * A j i = 0 := by
    intro j
    have h₁ := congrFun hsum j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h₁
    simp only [colK, Matrix.map_apply, zsmul_eq_mul] at h₁
    exact_mod_cast h₁
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hg₀⟩ := hne
  -- Step 2: divide by the greatest common divisor of the coefficients
  obtain ⟨g', hg', hgcd⟩ := Finset.extract_gcd g ⟨i₀, hi₀⟩
  have hd : t.gcd g ≠ 0 := fun h0 => hg₀ (Finset.gcd_eq_zero_iff.1 h0 i₀ hi₀)
  have hint' : ∀ j, ∑ i ∈ t, g' i * A j i = 0 := by
    intro j
    have h₁ := hint j
    rw [Finset.sum_congr rfl fun i hi => by rw [hg' i hi, mul_assoc], ← Finset.mul_sum] at h₁
    exact (mul_eq_zero.1 h₁).resolve_left hd
  -- Step 3: modulo `p` the relation is trivial, so `p` divides every coefficient
  have hp := h t (fun i => (g' i : ZMod p)) ht (by
    funext j
    have h₁ := congrArg (Int.cast : ℤ → ZMod p) (hint' j)
    push_cast at h₁
    simpa [Finset.sum_apply, colK] using h₁)
  have hdvd : (p : ℤ) ∣ t.gcd g' :=
    Finset.dvd_gcd fun i hi => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hp i hi)
  rw [hgcd] at hdvd
  have h1 := Int.eq_one_of_dvd_one (by positivity) hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast h1)

/-- The columns of `A` in `I`, as an `r × I` matrix. -/
abbrev colsOf {K : Type} (A : Matrix (Fin r) (Fin m) K) (I : Finset (Fin m)) :
    Matrix (Fin r) I K :=
  A.submatrix id (Subtype.val : I → Fin m)

/-- The Gram matrix `A_Iᵀ A_I` of the columns of `A` in `I`. -/
def gram (A : Matrix (Fin r) (Fin m) ℤ) (I : Finset (Fin m)) : Matrix I I ℤ :=
  (colsOf A I)ᵀ * colsOf A I

theorem gram_map {K : Type} [Field K] (A : Matrix (Fin r) (Fin m) ℤ) (I : Finset (Fin m)) :
    (gram A I).map (Int.cast : ℤ → K)
      = (colsOf (A.map (Int.cast : ℤ → K)) I)ᵀ * colsOf (A.map (Int.cast : ℤ → K)) I := by
  ext i j
  simp [gram, Matrix.mul_apply]

theorem det_gram_map {K : Type} [Field K] (A : Matrix (Fin r) (Fin m) ℤ) (I : Finset (Fin m)) :
    (((gram A I).det : ℤ) : K)
      = ((colsOf (A.map (Int.cast : ℤ → K)) I)ᵀ * colsOf (A.map (Int.cast : ℤ → K)) I).det := by
  rw [← gram_map]
  exact (Int.castRingHom K).map_det (gram A I)

/-- A combination of the columns in `I` is the product with the column submatrix. -/
theorem sum_smul_colK {K : Type} [Field K] (A : Matrix (Fin r) (Fin m) K) (I : Finset (Fin m))
    (g : I → K) : ∑ e, g e • colK A e = colsOf A I *ᵥ g := by
  funext j
  simp [colK, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **Independent columns have a nonzero Gram determinant.** -/
theorem gram_det_ne_zero (A : Matrix (Fin r) (Fin m) ℤ) (I : Finset (Fin m))
    (hI : LinearIndepOn ℚ (colK (A.map (Int.cast : ℤ → ℚ))) (I : Set (Fin m))) :
    (gram A I).det ≠ 0 := by
  intro h0
  set B := colsOf (A.map (Int.cast : ℤ → ℚ)) I
  have hdet : (Bᵀ * B).det = 0 := by rw [← det_gram_map, h0, Int.cast_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  -- `|B v|² = vᵀ Bᵀ B v = 0`
  have hBv : B *ᵥ v = 0 := by
    have h₁ : (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = 0 :=
      calc (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = (v ᵥ* Bᵀ) ⬝ᵥ (B *ᵥ v) := by rw [Matrix.vecMul_transpose]
        _ = v ⬝ᵥ (Bᵀ *ᵥ (B *ᵥ v)) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = 0 := by rw [Matrix.mulVec_mulVec, hv, dotProduct_zero]
    exact dotProduct_self_eq_zero.1 h₁
  have hli : LinearIndependent ℚ (fun e : I => colK (A.map (Int.cast : ℤ → ℚ)) e) := hI
  rw [Fintype.linearIndependent_iff] at hli
  exact hv0 (funext fun e => hli v (by rw [sum_smul_colK]; exact hBv) e)

/-- **A prime that does not divide the Gram determinant keeps the columns independent.** -/
theorem linearIndepOn_zmod_of_not_dvd (A : Matrix (Fin r) (Fin m) ℤ) (I : Finset (Fin m))
    (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ (gram A I).det) :
    LinearIndepOn (ZMod p) (colK (A.map (Int.cast : ℤ → ZMod p))) (I : Set (Fin m)) := by
  set B := colsOf (A.map (Int.cast : ℤ → ZMod p)) I
  have hdet : (Bᵀ * B).det ≠ 0 := by
    rw [← det_gram_map]
    exact fun h => hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  show LinearIndependent (ZMod p) (fun e : I => colK (A.map (Int.cast : ℤ → ZMod p)) e)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [sum_smul_colK] at hg
  have hBg : (Bᵀ * B) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, hg, Matrix.mulVec_zero]
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, fun h => hi (by rw [h]; rfl), hBg⟩)

/-- **The Gram determinant is small**: `|det(A_Iᵀ A_I)| ≤ |I|! (r 4^b)^{|I|}` when all
entries satisfy `|A_{ij}| < 2^b`. -/
theorem natAbs_det_gram_le (A : Matrix (Fin r) (Fin m) ℤ) {b : ℕ} (hA : ∀ i j, |A i j| < 2 ^ b)
    (I : Finset (Fin m)) :
    (gram A I).det.natAbs ≤ Nat.factorial I.card * (r * 4 ^ b) ^ I.card := by
  have hentry : ∀ i j, AbsoluteValue.abs ((gram A I) i j) ≤ (r * 4 ^ b : ℤ) := by
    intro i j
    rw [AbsoluteValue.abs_apply]
    simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id]
    calc |∑ k, A k i * A k j| ≤ ∑ k, |A k i * A k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin r, (2 ^ b * 2 ^ b : ℤ) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hA k i).le (hA k j).le (abs_nonneg _) (by positivity)
      _ = r * 4 ^ b := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_pow]
          norm_num
  have h := Matrix.det_le hentry
  rw [AbsoluteValue.abs_apply, Fintype.card_coe, nsmul_eq_mul] at h
  have h' : ((gram A I).det.natAbs : ℤ)
      ≤ ((Nat.factorial I.card * (r * 4 ^ b) ^ I.card : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; push_cast; exact h
  exact_mod_cast h'

/-- With `|I| ≤ r`, the Gram determinant has fewer than `2 r (r + b) + 1` bits. -/
theorem natAbs_det_gram_lt (A : Matrix (Fin r) (Fin m) ℤ) {b : ℕ} (hA : ∀ i j, |A i j| < 2 ^ b)
    (I : Finset (Fin m)) (hI : I.card ≤ r) :
    (gram A I).det.natAbs < 2 ^ (2 * (r * (r + b)) + 1) := by
  have hrr : r * r ≤ 4 ^ r := by
    have := Nat.lt_two_pow_self (n := r)
    calc r * r ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul this.le this.le
      _ = 4 ^ r := by rw [← mul_pow]; norm_num
  set k := I.card
  calc (gram A I).det.natAbs ≤ Nat.factorial k * (r * 4 ^ b) ^ k := natAbs_det_gram_le A hA I
    _ ≤ r ^ k * (r * 4 ^ b) ^ k :=
        Nat.mul_le_mul_right _ ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hI k))
    _ = (r * r * 4 ^ b) ^ k := by rw [← mul_pow, mul_assoc]
    _ ≤ (4 ^ r * 4 ^ b) ^ k := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hrr) k
    _ = 4 ^ ((r + b) * k) := by rw [← pow_add, ← pow_mul]
    _ ≤ 4 ^ (r * (r + b)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ = 2 ^ (2 * (r * (r + b))) := by rw [pow_mul 2 2]; norm_num
    _ < 2 ^ (2 * (r * (r + b)) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### The rank over `ℚ` is the largest rank modulo a small prime -/

/-- The rank of `S` in the column matroid of `A` modulo `p`; `0` when `p` is not prime. -/
noncomputable def modRk (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) (S : Finset (Fin m)) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    rk (colMatroid (A.map (Int.cast : ℤ → ZMod p))) S
  else 0

/-- **Reduction modulo a prime does not increase the rank.** -/
theorem modRk_le (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) (S : Finset (Fin m)) :
    modRk A p S ≤ rk (colMatroid (A.map (Int.cast : ℤ → ℚ))) S := by
  unfold modRk
  split_ifs with h
  · haveI : Fact p.Prime := ⟨h⟩
    obtain ⟨I₀, hI⟩ := (colMatroid (A.map (Int.cast : ℤ → ZMod p))).exists_isBasis
      (S : Set (Fin m)) (by simp)
    obtain ⟨I, rfl⟩ := exists_finset I₀
    rw [← card_eq_rk _ hI]
    exact card_le_rk _ ((colMatroid_indep _ I).2
      (linearIndepOn_rat_of_zmod A p ((colMatroid_indep _ I).1 hI.indep)))
      (Finset.coe_subset.1 hI.subset)
  · exact Nat.zero_le _

/-- **Some prime `p ≤ N` keeps the rank of `S`**, for `N = primeBound (2 r (r + b) + 1)`. -/
theorem exists_le_modRk (A : Matrix (Fin r) (Fin m) ℤ) {b : ℕ} (hA : ∀ i j, |A i j| < 2 ^ b)
    (S : Finset (Fin m)) :
    ∃ p, p.Prime ∧ p ≤ primeBound (2 * (r * (r + b)) + 1) ∧
      rk (colMatroid (A.map (Int.cast : ℤ → ℚ))) S ≤ modRk A p S := by
  obtain ⟨I₀, hI⟩ := (colMatroid (A.map (Int.cast : ℤ → ℚ))).exists_isBasis (S : Set (Fin m))
    (by simp)
  obtain ⟨I, rfl⟩ := exists_finset I₀
  have hind := (colMatroid_indep _ I).1 hI.indep
  have hcard : I.card ≤ r := by
    rw [card_eq_rk _ hI]
    exact (rk_le_rank _ S).trans (rank_colMatroid_le _)
  obtain ⟨hN1, hN, -⟩ := primeBound_spec (2 * (r * (r + b)) + 1)
  obtain ⟨p, hp, hpN, hndvd⟩ := exists_prime_not_dvd (gram_det_ne_zero A I hind)
    (natAbs_det_gram_lt A hA I hcard) hN1 hN
  refine ⟨p, hp, hpN, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [modRk, dif_pos hp, ← card_eq_rk _ hI]
  exact card_le_rk _ ((colMatroid_indep _ I).2 (linearIndepOn_zmod_of_not_dvd A I p hndvd))
    (Finset.coe_subset.1 hI.subset)

/-- The primes `p ≤ N`, in increasing order. -/
def primesUpTo (N : ℕ) : List ℕ := (List.range (N + 1)).filter Nat.Prime

theorem foldl_max_le {f : ℕ → ℕ} {R : ℕ} :
    ∀ (ps : List ℕ) (a : ℕ), a ≤ R → (∀ p ∈ ps, f p ≤ R) →
      ps.foldl (fun a p => max a (f p)) a ≤ R
  | [], _, ha, _ => ha
  | p :: ps, a, ha, h => foldl_max_le ps _ (max_le ha (h p (by simp)))
      fun q hq => h q (by simp [hq])

theorem le_foldl_max {f : ℕ → ℕ} :
    ∀ (ps : List ℕ) (a : ℕ), a ≤ ps.foldl (fun a p => max a (f p)) a ∧
      ∀ p ∈ ps, f p ≤ ps.foldl (fun a p => max a (f p)) a
  | [], _ => ⟨le_rfl, by simp⟩
  | p :: ps, a => by
    obtain ⟨h₁, h₂⟩ := le_foldl_max (f := f) ps (max a (f p))
    refine ⟨(le_max_left _ _).trans h₁, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact (le_max_right _ _).trans h₁
    · exact h₂ q hq

/-- **The rank over `ℚ` is the largest rank modulo a prime `p ≤ N`.** -/
theorem rk_rat_eq_max (A : Matrix (Fin r) (Fin m) ℤ) {b : ℕ} (hA : ∀ i j, |A i j| < 2 ^ b)
    (S : Finset (Fin m)) :
    (primesUpTo (primeBound (2 * (r * (r + b)) + 1))).foldl (fun a p => max a (modRk A p S)) 0
      = rk (colMatroid (A.map (Int.cast : ℤ → ℚ))) S := by
  refine le_antisymm (foldl_max_le _ _ (Nat.zero_le _) fun p _ => modRk_le A p S) ?_
  obtain ⟨p, hp, hpN, hle⟩ := exists_le_modRk A hA S
  have hmem : p ∈ primesUpTo (primeBound (2 * (r * (r + b)) + 1)) :=
    List.mem_filter.2 ⟨List.mem_range.2 (Nat.lt_succ_of_le hpN), decide_eq_true hp⟩
  exact hle.trans ((le_foldl_max (f := fun p => modRk A p S) _ 0).2 p hmem)

/-! ### The rank circuit -/

/-- The rank circuit modulo `p` (`Field.lean`); the empty circuit when `p` is not prime. -/
noncomputable def primeRankCircuit (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) : Circuit BoolOp m :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    fieldRankCircuit (A.map (Int.cast : ℤ → ZMod p))
  else ⟨[], []⟩

theorem primeRankCircuit_spec (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) :
    (primeRankCircuit A p).size ≤ 8 * p ^ 2 * (m + 1) * (r + 1) ^ 2 ∧
      ∀ S : Finset (Fin m),
        bitsVal ((primeRankCircuit A p).eval boolInterp (indicator S)) = modRk A p S := by
  unfold primeRankCircuit modRk
  split_ifs with h
  · haveI : Fact p.Prime := ⟨h⟩
    refine ⟨?_, fun S => ?_⟩
    · rw [(fieldRankCircuit_spec _).1, ZMod.card]
      exact fieldSize_le h.two_le m r
    · have h₁ := fieldRankCircuit_rank (A.map (Int.cast : ℤ → ZMod p)) S
      rw [← coe_rk] at h₁
      exact_mod_cast h₁
  · exact ⟨Nat.zero_le _, fun S => rfl⟩

/-- The value of the circuit modulo `p` is at most `r`. -/
theorem bitsVal_primeRankCircuit_le (A : Matrix (Fin r) (Fin m) ℤ) (p : ℕ) (x : Fin m → Bool) :
    bitsVal ((primeRankCircuit A p).eval boolInterp x) ≤ r := by
  rw [← indicator_filter x, (primeRankCircuit_spec A p).2]
  exact (modRk_le A p _).trans ((rk_le_rank _ _).trans (rank_colMatroid_le _))

/-- Inlining a Boolean circuit on the inputs of the host circuit. -/
theorem inline_input_spec (B : Circuit BoolOp m) (gs : List (Gate BoolOp m)) :
    gs <+: (inline (fun o a b => emit o a b) (fun i => .input i) .const B gs).1 ∧
      (inline (fun o a b => emit o a b) (fun i => .input i) .const B gs).1.length
        = gs.length + B.size ∧
      DenL boolInterp (inline (fun o a b => emit o a b) (fun i => .input i) .const B gs).1
        (inline (fun o a b => emit o a b) (fun i => .input i) .const B gs).2
        (fun x => B.eval boolInterp x) := by
  obtain ⟨hp, h⟩ := inline_spec (R := Den boolInterp) (J := fun _ => boolInterp)
    (φ := fun i x => x i) (gad := fun o a b => emit o a b) (inp := fun i => .input i)
    (c := .const) (gs₀ := gs) (fun _ _ _ _ hp h => h.mono hp) (den_const _)
    (fun i => den_input _ i)
    (fun o _ _ _ _ gs _ h₁ h₂ => ⟨isPrefix_emit _ _ _ _, den_emit o h₁ h₂⟩) B
  refine ⟨hp, ?_, (DenL.of_forall₂ h).congr fun x => ?_⟩
  · rw [length_inline (fun _ => 1) (fun o a b gs => length_emit o a b gs)]
    simp [Circuit.size]
  · simp only [List.map_map]; rfl

/-- The signed maximum of two `W`-bit vectors holding numbers below `2^{W-1}` is their
maximum. -/
theorem bvMax_ofNat {W a c : ℕ} (ha : 2 * a < 2 ^ W) (hc : 2 * c < 2 ^ W) :
    (bvInterp W).op .max (BitVec.ofNat W a) (BitVec.ofNat W c) = BitVec.ofNat W (max a c) := by
  have hta : (BitVec.ofNat W a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ha
  have htc : (BitVec.ofNat W c).toInt = c := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hc
  simp only [bvInterp]
  by_cases hlt : a < c
  · rw [if_pos (BitVec.slt_iff_toInt_lt.2 (by rw [hta, htc]; exact_mod_cast hlt)),
      max_eq_right hlt.le]
  · rw [if_neg (by rw [BitVec.slt_iff_toInt_lt, hta, htc]; exact_mod_cast hlt),
      max_eq_left (not_lt.1 hlt)]

/-- Run the rank circuits modulo the primes in `ps` and keep the running maximum in `acc`, a
`W`-bit two's complement number: `s_p + 15 W + 10` gates for the prime `p`. -/
noncomputable def maxRankB (A : Matrix (Fin r) (Fin m) ℤ) (W : ℕ) :
    List ℕ → List (Arg m) → Bld BoolOp m (List (Arg m))
  | [], acc => fun gs => (gs, acc)
  | p :: ps, acc => fun gs =>
    let q := inline (fun o a b => emit o a b) (fun i => .input i) .const (primeRankCircuit A p) gs
    let t := bvGad W .max acc (fit W q.2) q.1
    maxRankB A W ps t.2 t.1

theorem maxRankB_spec (A : Matrix (Fin r) (Fin m) ℤ) {W : ℕ} (hW : 2 * r < 2 ^ W) :
    ∀ (ps : List ℕ) {acc : List (Arg m)} {F : (Fin m → Bool) → ℕ} {gs : List (Gate BoolOp m)},
      (∀ x, F x ≤ r) → BitRep W gs acc (fun x => BitVec.ofNat W (F x)) →
      gs <+: (maxRankB A W ps acc gs).1 ∧
        (maxRankB A W ps acc gs).1.length
          = gs.length + (ps.map fun p => (primeRankCircuit A p).size + (15 * W + 10)).sum ∧
        BitRep W (maxRankB A W ps acc gs).1 (maxRankB A W ps acc gs).2 (fun x =>
          BitVec.ofNat W (ps.foldl (fun a p =>
            max a (bitsVal ((primeRankCircuit A p).eval boolInterp x))) (F x)))
  | [], acc, F, gs, _, hacc => ⟨List.prefix_refl _, by simp [maxRankB], hacc⟩
  | p :: ps, acc, F, gs, hF, hacc => by
    obtain ⟨hp₁, hlen₁, hden₁⟩ := inline_input_spec (primeRankCircuit A p) gs
    set q := inline (fun o a b => emit o a b) (fun i => .input i) .const (primeRankCircuit A p) gs
    obtain ⟨hp₂, hmax⟩ := bvGad_spec (hacc.mono hp₁) (bitRep_fit hden₁ W) .max
    have hmax' : BitRep W (bvGad W .max acc (fit W q.2) q.1).1
        (bvGad W .max acc (fit W q.2) q.1).2 (fun x =>
          BitVec.ofNat W (max (F x) (bitsVal ((primeRankCircuit A p).eval boolInterp x)))) :=
      hmax.congr fun x => congrArg bitsOf (bvMax_ofNat (by have := hF x; omega)
        (by have := bitsVal_primeRankCircuit_le A p x; omega))
    obtain ⟨hp₃, hlen₃, hden₃⟩ := maxRankB_spec A hW ps
      (fun x => max_le (hF x) (bitsVal_primeRankCircuit_le A p x)) hmax'
    refine ⟨hp₁.trans (hp₂.trans hp₃), ?_, hden₃⟩
    show (maxRankB A W ps (bvGad W .max acc (fit W q.2) q.1).2
      (bvGad W .max acc (fit W q.2) q.1).1).1.length = _
    rw [hlen₃, length_bvGad, hlen₁]
    simp only [bvCost, List.map_cons, List.sum_cons]
    ring

/-- **The rank circuit over `ℚ`**: the rank circuits modulo the primes `p ≤ N` and their
maximum, in `⌈log₂(r+1)⌉ + 1` bits. -/
noncomputable def ratRankCircuit (A : Matrix (Fin r) (Fin m) ℤ) (N : ℕ) : Circuit BoolOp m :=
  let p := maxRankB A (Nat.size r + 1) (primesUpTo N) (List.replicate (Nat.size r + 1) .const) []
  ⟨p.1, p.2⟩

/-- **Size and value of the rank circuit over `ℚ`.**  It has at most
`(N+1) (8 N² (m+1) (r+1)² + 15 (⌈log₂(r+1)⌉ + 1) + 10)` gates, and on the indicator vector
of `S` it outputs in binary the largest rank of `S` modulo a prime `p ≤ N`. -/
theorem ratRankCircuit_spec (A : Matrix (Fin r) (Fin m) ℤ) (N : ℕ) :
    (ratRankCircuit A N).size
        ≤ (N + 1) * (8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * (Nat.size r + 1) + 10) ∧
      ∀ S : Finset (Fin m), bitsVal ((ratRankCircuit A N).eval boolInterp (indicator S))
        = (primesUpTo N).foldl (fun a p => max a (modRk A p S)) 0 := by
  set W := Nat.size r + 1
  have hW : 2 * r < 2 ^ W := by
    have := Nat.lt_size_self r
    rw [show W = Nat.size r + 1 from rfl, pow_succ]; omega
  have hacc : BitRep W ([] : List (Gate BoolOp m)) (List.replicate W .const)
      (fun _ => BitVec.ofNat W 0) :=
    ⟨by simp [Arg.Valid], fun x => by
      show _ = bitsOf (0 : BitVec W)
      rw [bitsOf_zero]
      simp [Arg.read, boolInterp]⟩
  obtain ⟨-, hlen, hden⟩ := maxRankB_spec A hW (primesUpTo N) (F := fun _ => 0)
    (fun _ => Nat.zero_le _) hacc
  refine ⟨?_, fun S => ?_⟩
  · show (maxRankB A W (primesUpTo N) (List.replicate W .const) []).1.length ≤ _
    rw [hlen, List.length_nil, zero_add]
    have hbound : ∀ c ∈ (primesUpTo N).map fun p => (primeRankCircuit A p).size + (15 * W + 10),
        c ≤ 8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * W + 10 := by
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      have hpN : p ≤ N := Nat.lt_succ_iff.1 (List.mem_range.1 (List.mem_filter.1 hp).1)
      have h₁ := (primeRankCircuit_spec A p).1
      have h₂ : 8 * p ^ 2 * (m + 1) * (r + 1) ^ 2 ≤ 8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 := by
        gcongr
      omega
    have hlen' : ((primesUpTo N).map fun p => (primeRankCircuit A p).size + (15 * W + 10)).length
        ≤ N + 1 := by
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    calc _ ≤ ((primesUpTo N).map fun p => (primeRankCircuit A p).size + (15 * W + 10)).length
          • (8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * W + 10) := List.sum_le_card_nsmul _ _ hbound
      _ ≤ (N + 1) * (8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * W + 10) := by
          rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hlen'
  · have h := hden.2 (indicator S)
    simp only [Circuit.eval, ratRankCircuit]
    rw [h, bitsVal_bitsOf, BitVec.toNat_ofNat]
    have hval : ∀ p, bitsVal ((primeRankCircuit A p).eval boolInterp (indicator S))
        = modRk A p S := fun p => (primeRankCircuit_spec A p).2 S
    simp only [hval]
    apply Nat.mod_eq_of_lt
    have := foldl_max_le (f := fun p => modRk A p S) (R := r) (primesUpTo N) 0 (Nat.zero_le _)
      fun p _ => (modRk_le A p S).trans ((rk_le_rank _ _).trans (rank_colMatroid_le _))
    omega

/-! ### Explicit sizes and the main results -/

/-- With `N ≤ 32 (r (r + b) + 1)²`, the bound of `ratRankCircuit_spec` is at most
`2^19 (m+1) (r+1)² (r (r + b) + 1)^6`. -/
theorem ratSize_le (m r b N : ℕ) (hN : N ≤ 32 * (r * (r + b) + 1) ^ 2) :
    (N + 1) * (8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * (Nat.size r + 1) + 10)
      ≤ 2 ^ 19 * (m + 1) * (r + 1) ^ 2 * (r * (r + b) + 1) ^ 6 := by
  obtain ⟨T, hT⟩ : ∃ T, T = r * (r + b) + 1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = (m + 1) * (r + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hT] at hN ⊢
  have hT1 : 1 ≤ T := by omega
  have hrX : r + 1 ≤ X := by rw [hX]; nlinarith
  have hsr : Nat.size r ≤ r := Nat.size_le.2 Nat.lt_two_pow_self
  have hT4 : X ≤ T ^ 4 * X := Nat.le_mul_of_pos_left X (by positivity)
  have h1 : N + 1 ≤ 33 * T ^ 2 := by nlinarith
  have h2 : 8 * N ^ 2 ≤ 8192 * T ^ 4 := by
    have : N ^ 2 ≤ (32 * T ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
    nlinarith
  have h3 : 8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * (Nat.size r + 1) + 10
      ≤ 8217 * (T ^ 4 * X) := by
    have e : 8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 = 8 * N ^ 2 * X := by rw [hX]; ring
    have h4 : 8 * N ^ 2 * X ≤ 8192 * T ^ 4 * X := Nat.mul_le_mul_right X h2
    rw [e, show 8192 * T ^ 4 * X = 8192 * (T ^ 4 * X) by ring] at *
    omega
  calc (N + 1) * (8 * N ^ 2 * (m + 1) * (r + 1) ^ 2 + 15 * (Nat.size r + 1) + 10)
      ≤ 33 * T ^ 2 * (8217 * (T ^ 4 * X)) := Nat.mul_le_mul h1 h3
    _ = 271161 * X * T ^ 6 := by ring
    _ ≤ 2 ^ 19 * X * T ^ 6 := by gcongr; norm_num
    _ = 2 ^ 19 * (m + 1) * (r + 1) ^ 2 * T ^ 6 := by rw [hX]; ring

/-- The bound of Theorem A for a rank circuit of size at most
`2^19 (m+1) (r+1)² (r (r + b) + 1)^6` and rank `k ≤ r` is at most
`2^21 (m+1)² (r+1)² (r (r + b) + 1)^6`. -/
theorem theoremA_ratSize_le (m r b s k : ℕ)
    (hs : s ≤ 2 ^ 19 * (m + 1) * (r + 1) ^ 2 * (r * (r + b) + 1) ^ 6) (hk : k ≤ r) :
    3 * m * s + m * Nat.size k + 9 * m ^ 2 + 4 * m + 4 * Nat.size k + 1
      ≤ 2 ^ 21 * (m + 1) ^ 2 * (r + 1) ^ 2 * (r * (r + b) + 1) ^ 6 := by
  obtain ⟨T, hT⟩ : ∃ T, T = (r * (r + b) + 1) ^ 6 := ⟨_, rfl⟩
  rw [← hT] at hs ⊢
  have hT1 : 1 ≤ T := hT ▸ Nat.one_le_pow _ _ (by omega)
  have hsk : Nat.size k ≤ r := (Nat.size_le.2 Nat.lt_two_pow_self).trans hk
  have h1 : 3 * m * s ≤ 3 * 2 ^ 19 * ((m + 1) ^ 2 * (r + 1) ^ 2 * T) :=
    calc 3 * m * s ≤ 3 * (m + 1) * (2 ^ 19 * (m + 1) * (r + 1) ^ 2 * T) :=
          Nat.mul_le_mul (by omega) hs
      _ = 3 * 2 ^ 19 * ((m + 1) ^ 2 * (r + 1) ^ 2 * T) := by ring
  have h2 : m * Nat.size k + 9 * m ^ 2 + 4 * m + 4 * Nat.size k + 1
      ≤ 2 ^ 19 * ((m + 1) ^ 2 * (r + 1) ^ 2 * T) := by
    have h₁ : m * Nat.size k ≤ m * r := Nat.mul_le_mul_left m hsk
    have h₂ : m * r + 9 * m ^ 2 + 4 * m + 4 * r + 1 ≤ 9 * ((m + 1) ^ 2 * (r + 1) ^ 2) := by
      nlinarith [Nat.zero_le (m * r), Nat.zero_le (m * m * r), Nat.zero_le (m * r * r),
        Nat.zero_le (m * m * r * r)]
    have h₃ : (m + 1) ^ 2 * (r + 1) ^ 2 ≤ (m + 1) ^ 2 * (r + 1) ^ 2 * T :=
      Nat.le_mul_of_pos_right _ hT1
    omega
  calc 3 * m * s + m * Nat.size k + 9 * m ^ 2 + 4 * m + 4 * Nat.size k + 1
      ≤ 3 * 2 ^ 19 * ((m + 1) ^ 2 * (r + 1) ^ 2 * T)
        + 2 ^ 19 * ((m + 1) ^ 2 * (r + 1) ^ 2 * T) := by omega
    _ = 2 ^ 21 * (m + 1) ^ 2 * (r + 1) ^ 2 * T := by ring

/-- **Matroids represented over `ℚ`: Boolean rank circuits** (`greedy_intersection.tex`,
Corollary `cor:classes`, item 3).  Let `A ∈ ℤ^{r × m}` with `|A_{ij}| < 2^b` for all
entries.  A Boolean circuit of size at most `2^19 (m+1) (r+1)² (r (r + b) + 1)^6` outputs in
binary, from the indicator vector of `S ⊆ E`, the rank over `ℚ` of the columns of `A`
indexed by `S`: Mathlib's `Matrix.rank` of the column submatrix over `ℚ`, which is the rank
of `S` in the column matroid of `A` over `ℚ`. -/
theorem rat_rankCircuit (A : Matrix (Fin r) (Fin m) ℤ) (b : ℕ) (hA : ∀ i j, |A i j| < 2 ^ b) :
    ∃ B : Circuit BoolOp m, B.size ≤ 2 ^ 19 * (m + 1) * (r + 1) ^ 2 * (r * (r + b) + 1) ^ 6 ∧
      ∀ S : Finset (Fin m),
        bitsVal (B.eval boolInterp (indicator S))
            = ((A.map (Int.cast : ℤ → ℚ)).submatrix id (fun e : S => (e : Fin m))).rank ∧
        (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞)
            = (colMatroid (A.map (Int.cast : ℤ → ℚ))).eRk (S : Set (Fin m)) := by
  have hN : primeBound (2 * (r * (r + b)) + 1) ≤ 32 * (r * (r + b) + 1) ^ 2 :=
    calc primeBound (2 * (r * (r + b)) + 1) ≤ 8 * (2 * (r * (r + b)) + 1 + 1) ^ 2 :=
          (primeBound_spec _).2.2
      _ = 32 * (r * (r + b) + 1) ^ 2 := by ring
  obtain ⟨hsize, hval⟩ := ratRankCircuit_spec A (primeBound (2 * (r * (r + b)) + 1))
  have heRk : ∀ S : Finset (Fin m),
      (bitsVal ((ratRankCircuit A (primeBound (2 * (r * (r + b)) + 1))).eval boolInterp
        (indicator S)) : ℕ∞) = (colMatroid (A.map (Int.cast : ℤ → ℚ))).eRk (S : Set (Fin m)) :=
    fun S => by rw [hval S, rk_rat_eq_max A hA S, coe_rk]
  refine ⟨_, hsize.trans (ratSize_le m r b _ hN), fun S => ⟨?_, heRk S⟩⟩
  have h := heRk S
  rw [eRk_colMatroid_eq_rank] at h
  exact_mod_cast h

/-- **Matroids represented over `ℚ`: signed tropical circuits** (Theorem A applied to
`rat_rankCircuit`).  Let `A ∈ ℤ^{r × m}` with `|A_{ij}| < 2^b` for all entries and `M` the
column matroid of `A` over `ℚ`.  Then `h_M(w) = max_{B ∈ Bases(M)} w(B)` is computed at every
`w ∈ ℝ^m` by a signed tropical circuit of size at most
`2^21 (m+1)² (r+1)² (r (r + b) + 1)^6`. -/
theorem theoremA_rat (A : Matrix (Fin r) (Fin m) ℤ) (b : ℕ) (hA : ∀ i j, |A i j| < 2 ^ b) :
    ∃ C : Circuit STOp m,
      C.size ≤ 2 ^ 21 * (m + 1) ^ 2 * (r + 1) ^ 2 * (r * (r + b) + 1) ^ 6 ∧
      ∀ w : Fin m → ℝ,
        C.eval (stInterp ℝ) w = [maxBasisWeight (colMatroid (A.map (Int.cast : ℤ → ℚ))) w] := by
  obtain ⟨B, hB, hrk⟩ := rat_rankCircuit A b hA
  obtain ⟨C, hC, heval⟩ := theoremA (colMatroid (A.map (Int.cast : ℤ → ℚ))) (colMatroid_E _) B
    fun S => (hrk S).2
  exact ⟨C, hC.trans (theoremA_ratSize_le m r b _ _ hB (rank_colMatroid_le _)), heval⟩

end SignedTropical.Classes
