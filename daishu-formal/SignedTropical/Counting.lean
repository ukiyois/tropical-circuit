import SignedTropical.Converse
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card

/-!
# Corollary D: most matroids need large signed circuits

`docs/research-direction-2026-10-11.md`, Section 3.2, Corollary D: there are
`2^{2^m / poly(m)}` matroids on `m` elements and `2^{O(s log s)}` Boolean circuits of size
`s`, and Theorem B transfers the bound.

The part proved here:

* **Counting Boolean circuits** (`ncard_computed_le`): the functions
  `S ↦ bitsVal(B(1_S))` with values below `2^L` computed by Boolean circuits of size at
  most `s` number at most `codeCount m s L = (s+1) (3 (m+s+1)²)^s (m+s+1)^L`.  Every such
  circuit is equivalent to a decoded code (`exists_code`): operands are renumbered into
  `m + 1 + s` symbols, a reference to a wire that does not exist becomes the constant
  (which it reads anyway), and the outputs are cut or padded to `L` bits.
* **Matroids are determined by their rank function** (`eq_of_eRk_eq`).
* **Corollary D, counting form** (`corollaryD_count`): at most
  `codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉` matroids on `Fin m` have a signed tropical
  circuit of size at most `S` computing `h_M` on `{0,1}^m` (Theorem B and the two facts
  above).
* **Corollary D** (`corollaryD`): given an external lower bound `N` on the number of
  matroids on `Fin m` (Knuth's bound gives `log₂ N ≥ 2^m / poly(m)`), if
  `codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉ < N` then some matroid has no signed circuit of
  size at most `S` computing `h_M`, not even on `{0,1}^m`.  The lower bound on the number of
  matroids is the hypothesis `hN`.

Since `log₂ codeCount m s L = O(s log(m + s) + L log(m + s))`, the condition holds for
`S = 2^{c m}` with a small constant `c > 0` and large `m`; this asymptotic reading is not
formalized.
-/

open Finset

namespace SignedTropical

variable {m : ℕ}

/-! ### Codes for Boolean circuits -/

/-- Decode an operand symbol: `0, …, m-1` are the inputs, `m` the constant, `m + 1 + j`
wire `j`. -/
def decArg (m s : ℕ) (c : Fin (m + 1 + s)) : Arg m :=
  if h : (c : ℕ) < m then .input ⟨c, h⟩ else if (c : ℕ) = m then .const else .wire (c - m - 1)

/-- Encode an operand; a wire with index at least `s` becomes the constant. -/
def encArg (m s : ℕ) : Arg m → Fin (m + 1 + s)
  | .input i => ⟨i, by omega⟩
  | .const => ⟨m, by omega⟩
  | .wire j => if h : j < s then ⟨m + 1 + j, by omega⟩ else ⟨m, by omega⟩

/-- Operand normalization: what `decArg` gives back from `encArg`. -/
def normArg (s : ℕ) : Arg m → Arg m
  | .wire j => if j < s then .wire j else .const
  | a => a

theorem decArg_encArg (s : ℕ) (a : Arg m) : decArg m s (encArg m s a) = normArg s a := by
  cases a with
  | input i => simp [decArg, encArg, normArg]
  | const => simp [decArg, encArg, normArg]
  | wire j =>
    by_cases h : j < s
    · simp only [encArg, h, dif_pos, decArg, normArg, if_pos]
      rw [dif_neg (by omega), if_neg (by omega)]
      congr 1; omega
    · simp [encArg, h, decArg, normArg]

/-- A code: the number of gates used, `s` gate codes, and `L` output codes. -/
abbrev Code (m s L : ℕ) :=
  Fin (s + 1) × (Fin s → BoolOp × Fin (m + 1 + s) × Fin (m + 1 + s)) × (Fin L → Fin (m + 1 + s))

/-- The circuit of a code. -/
def decode {s L : ℕ} (c : Code m s L) : Circuit BoolOp m :=
  ⟨((List.finRange s).take c.1).map fun i =>
      ⟨(c.2.1 i).1, decArg m s (c.2.1 i).2.1, decArg m s (c.2.1 i).2.2⟩,
    (List.finRange L).map fun j => decArg m s (c.2.2 j)⟩

/-- The number of codes. -/
def codeCount (m s L : ℕ) : ℕ := (s + 1) * (3 * (m + 1 + s) ^ 2) ^ s * (m + 1 + s) ^ L

theorem card_code (s L : ℕ) : Fintype.card (Code m s L) = codeCount m s L := by
  have h3 : Fintype.card BoolOp = 3 := card_boolOp
  simp [Code, codeCount, Fintype.card_prod, h3, sq, mul_assoc]

/-- Normalizing the operands of a gate list with at most `s` gates does not change any
wire: a normalized operand is a wire with index at least `s`, which does not exist yet. -/
theorem wires_normArg {s : ℕ} (x : Fin m → Bool) :
    ∀ gs : List (Gate BoolOp m), gs.length ≤ s →
      wires boolInterp x (gs.map fun g => ⟨g.op, normArg s g.a, normArg s g.b⟩)
        = wires boolInterp x gs := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro; rfl
  | append_singleton gs g ih =>
    intro hlen
    simp only [List.length_append, List.length_singleton] at hlen
    rw [List.map_append, List.map_singleton, wires_concat, wires_concat, ih (by omega)]
    have hread : ∀ a : Arg m, (normArg s a).read boolInterp x (wires boolInterp x gs)
        = a.read boolInterp x (wires boolInterp x gs) := by
      intro a
      cases a with
      | input i => rfl
      | const => rfl
      | wire j =>
        simp only [normArg]
        split_ifs with h
        · rfl
        · simp only [Arg.read]
          rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [Gate.eval, hread]

theorem read_normArg {s : ℕ} (x : Fin m → Bool) {gs : List (Gate BoolOp m)} (hlen : gs.length ≤ s)
    (a : Arg m) :
    (normArg s a).read boolInterp x (wires boolInterp x gs)
      = a.read boolInterp x (wires boolInterp x gs) := by
  cases a with
  | input i => rfl
  | const => rfl
  | wire j =>
    simp only [normArg]
    split_ifs with h
    · rfl
    · simp only [Arg.read]
      rw [List.getD_eq_default _ _ (by simp; omega)]

theorem bitsVal_replicate_false (k : ℕ) : bitsVal (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem bitsVal_append_false (l : List Bool) (k : ℕ) :
    bitsVal (l ++ List.replicate k false) = bitsVal l := by
  induction l with
  | nil => simpa using bitsVal_replicate_false k
  | cons b l ih => simp [ih]

theorem bitsVal_ofFn_getD (L : ℕ) (l : List Bool) (h : bitsVal l < 2 ^ L) :
    bitsVal (List.ofFn fun j : Fin L => l.getD j false) = bitsVal l := by
  have heq : (List.ofFn fun j : Fin L => l.getD j false)
      = l.take L ++ List.replicate (L - l.length) false := by
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    have hiL : i < L := by simpa using h₁
    simp only [List.getElem_ofFn]
    by_cases hi : i < l.length
    · rw [List.getD_eq_getElem _ _ hi, List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by simp; omega)]
      simp
  rw [heq, bitsVal_append_false, bitsVal_take_of_lt h]

/-- **Every small circuit has a code** computing the same values, when these are below
`2^L`. -/
theorem exists_code {s L : ℕ} {B : Circuit BoolOp m} (hB : B.size ≤ s)
    (hval : ∀ S, bitsVal (B.eval boolInterp (indicator S)) < 2 ^ L) :
    ∃ c : Code m s L, ∀ S, bitsVal ((decode c).eval boolInterp (indicator S))
      = bitsVal (B.eval boolInterp (indicator S)) := by
  have hsize : B.gates.length ≤ s := hB
  let gcode : Fin s → BoolOp × Fin (m + 1 + s) × Fin (m + 1 + s) := fun i =>
    if h : (i : ℕ) < B.gates.length then
      ((B.gates[i]).op, encArg m s (B.gates[i]).a, encArg m s (B.gates[i]).b)
    else (.and, encArg m s .const, encArg m s .const)
  let ocode : Fin L → Fin (m + 1 + s) := fun j => encArg m s (B.outs.getD j .const)
  let c : Code m s L := (⟨B.gates.length, Nat.lt_succ_of_le hsize⟩, gcode, ocode)
  have hgates : (decode c).gates = B.gates.map fun g => ⟨g.op, normArg s g.a, normArg s g.b⟩ := by
    apply List.ext_getElem
    · simp [decode, c]; omega
    · intro i h₁ h₂
      simp only [decode, c, List.getElem_map, List.getElem_take, List.getElem_finRange]
      simp only [List.length_map] at h₂
      simp [gcode, h₂, decArg_encArg]
  have heval : ∀ x, (decode c).eval boolInterp x
      = List.ofFn fun j : Fin L => (B.eval boolInterp x).getD j false := by
    intro x
    simp only [Circuit.eval]
    rw [hgates, wires_normArg _ _ hsize]
    apply List.ext_getElem (by simp [decode, c])
    intro j h₁ h₂
    have hjL : j < L := by simpa using h₂
    simp only [decode, c, List.getElem_map, List.getElem_finRange, List.getElem_ofFn, ocode,
      decArg_encArg, read_normArg _ hsize, Fin.val_cast]
    by_cases hj : j < B.outs.length
    · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj),
        List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hj)]
      rfl
  exact ⟨c, fun S => by rw [heval, bitsVal_ofFn_getD L _ (hval S)]⟩

/-- **Counting functions computed by small Boolean circuits.** -/
theorem ncard_computed_le (s L : ℕ) :
    Set.ncard {f : Finset (Fin m) → ℕ | (∀ S, f S < 2 ^ L) ∧ ∃ B : Circuit BoolOp m,
      B.size ≤ s ∧ ∀ S, bitsVal (B.eval boolInterp (indicator S)) = f S} ≤ codeCount m s L := by
  let F : Code m s L → Finset (Fin m) → ℕ := fun c S =>
    bitsVal ((decode c).eval boolInterp (indicator S))
  have hsub : {f : Finset (Fin m) → ℕ | (∀ S, f S < 2 ^ L) ∧ ∃ B : Circuit BoolOp m,
      B.size ≤ s ∧ ∀ S, bitsVal (B.eval boolInterp (indicator S)) = f S} ⊆ Set.range F := by
    rintro f ⟨hlt, B, hB, hf⟩
    obtain ⟨c, hc⟩ := exists_code (L := L) hB fun S => (hf S).symm ▸ hlt S
    exact ⟨c, funext fun S => (hc S).trans (hf S)⟩
  calc _ ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub (Set.finite_range F)
    _ ≤ (Set.univ : Set (Code m s L)).ncard := by
        rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
    _ = codeCount m s L := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_code]

/-! ### Matroids and their rank functions -/

/-- A matroid on `Fin m` with ground set `univ` is determined by its rank function. -/
theorem eq_of_eRk_eq {M M' : Matroid (Fin m)} (hE : M.E = Set.univ) (hE' : M'.E = Set.univ)
    (h : ∀ S : Finset (Fin m), M.eRk (S : Set (Fin m)) = M'.eRk (S : Set (Fin m))) : M = M' := by
  refine Matroid.ext_indep (hE.trans hE'.symm) fun I _ => ?_
  obtain ⟨F, rfl⟩ := exists_finset I
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _),
    Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _), h F]


/-- The matroids on `Fin m` with ground set `univ` form a finite set. -/
theorem finite_matroids : {M : Matroid (Fin m) | M.E = Set.univ}.Finite := by
  classical
  refine Set.Finite.of_injOn (f := fun M : Matroid (Fin m) => fun S : Finset (Fin m) =>
    decide (M.Indep (S : Set (Fin m)))) (t := Set.univ) (fun _ _ => trivial) ?_ Set.finite_univ
  intro M hM M' hM' h
  refine Matroid.ext_indep (hM.trans hM'.symm) fun I _ => ?_
  obtain ⟨F, rfl⟩ := exists_finset I
  have := congrFun h F
  simpa using this

theorem computed_finite (s L : ℕ) :
    {f : Finset (Fin m) → ℕ | (∀ S, f S < 2 ^ L) ∧ ∃ B : Circuit BoolOp m,
      B.size ≤ s ∧ ∀ S, bitsVal (B.eval boolInterp (indicator S)) = f S}.Finite := by
  refine (Set.finite_range fun c : Code m s L => fun S =>
    bitsVal ((decode c).eval boolInterp (indicator S))).subset ?_
  rintro f ⟨hlt, B, hB, hf⟩
  obtain ⟨c, hc⟩ := exists_code (L := L) hB fun S => (hf S).symm ▸ hlt S
  exact ⟨c, funext fun S => (hc S).trans (hf S)⟩

/-- **Corollary D, counting form.**  At most `codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉`
matroids on `Fin m` (ground set `univ`) have a signed tropical circuit of size at most `S`
computing `h_M` on `{0,1}^m`. -/
theorem corollaryD_count (m S : ℕ) :
    Set.ncard {M : Matroid (Fin m) | M.E = Set.univ ∧ ∃ C : Circuit STOp m, C.size ≤ S ∧
      ∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
        = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]}
      ≤ codeCount m (15 * S ^ 2 + 40 * S) (Nat.size m) := by
  refine (Set.ncard_le_ncard_of_injOn (fun M : Matroid (Fin m) => fun T : Finset (Fin m) => rk M T)
    ?_ ?_ (computed_finite _ _)).trans (ncard_computed_le _ _)
  · rintro M ⟨hE, C, hC, hcomp⟩
    obtain ⟨B, hBsize, hB⟩ := theoremB M hE C hcomp
    refine ⟨fun T => rk_lt_two_pow M T, B, hBsize.trans ?_, fun T => ?_⟩
    · have h1 : C.size ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hC 2
      omega
    · have := hB T
      rw [← coe_rk] at this
      exact_mod_cast this
  · rintro M ⟨hE, -⟩ M' ⟨hE', -⟩ h
    exact eq_of_eRk_eq hE hE' fun T => by
      rw [← coe_rk, ← coe_rk]
      exact congrArg _ (congrFun h T)

/-- **Corollary D.**  Let `N` be a lower bound on the number of matroids on `Fin m` (an
external input: Knuth's construction gives `log₂ N ≥ 2^m / poly(m)`).  If
`codeCount m (15 S² + 40 S) ⌈log₂(m+1)⌉ < N`, some matroid on `Fin m` has no signed
tropical circuit of size at most `S` computing `h_M`, not even on `{0,1}^m`. -/
theorem corollaryD (m S N : ℕ) (hN : N ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ})
    (hlt : codeCount m (15 * S ^ 2 + 40 * S) (Nat.size m) < N) :
    ∃ M : Matroid (Fin m), M.E = Set.univ ∧ ∀ C : Circuit STOp m,
      (∀ T : Finset (Fin m), C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
        = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]) → S < C.size := by
  by_contra hcon
  push Not at hcon
  have hsub : {M : Matroid (Fin m) | M.E = Set.univ} ⊆ {M : Matroid (Fin m) | M.E = Set.univ ∧
      ∃ C : Circuit STOp m, C.size ≤ S ∧ ∀ T : Finset (Fin m),
        C.eval (stInterp ℝ) (fun e => if e ∈ T then 1 else 0)
          = [maxBasisWeight M (fun e => if e ∈ T then 1 else 0)]} := by
    intro M hM
    obtain ⟨C, hC, hle⟩ := hcon M hM
    exact ⟨hM, C, hle, hC⟩
  have := (Set.ncard_le_ncard hsub (finite_matroids.subset fun M hM => hM.1)).trans
    (corollaryD_count m S)
  omega

end SignedTropical
