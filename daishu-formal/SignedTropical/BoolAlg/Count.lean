import SignedTropical.BoolAlg.Arith

/-!
# Population counts, sums, and circuits that output numbers

Gadgets over `BoolOp` on numbers carried in binary (`numR` of `BoolAlg/Arith.lean`), with exact
gate counts.

* **Population count** (`popcountB` on a list, `vecPopcountB` on a vector of `r` bits): the bits
  are split in halves, counted recursively, and the two counts added.  The count has
  `⌈log₂(r+1)⌉` bits (`Nat.size r`) and costs `popCost r = 11 (2r - 1 - ⌈log₂(r+1)⌉) ≤ 22 r`
  gates (`popCost_le`).
* **Sums** (`numSumB w` on `r` numbers of width `w`): the sum on `w + ⌈log₂(r+1)⌉` bits,
  `11 r (w + ⌈log₂(r+1)⌉)` gates.
* **Circuits that output numbers.**  A circuit run on carried bits carries the number it outputs,
  at the cost of its size (`runB_num`); if it outputs `f(S)` on the indicator vector of every `S`,
  for instance a rank circuit, then run on a carried vector `V` it carries `f` of the set of set
  entries of `V` (`runB_set`, a rank query), on any width `w` with `f < 2^w`
  (`runB_set_fit`).  An implementation of a number from the inputs is a circuit that outputs it
  in binary (`circuitOf_num`).
* **Independence tests** (`indepOfRankB`): a rank query `Fr` reading (context, set), fitted to
  `⌈log₂(m+1)⌉` bits and compared with the size of the set, `cR + popCost m + 5⌈log₂(m+1)⌉ + 1`
  gates (`indepOfRankB_impl`); it answers `[A independent in N]` at every context at which the
  query is the rank of `N` (`indepOfRank_correct`).  The one construction of this kind, used by
  the matroid intersection circuit (`Rainbow/MICircuit.lean`) and by transversal matroids.
-/

namespace SignedTropical.BoolAlg

open Finset

variable {n r : ℕ}

/-! ### Population count -/

/-- `⌈log₂(k+1)⌉ ≤ k`. -/
theorem size_le_self (k : ℕ) : Nat.size k ≤ k := Nat.size_le.2 Nat.lt_two_pow_self

/-- The gates of `popcountB` on `r` bits: `11 (2r - 1 - ⌈log₂(r+1)⌉)`. -/
def popCost (r : ℕ) : ℕ := 11 * (2 * r - 1 - Nat.size r)

/-- **A population count costs at most `22 r` gates** (`thm:D`, Step 2: `O(m)`). -/
theorem popCost_le (r : ℕ) : popCost r ≤ 22 * r := by
  unfold popCost; omega

/-- **Population count**: split the bits in halves, count each half, add the counts; the result
has `⌈log₂(r+1)⌉` bits for `r` input bits. -/
def popcountB : List (Arg n) → Bld BoolOp n (List (Arg n))
  | [] => fun gs => (gs, [])
  | [a] => fun gs => (gs, [a])
  | a :: b :: l => fun gs =>
    let p := popcountB ((a :: b :: l).take ((l.length + 2) / 2)) gs
    let q := popcountB ((a :: b :: l).drop ((l.length + 2) / 2)) p.1
    let s := numAddB (p.2, q.2) q.1
    (s.1, s.2.take (Nat.size (l.length + 2)))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- **Population count** of `L` bits: the number of set bits on `⌈log₂(L+1)⌉` bits, with
`popCost L` gates. -/
theorem popcountB_spec (L : ℕ) : ∀ {as : List (Arg n)} {A : (Fin n → Bool) → List Bool}
    {gs : List (Gate BoolOp n)}, as.length = L → DenL boolInterp gs as A →
      gs <+: (popcountB as gs).1 ∧ (popcountB as gs).1.length = gs.length + popCost L ∧
        (numR (Nat.size L)).rep (popcountB as gs).1 (popcountB as gs).2
          (fun x => (A x).count true) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  rintro (_ | ⟨a, _ | ⟨b, l⟩⟩) A gs hL hA
  · subst hL
    have h0 : ∀ x, A x = [] := fun x => List.length_eq_zero_iff.1 (hA.length_eq x)
    simp only [popcountB]
    exact ⟨List.prefix_refl _, by simp [popCost], rfl, A, hA, fun x => by simp [h0 x]⟩
  · subst hL
    simp only [popcountB]
    refine ⟨List.prefix_refl _, by simp [popCost], Nat.size_one.symm, A, hA, fun x => ?_⟩
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 (hA.length_eq x)
    show bitsVal (A x) = (A x).count true
    rw [hc]
    cases c <;> rfl
  · have hL2 : l.length + 2 = L := by simpa using hL
    simp only [popcountB]
    rw [hL2]
    set as := a :: b :: l with has
    set k := L / 2 with hk
    have hkL : k ≤ L - k := by omega
    have hsk := Nat.size_le_size hkL
    obtain ⟨hp₁, hl₁, hr₁⟩ := ih k (by omega) (as := as.take k) (A := fun x => (A x).take k)
      (gs := gs) (by simp only [List.length_take, has, List.length_cons]; omega) (denL_take hA k)
    obtain ⟨hp₂, hl₂, hr₂⟩ := ih (L - k) (by omega) (as := as.drop k)
      (A := fun x => (A x).drop k) (gs := (popcountB (as.take k) gs).1)
      (by simp only [List.length_drop, has, List.length_cons]; omega) ((denL_drop hA k).mono hp₁)
    obtain ⟨hp₃, hl₃, hr₃⟩ := numAddB_impl (n := n) (Nat.size k) (Nat.size (L - k))
      (gs := (popcountB (as.drop k) (popcountB (as.take k) gs).1).1)
      (s := ((popcountB (as.take k) gs).2, (popcountB (as.drop k) (popcountB (as.take k) gs).1).2))
      (T := fun x => (((A x).take k).count true, ((A x).drop k).count true))
      ⟨(numR _).mono hp₂ hr₁, hr₂⟩
    have hsz : Nat.size k + 1 = Nat.size L := size_div_two_add_one (by omega)
    have hmax : max (Nat.size k) (Nat.size (L - k)) = Nat.size (L - k) := max_eq_right hsk
    obtain ⟨-, -, hr₄⟩ := numTrunc_impl (n := n) (W := Nat.size L) (by rw [hmax]; omega) hr₃
    refine ⟨(hp₁.trans hp₂).trans hp₃, ?_, Rep.congr _ hr₄ fun x => ?_⟩
    · rw [hl₃, hl₂, hl₁, hmax]
      have h₁ := size_le_self k
      have h₂ := size_le_self (L - k)
      unfold popCost
      omega
    · have hlen : (A x).count true < 2 ^ Nat.size L :=
        lt_of_le_of_lt (List.count_le_length.trans (by rw [hA.length_eq x, hL]))
          (Nat.lt_size_self L)
      beta_reduce
      rw [← List.count_append, List.take_append_drop, Nat.mod_eq_of_lt hlen]

/-- **Population count of a vector** of `r` bits: `popCost r ≤ 22 r` gates, `⌈log₂(r+1)⌉` output
bits. -/
def vecPopcountB (v : Fin r → Arg n) : Bld BoolOp n (List (Arg n)) := popcountB (List.ofFn v)

/-- The `true` entries of `List.ofFn V` are the set entries of `V`. -/
theorem count_ofFn (V : Fin r → Bool) :
    (List.ofFn V).count true = (univ.filter fun i => V i = true).card := by
  rw [List.ofFn_eq_map, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
    ← filter_finRange_length]
  congr 1
  apply List.filter_congr
  intro i _
  simp

/-- **Population count of a vector** (`thm:D`, Step 2; `lem:augment`, Step 3, `|I|`): the
number of set entries of `r` bits, on `⌈log₂(r+1)⌉` bits, with `popCost r ≤ 22 r` gates. -/
theorem vecPopcountB_impl :
    Impl (vecR r) (numR (n := n) (Nat.size r)) vecPopcountB (popCost r)
      (fun V => (univ.filter fun i => V i = true).card) := by
  intro gs v V hv
  obtain ⟨hp, hl, hr⟩ := popcountB_spec r (List.length_ofFn) (denL_ofFn hv)
  exact ⟨hp, hl, Rep.congr _ hr fun x => count_ofFn (V x)⟩

/-! ### Sums -/

/-- Add the numbers `v 0, …, v (r-1)` to `acc`, truncating to `W` bits after each addition. -/
def numSumAccB (W : ℕ) : {r : ℕ} → (Fin r → List (Arg n)) → List (Arg n) →
    Bld BoolOp n (List (Arg n))
  | 0, _, acc => fun gs => (gs, acc)
  | _ + 1, v, acc => fun gs =>
    let p := numAddB (acc, v 0) gs
    numSumAccB W (fun i => v i.succ) (p.2.take W) p.1

/-- `numSumAccB`: `11 W` gates per number, the sum modulo `2 ^ W`. -/
theorem numSumAccB_spec {w W : ℕ} (hw : w ≤ W) : ∀ {r : ℕ} {v : Fin r → List (Arg n)}
    {acc : List (Arg n)} {V : (Fin n → Bool) → Fin r → ℕ} {S : (Fin n → Bool) → ℕ}
    {gs : List (Gate BoolOp n)}, (Rep.pi (Fin r) (numR w)).rep gs v V → (numR W).rep gs acc S →
      gs <+: (numSumAccB W v acc gs).1 ∧
        (numSumAccB W v acc gs).1.length = gs.length + r * (11 * W) ∧
        (numR W).rep (numSumAccB W v acc gs).1 (numSumAccB W v acc gs).2
          (fun x => (S x + ∑ i, V x i) % 2 ^ W)
  | 0, _, acc, V, S, gs, _, hS => ⟨List.prefix_refl _, by simp [numSumAccB],
      Rep.congr _ hS fun x => by simp [Nat.mod_eq_of_lt (numR_lt hS x)]⟩
  | r + 1, v, acc, V, S, gs, hv, hS => by
    obtain ⟨hp₁, hl₁, hr₁⟩ := numAddB_impl W w (s := (acc, v 0)) (T := fun x => (S x, V x 0))
      ⟨hS, hv 0⟩
    rw [max_eq_left hw] at hl₁ hr₁
    have hr₂ := numTrunc_impl (n := n) (w := W + 1) (W := W) (by omega) hr₁
    obtain ⟨hp₃, hl₃, hr₃⟩ := numSumAccB_spec hw (v := fun i => v i.succ)
      (V := fun x i => V x i.succ) (fun i => (numR w).mono hp₁ (hv i.succ)) hr₂.2.2
    refine ⟨hp₁.trans hp₃, hl₃.trans (by rw [hl₁]; ring), Rep.congr _ hr₃ fun x => ?_⟩
    simp only [Fin.sum_univ_succ]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

/-- **Sum of `r` numbers** of width `w`, on `w + ⌈log₂(r+1)⌉` bits:
`11 r (w + ⌈log₂(r+1)⌉)` gates. -/
def numSumB (w : ℕ) (v : Fin r → List (Arg n)) : Bld BoolOp n (List (Arg n)) :=
  numSumAccB (w + Nat.size r) v (List.replicate (w + Nat.size r) .const)

/-- **Sum of `r` numbers** of width `w` (`lem:observer`, Step 3): on `w + ⌈log₂(r+1)⌉`
bits, `11 r (w + ⌈log₂(r+1)⌉)` gates. -/
theorem numSumB_impl (w : ℕ) :
    Impl (Rep.pi (Fin r) (numR w)) (numR (n := n) (w + Nat.size r)) (numSumB w)
      (r * (11 * (w + Nat.size r))) (fun V => ∑ i, V i) := by
  intro gs v V hv
  have h0 : (numR (w + Nat.size r)).rep gs (List.replicate (w + Nat.size r) .const)
      (fun _ => 0) :=
    ⟨List.length_replicate, _, denL_replicate_const gs _,
      fun x => bitsVal_replicate_false _⟩
  obtain ⟨hp, hl, hr⟩ := numSumAccB_spec (Nat.le_add_right w (Nat.size r)) hv h0
  refine ⟨hp, hl, Rep.congr _ hr fun x => ?_⟩
  rw [zero_add]
  apply Nat.mod_eq_of_lt
  calc ∑ i, V x i ≤ ∑ _i : Fin r, 2 ^ w := Finset.sum_le_sum fun i _ => (numR_lt (hv i) x).le
    _ = r * 2 ^ w := by simp
    _ < 2 ^ Nat.size r * 2 ^ w := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self r)
        (Nat.two_pow_pos w)
    _ = 2 ^ (w + Nat.size r) := by rw [pow_add, mul_comm]

/-! ### Circuits that output numbers -/

/-- **Running a circuit that outputs a number in binary**: `C.size` gates. -/
theorem runB_num {k : ℕ} (C : Circuit BoolOp k) :
    Impl (vecR k) (numR (n := n) C.outs.length) (runB C) C.size
      (fun V => bitsVal (C.eval boolInterp V)) :=
  fun _ _ _ hv =>
    let h := runB_impl boolInterp C hv
    ⟨h.1, h.2.1, h.2.2.1, _, h.2.2.2, fun _ => rfl⟩

/-- **Queries to a circuit on sets**, for instance rank queries: if `C` outputs `f(S)` in binary
from the indicator vector of every `S`, then `C` run on a carried vector `V` carries `f` of the
set of set entries of `V`, at the cost of `C.size` gates. -/
theorem runB_set {k : ℕ} (C : Circuit BoolOp k) {f : Finset (Fin k) → ℕ}
    (hC : ∀ S, bitsVal (C.eval boolInterp (indicator S)) = f S) :
    Impl (vecR k) (numR (n := n) C.outs.length) (runB C) C.size
      (fun V => f (univ.filter fun i => V i = true)) :=
  (runB_num C).congr fun V => by rw [← hC, indicator_filter]

/-- **Queries on `w` bits**: if `C` outputs `f(S) < 2^w` in binary from the indicator vector of
every `S`, then `C` run on a carried vector `V`, its outputs fitted to `w` bits, carries `f` of
the set of set entries of `V`, at the cost of `C.size` gates.  For a rank circuit of a matroid
on `Fin k`, `w = ⌈log₂(k+1)⌉` (`Nat.size k`) bits suffice, however many outputs `C` has. -/
theorem runB_set_fit {k w : ℕ} (C : Circuit BoolOp k) {f : Finset (Fin k) → ℕ}
    (hC : ∀ S, bitsVal (C.eval boolInterp (indicator S)) = f S) (hw : ∀ S, f S < 2 ^ w) :
    Impl (vecR k) (numR (n := n) w) (seqB (runB C) (pureB (fit w))) C.size
      (fun V => f (univ.filter fun i => V i = true)) :=
  ((runB_set C hC).comp numFit_impl).cost (Nat.add_zero _) |>.congr fun _ =>
    Nat.mod_eq_of_lt (hw _)

/-! ### Independence tests from rank queries -/

section IndepTest

variable {m : ℕ} {σ τ : Type} {Rc : Rep BoolOp Bool n σ τ}

/-- The value of the independence oracle from a rank query `Fr`:
`[Fr(a, A) mod 2^⌈log₂(m+1)⌉ = |A|]`. -/
def indepOfRankV (Fr : τ × (Fin m → Bool) → ℕ) (t : τ × (Fin m → Bool)) : Bool :=
  decide (Fr t % 2 ^ Nat.size m = (univ.filter fun i => t.2 i = true).card)

/-- **The independence oracle from a rank query** `bR` reading (context, set): its value fitted to
`⌈log₂(m+1)⌉` bits, compared with the size of the set (`lem:observer`, Step 3, "an independence
test `[r_{N_G}(J) = |J|]`"; `cor:transversal`, Step 3). -/
def indepOfRankB (bR : σ × (Fin m → Arg n) → Bld BoolOp n (List (Arg n))) :
    σ × (Fin m → Arg n) → Bld BoolOp n (Arg n) :=
  seqB (pairB (seqB bR (pureB (fit (Nat.size m)))) fun s => vecPopcountB s.2) numEqB

/-- **An independence oracle from a rank query**: if `bR` computes `Fr` from (context, set) with
`cR` gates, then `indepOfRankB bR` computes `indepOfRankV Fr`, that is
`[Fr mod 2^⌈log₂(m+1)⌉ = |A|]`, with `cR + popCost m + 5⌈log₂(m+1)⌉ + 1` gates. -/
theorem indepOfRankB_impl {bR : σ × (Fin m → Arg n) → Bld BoolOp n (List (Arg n))} {w cR : ℕ}
    {Fr : τ × (Fin m → Bool) → ℕ} (hR : Impl (Rc.prod (vecR m)) (numR w) bR cR Fr) :
    Impl (Rc.prod (vecR m)) bitR (indepOfRankB bR) (cR + popCost m + (5 * Nat.size m + 1))
      (indepOfRankV Fr) := by
  have h := (((hR.comp (numFit_impl (W := Nat.size m))).cost (Nat.add_zero cR)).pair
    (vecPopcountB_impl.pre (R := Rc.prod (vecR m)) (g := Prod.snd) (G := Prod.snd)
      fun _ _ _ hs => hs.2)).comp (numEqB_impl (Nat.size m) (Nat.size m))
  exact h.cost (by rw [max_self])

open Classical in
/-- **The oracle from a rank query answers independence** at every context `a` at which the
query is the rank of `N`. -/
theorem indepOfRank_correct {Fr : τ × (Fin m → Bool) → ℕ} {N : Matroid (Fin m)} {a : τ}
    (hFr : ∀ S : Finset (Fin m), Fr (a, indicator S) = rk N S) (A : Fin m → Bool) :
    indepOfRankV Fr (a, A) = decide (N.Indep ↑(univ.filter fun i => A i = true)) := by
  unfold indepOfRankV
  set S := univ.filter fun i => A i = true
  have hA : A = indicator S := (indicator_filter A).symm
  rw [hA, hFr, Nat.mod_eq_of_lt (rk_lt_two_pow N S)]
  refine decide_eq_decide.2 ?_
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _), ← coe_rk,
    Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj]

end IndepTest

/-! ### Back to circuits -/

/-- **An implementation of a number from the inputs is a circuit** of size `c` that outputs it
in binary on `w` bits. -/
theorem circuitOf_num {b : (Fin n → Arg n) → Bld BoolOp n (List (Arg n))} {w c : ℕ}
    {F : (Fin n → Bool) → ℕ} (h : Impl (vecR n) (numR w) b c F) :
    (circuitOf b).size = c ∧ (circuitOf b).outs.length = w ∧
      ∀ x, bitsVal ((circuitOf b).eval boolInterp x) = F x := by
  obtain ⟨-, hl, hL, A, hA, hv⟩ := h (gs := []) (s := fun i => .input i) (T := fun x => x)
    fun i => den_input [] i
  exact ⟨by simpa [Circuit.size, circuitOf] using hl, hL,
    fun x => (congrArg bitsVal (hA.eval x)).trans (hv x)⟩

end SignedTropical.BoolAlg
