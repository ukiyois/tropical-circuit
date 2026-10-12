import SignedTropical.BoolAlg.Rel

/-!
# Least-index shortest paths

The choice of a path in one round of the augmenting path algorithm (`lem:augment`, Step 1: "the
sink of least index in the first layer containing a sink, the predecessors of least index"),
for any relation `G` on `Fin r`, set of sources `S` and set of targets `Y`:

* `predV G S i y`: the in-neighbour of least index of `y` in layer `i` (and `y` if there is none);
  `backV G S d y`: the path chosen backwards from `y` in layer `d` (`backV_self`, `backV_pred`);
  this is `backPath` of `Rainbow/Exchange.lean` for the exchange graph (`BoolAlg/ExchangeBits`);
* `pathSet G S Y`: if some layer meets `Y`, the vertices `backV d y i`, `i ≤ d`, for the first
  layer `d` meeting `Y` and the least element `y` of `Y` in it; otherwise `∅`;
* `pathB` computes the bits of `pathSet G S Y` from `(G, S, Y)` with
  `pathCost r = 8r³ + 7r² + 9r + 3` gates (`pathB_impl`, `pathV_eq_true_iff`): the layers
  `0, …, r`, least-index selections of the first layer meeting `Y`, of the least element of `Y`
  in each layer and of the predecessors, and a downward pass `cur_i = T_i ∪ Pred_i(cur_{i+1})`
  from `i = r` to `0`, whose union is the path.
-/

namespace SignedTropical.BoolAlg

open Finset

variable {n r : ℕ}

/-- Layer `d + 1` is layer `d` together with its out-neighbours. -/
theorem layerV_succ_eq_true_iff {G : Fin r → Fin r → Bool} {S : Fin r → Bool} {d : ℕ}
    {v : Fin r} : layerV G S (d + 1) v = true ↔
      layerV G S d v = true ∨ ∃ u, layerV G S d u = true ∧ G u v = true := by
  rw [layerV_succ]; simp [bfsStep]

/-! ### Paths chosen backwards -/

section Values

variable (G : Fin r → Fin r → Bool) (S Y : Fin r → Bool)

/-- The elements of `Y` in layer `d`. -/
def hitV (d : ℕ) (y : Fin r) : Bool := layerV G S d y && Y y

/-- The in-neighbour of least index of `y` in layer `i`, and `y` if there is none. -/
def predV (i : ℕ) (y : Fin r) : Fin r :=
  if h : (univ.filter fun u => (layerV G S i u && G u y) = true).Nonempty then
    (univ.filter fun u => (layerV G S i u && G u y) = true).min' h
  else y

/-- The path chosen backwards from `y` in layer `d`: `backV d y d = y` and
`backV d y i = predV i (backV d y (i + 1))` for `i < d` (`backV_self`, `backV_pred`). -/
def backV : ℕ → Fin r → ℕ → Fin r
  | 0, y, _ => y
  | d + 1, y, i => if i ≤ d then backV d (predV G S d y) i else y

/-- Some layer meets `Y`. -/
def Hits : Prop := ∃ d y, hitV G S Y d y = true

/-- The least element of `Y` in the first layer meeting `Y`. -/
def firstY (h : Hits G S Y) : Fin r :=
  (univ.filter fun y => hitV G S Y (Nat.find h) y = true).min'
    (let ⟨y, hy⟩ := Nat.find_spec h; ⟨y, mem_filter.2 ⟨mem_univ y, hy⟩⟩)

open Classical in
/-- **The least-index shortest path** from `S` to `Y`: if some layer meets `Y`, the vertices
`backV d y i` with `i ≤ d`, for the first layer `d` meeting `Y` and the least element `y` of `Y`
in it; otherwise `∅`. -/
noncomputable def pathSet : Finset (Fin r) :=
  if h : Hits G S Y then (range (Nat.find h + 1)).image (backV G S (Nat.find h) (firstY G S Y h))
  else ∅

/-- The target bits: `targetV d` is the one-hot vector of the least element of `Y` in layer `d`
if `d` is the first layer meeting `Y`, and empty otherwise (`targetV_eq`). -/
def targetV (d : Fin (r + 1)) (y : Fin r) : Bool :=
  leadV (fun e : Fin (r + 1) => decide (∃ y, hitV G S Y e y = true)) d && leadV (hitV G S Y d) y

/-- The predecessor bits: `predHotV i y` is the one-hot vector of the in-neighbour of least
index of `y` in layer `i` (`predV_spec`). -/
def predHotV (i : ℕ) (y : Fin r) : Fin r → Bool :=
  leadV fun u => layerV G S i u && G u y

end Values

/-- One round of the downward pass, for the layer `i < r`: with `c = T_i ∪ P_i(cur)`, the state
`(cur, acc)` becomes `(c, acc ∪ c)`. -/
def downStep (P : Fin r → Fin r → Fin r → Bool) (T : Fin (r + 1) → Fin r → Bool) (i : ℕ)
    (s : (Fin r → Bool) × (Fin r → Bool)) : (Fin r → Bool) × (Fin r → Bool) :=
  if h : i < r then
    (fun u => T ⟨i, by omega⟩ u || decide (∃ y, s.1 y = true ∧ P ⟨i, h⟩ y u = true),
      fun u => s.2 u || (T ⟨i, by omega⟩ u || decide (∃ y, s.1 y = true ∧ P ⟨i, h⟩ y u = true)))
  else s

/-- The downward pass from `(T_r, T_r)` through the layers `r - 1, …, 0`; the result is the union
of the `cur_i`. -/
def downV (P : Fin r → Fin r → Fin r → Bool) (T : Fin (r + 1) → Fin r → Bool) : Fin r → Bool :=
  ((List.range r).reverse.foldl (fun s i => downStep P T i s) (T (Fin.last r), T (Fin.last r))).2

/-- The value of the path gadget. -/
def pathV (G : Fin r → Fin r → Bool) (S Y : Fin r → Bool) : Fin r → Bool :=
  downV (fun i : Fin r => predHotV G S i) (targetV G S Y)

section Proofs

variable {G : Fin r → Fin r → Bool} {S Y : Fin r → Bool}

/-- The path chosen backwards from `y` in layer `d` ends at `y`. -/
theorem backV_self (d : ℕ) (y : Fin r) : backV G S d y d = y := by
  cases d <;> simp [backV]

/-- Each vertex of the path is the predecessor of least index of the next one. -/
theorem backV_pred {d i : ℕ} (hi : i < d) (y : Fin r) :
    backV G S d y i = predV G S i (backV G S d y (i + 1)) := by
  induction d generalizing y with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ d ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simp only [backV, if_pos hi.le, if_pos (show i + 1 ≤ d by omega)]
      exact ih hi _
    · simp [backV, backV_self]

/-- If `y` lies in layer `i + 1` but not in layer `i`, then `predV i y` is an in-neighbour of
`y` in layer `i`, and `predHotV i y` is its one-hot vector. -/
theorem predV_spec {i : ℕ} {y : Fin r} (h : layerV G S (i + 1) y = true)
    (h' : layerV G S i y = false) :
    layerV G S i (predV G S i y) = true ∧ G (predV G S i y) y = true ∧
      ∀ u, predHotV G S i y u = decide (u = predV G S i y) := by
  have hne : (univ.filter fun u => (layerV G S i u && G u y) = true).Nonempty := by
    rcases layerV_succ_eq_true_iff.1 h with h | ⟨u, hu, huy⟩
    · exact absurd h (by simp [h'])
    · exact ⟨u, by simp [hu, huy]⟩
  have hp : predV G S i y = (univ.filter fun u => (layerV G S i u && G u y) = true).min' hne :=
    dif_pos hne
  have hmem := mem_filter.1 (min'_mem _ hne)
  rw [Bool.and_eq_true, ← hp] at hmem
  exact ⟨hmem.2.1, hmem.2.2, fun u => (leadV_eq_min' hne u).trans (by rw [hp])⟩

/-- Along the path chosen backwards from an element `y` of distance exactly `d`, the vertex
`backV d y i` has distance exactly `i`. -/
theorem backV_layer {d : ℕ} {y : Fin r} (hd : layerV G S d y = true)
    (hmin : ∀ j < d, layerV G S j y = false) :
    ∀ i ≤ d, layerV G S i (backV G S d y i) = true ∧
      ∀ j < i, layerV G S j (backV G S d y i) = false := by
  have key : ∀ l ≤ d, layerV G S (d - l) (backV G S d y (d - l)) = true ∧
      ∀ j < d - l, layerV G S j (backV G S d y (d - l)) = false := by
    intro l hl
    induction l with
    | zero => simpa [backV_self] using ⟨hd, hmin⟩
    | succ l ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [show d - l = d - (l + 1) + 1 by omega] at h1 h2
      rw [backV_pred (show d - (l + 1) < d by omega)]
      obtain ⟨hp1, hp2, -⟩ := predV_spec h1 (h2 _ (by omega))
      refine ⟨hp1, fun j hj => ?_⟩
      by_contra hc
      have := layerV_succ_eq_true_iff.2 (Or.inr ⟨_, by simpa using hc, hp2⟩)
      rw [h2 (j + 1) (by omega)] at this
      exact Bool.false_ne_true this
  intro i hi
  have := key (d - i) (by omega)
  rwa [show d - (d - i) = i by omega] at this

/-! ### The first layer meeting `Y` -/

/-- The least element of `Y` in the first layer meeting `Y` lies in that layer and in `Y`. -/
theorem firstY_mem (h : Hits G S Y) :
    layerV G S (Nat.find h) (firstY G S Y h) = true ∧ Y (firstY G S Y h) = true := by
  have := (mem_filter.1 (min'_mem (univ.filter fun y => hitV G S Y (Nat.find h) y = true)
    (let ⟨y, hy⟩ := Nat.find_spec h; ⟨y, mem_filter.2 ⟨mem_univ y, hy⟩⟩))).2
  rw [hitV, Bool.and_eq_true] at this
  exact this

/-- The first layer meeting `Y` is at most `r`. -/
theorem find_le (h : Hits G S Y) : Nat.find h ≤ r := by
  obtain ⟨hm1, hm2⟩ := firstY_mem h
  exact Nat.find_min' h ⟨firstY G S Y h, by rw [hitV, layerV_le_card _ hm1, hm2]; rfl⟩

/-- The least element of `Y` in the first layer meeting `Y` has distance exactly that layer. -/
theorem firstY_layer (h : Hits G S Y) :
    layerV G S (Nat.find h) (firstY G S Y h) = true ∧
      ∀ j < Nat.find h, layerV G S j (firstY G S Y h) = false := by
  obtain ⟨hm1, hm2⟩ := firstY_mem h
  refine ⟨hm1, fun j hj => ?_⟩
  by_contra hc
  exact Nat.find_min h hj ⟨firstY G S Y h, by rw [hitV, eq_true_of_ne_false hc, hm2]; rfl⟩

/-- **The targets**: `targetV d y` holds iff `d` is the first layer meeting `Y` and `y` the least
element of `Y` in it. -/
theorem targetV_eq (h : Hits G S Y) (d : Fin (r + 1)) (y : Fin r) :
    targetV G S Y d y = (decide ((d : ℕ) = Nat.find h) && decide (y = firstY G S Y h)) := by
  rw [targetV, leadV_eq_find h (by have := find_le h; omega) d]
  by_cases hd : (d : ℕ) = Nat.find h
  · simp only [hd, decide_true, Bool.true_and]
    exact leadV_eq_min' _ y
  · simp [hd]

/-- If no layer meets `Y`, the target bits are empty. -/
theorem targetV_of_not_hits (h : ¬Hits G S Y) (d : Fin (r + 1)) (y : Fin r) :
    targetV G S Y d y = false := by
  rw [targetV, leadV_of_forall_false (fun e => ?_) d, Bool.false_and]
  simp only [decide_eq_false_iff_not, not_exists]
  exact fun y hy => h ⟨e, y, hy⟩

/-! ### The downward pass -/

/-- A round of the downward pass for a layer `i < r`. -/
theorem downStep_of_lt {P : Fin r → Fin r → Fin r → Bool} {T : Fin (r + 1) → Fin r → Bool}
    {i : ℕ} (hi : i < r) (s : (Fin r → Bool) × (Fin r → Bool)) :
    downStep P T i s =
      (fun u => T ⟨i, by omega⟩ u || decide (∃ y, s.1 y = true ∧ P ⟨i, hi⟩ y u = true),
        fun u => s.2 u ||
          (T ⟨i, by omega⟩ u || decide (∃ y, s.1 y = true ∧ P ⟨i, hi⟩ y u = true))) :=
  dif_pos hi

/-- The downward pass through the layers `k - 1, …, 0` takes a state `(C k, A k)` to
`(C 0, A 0)` when each round takes `(C (i + 1), A (i + 1))` to `(C i, A i)`. -/
theorem foldl_downStep {P : Fin r → Fin r → Fin r → Bool} {T : Fin (r + 1) → Fin r → Bool}
    {C A : ℕ → Fin r → Bool} (hstep : ∀ i < r, downStep P T i (C (i + 1), A (i + 1)) = (C i, A i))
    {k : ℕ} (hk : k ≤ r) :
    (List.range k).reverse.foldl (fun s i => downStep P T i s) (C k, A k) = (C 0, A 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, hstep k (by omega)]
    exact ih (by omega)

/-- The downward pass ends in `A 0` when each round takes `(C (i + 1), A (i + 1))` to
`(C i, A i)` and the initial state is `(C r, A r)`. -/
theorem downV_eq {P : Fin r → Fin r → Fin r → Bool} {T : Fin (r + 1) → Fin r → Bool}
    {C A : ℕ → Fin r → Bool} (hstep : ∀ i < r, downStep P T i (C (i + 1), A (i + 1)) = (C i, A i))
    (hC : C r = T (Fin.last r)) (hA : A r = T (Fin.last r)) : downV P T = A 0 := by
  have h0 : (T (Fin.last r), T (Fin.last r)) = (C r, A r) := by rw [hC, hA]
  rw [downV, h0, foldl_downStep hstep le_rfl]

/-- **The path gadget computes the least-index shortest path.** -/
theorem pathV_eq_true_iff (u : Fin r) : pathV G S Y u = true ↔ u ∈ pathSet G S Y := by
  by_cases h : Hits G S Y
  · -- `cur_i` marks `backV D y₀ i` for `i ≤ D`, `acc_i` the `backV D y₀ j` with `i ≤ j ≤ D`
    set D := Nat.find h with hD
    set bp := backV G S D (firstY G S Y h) with hbp
    have hDr : D ≤ r := find_le h
    have hlay := backV_layer (firstY_layer h).1 (firstY_layer h).2
    have hpred : ∀ i, i + 1 ≤ D → ∀ v, predHotV G S i (bp (i + 1)) v = decide (v = bp i) := by
      intro i hiD v
      rw [(predV_spec (hlay (i + 1) hiD).1 ((hlay (i + 1) hiD).2 i (by omega))).2.2 v,
        hbp, ← backV_pred (by omega)]
    have hD0 : bp D = firstY G S Y h := backV_self _ _
    have hval : pathV G S Y = fun v => decide (∃ j < D + 1, 0 ≤ j ∧ v = bp j) := by
      refine downV_eq (C := fun i v => decide (i ≤ D ∧ v = bp i))
        (A := fun i v => decide (∃ j < D + 1, i ≤ j ∧ v = bp j)) (fun i hi => ?_) ?_ ?_
      · have hc : ∀ v, (targetV G S Y ⟨i, by omega⟩ v || decide (∃ y,
            decide (i + 1 ≤ D ∧ y = bp (i + 1)) = true ∧ predHotV G S i y v = true))
            = decide (i ≤ D ∧ v = bp i) := by
          intro v
          rw [targetV_eq h, Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro (⟨hi', rfl⟩ | ⟨y, ⟨hiD, rfl⟩, hy⟩)
            · exact ⟨by omega, by rw [← hD0]; exact congrArg bp (by omega)⟩
            · rw [hpred i hiD, decide_eq_true_eq] at hy
              exact ⟨by omega, hy⟩
          · rintro ⟨hiD, rfl⟩
            rcases hiD.lt_or_eq with hiD | rfl
            · exact Or.inr ⟨bp (i + 1), ⟨hiD, rfl⟩, by rw [hpred i hiD]; simp⟩
            · exact Or.inl ⟨rfl, hD0⟩
        rw [downStep_of_lt hi]
        refine Prod.ext (funext fun v => hc v) (funext fun v => ?_)
        simp only
        rw [hc v, Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hij, rfl⟩ | ⟨hiD, rfl⟩)
          · exact ⟨j, hj, by omega, rfl⟩
          · exact ⟨i, by omega, le_rfl, rfl⟩
        · rintro ⟨j, hj, hij, rfl⟩
          rcases hij.lt_or_eq with hij | rfl
          · exact Or.inl ⟨j, hj, hij, rfl⟩
          · exact Or.inr ⟨by omega, rfl⟩
      · funext v
        rw [targetV_eq h, Bool.eq_iff_iff]
        simp only [Fin.val_last, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hrD, rfl⟩
          exact ⟨by omega, by rw [← hD0]; exact congrArg bp (by omega)⟩
        · rintro ⟨hrD, rfl⟩
          exact ⟨by omega, by rw [← hD0]; exact congrArg bp (by omega)⟩
      · funext v
        rw [targetV_eq h, Bool.eq_iff_iff]
        simp only [Fin.val_last, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj, hrj, rfl⟩
          exact ⟨by omega, by rw [← hD0]; exact congrArg bp (by omega)⟩
        · rintro ⟨hrD, rfl⟩
          exact ⟨r, by omega, le_rfl, by rw [← hD0]; exact congrArg bp (by omega)⟩
    classical
    rw [hval, pathSet, dif_pos h, decide_eq_true_eq, mem_image]
    simp only [mem_range, zero_le, true_and]
    exact ⟨fun ⟨j, hj, hv⟩ => ⟨j, hj, hv.symm⟩, fun ⟨j, hj, hv⟩ => ⟨j, hj, hv.symm⟩⟩
  · -- no target is reached: all targets are empty, and so is every `cur_i`
    have hval : pathV G S Y = fun _ => false :=
      downV_eq (C := fun _ _ => false) (A := fun _ _ => false)
        (fun i hi => by
          rw [downStep_of_lt hi]
          refine Prod.ext (funext fun v => ?_) (funext fun v => ?_) <;>
            simp [targetV_of_not_hits h])
        (funext fun v => (targetV_of_not_hits h _ v).symm)
        (funext fun v => (targetV_of_not_hits h _ v).symm)
    classical
    rw [hval, pathSet, dif_neg h]
    simp

end Proofs

/-! ### The circuit -/

/-- The input of the path gadget: a relation `G`, the sources `S` and the targets `Y`. -/
abbrev pathInR (r : ℕ) : Rep BoolOp Bool n
    ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n))
    ((Fin r → Fin r → Bool) × (Fin r → Bool) × (Fin r → Bool)) :=
  (relR r).prod ((vecR r).prod (vecR r))

/-- The input together with the layers `0, …, r`. -/
abbrev pathLayR (r : ℕ) : Rep BoolOp Bool n
    (((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) ×
      (Fin (r + 1) → Fin r → Arg n))
    (((Fin r → Fin r → Bool) × (Fin r → Bool) × (Fin r → Bool)) × (Fin (r + 1) → Fin r → Bool)) :=
  (pathInR r).prod (Rep.pi (Fin (r + 1)) (vecR r))

/-- The context of the downward pass: the predecessor one-hots and the target one-hots. -/
abbrev pathCtxR (r : ℕ) : Rep BoolOp Bool n
    ((Fin r → Fin r → Fin r → Arg n) × (Fin (r + 1) → Fin r → Arg n))
    ((Fin r → Fin r → Fin r → Bool) × (Fin (r + 1) → Fin r → Bool)) :=
  (Rep.pi (Fin r) (matR r r)).prod (Rep.pi (Fin (r + 1)) (vecR r))

/-- The predecessor one-hots `Pred i y`, `i < r`, from the input and the layers. -/
def predsB (q : ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) ×
    (Fin (r + 1) → Fin r → Arg n)) : Bld BoolOp n (Fin r → Fin r → Fin r → Arg n) :=
  tabB fun i => tabB fun y => seqB vecAndB vecFirstB (q.2 i.castSucc, fun u => q.1.1 u y)

/-- The predecessor one-hots, `4r³` gates. -/
theorem predsB_impl :
    Impl (pathLayR r) (Rep.pi (Fin r) (matR (n := n) r r)) predsB (4 * r ^ 3)
      (fun Q i y => leadV fun u => Q.2 i.castSucc u && Q.1.1 u y) :=
  (Impl.tab fun i => Impl.tab fun y => (vecAndB_impl.comp vecFirstB_impl).pre
    (R := pathLayR r) (g := fun q => (q.2 i.castSucc, fun u => q.1.1 u y))
    (G := fun Q => (Q.2 i.castSucc, fun u => Q.1.1 u y))
    fun _ _ _ hs => ⟨hs.2 i.castSucc, fun u => hs.1.1 u y⟩).cost (by ring)

/-- The target one-hots `T d`, `d ≤ r`, from the input and the layers: the elements of `Y` in each
layer, whether each layer meets `Y`, the first such layer, the least element of `Y` in each
layer, and the mask. -/
def targetsB : ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) ×
    (Fin (r + 1) → Fin r → Arg n) → Bld BoolOp n (Fin (r + 1) → Fin r → Arg n) :=
  seqB (fun q => tabB fun d => vecAndB (q.2 d, q.1.2.2))
    (seqB (pairB (seqB (fun M => tabB fun d => vecAnyB (M d)) vecFirstB)
      (fun M => tabB fun d => vecFirstB (M d))) fun FW => tabB fun d => vecMaskB (FW.1 d, FW.2 d))

/-- The target one-hots, `6r(r + 1) + 3(r + 1)` gates. -/
theorem targetsB_impl :
    Impl (pathLayR r) (Rep.pi (Fin (r + 1)) (vecR (n := n) r)) targetsB
      (6 * r * (r + 1) + 3 * (r + 1))
      (fun Q d y => leadV (fun e => decide (∃ y, (Q.2 e y && Q.1.2.2 y) = true)) d &&
        leadV (fun y => Q.2 d y && Q.1.2.2 y) y) :=
  ((Impl.tab fun d => vecAndB_impl.pre (R := pathLayR r) (g := fun q => (q.2 d, q.1.2.2))
    (G := fun Q => (Q.2 d, Q.1.2.2)) fun _ _ _ hs => ⟨hs.2 d, hs.1.2.2⟩).comp
    ((((vecAnyB_impl.map (r + 1)).comp vecFirstB_impl).pair (vecFirstB_impl.map (r + 1))).comp
      (vecMaskB_impl.map₂ (r + 1)))).cost (by ring)

/-- The context of the downward pass, from `(G, S, Y)`. -/
def pathCtxB : ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) →
    Bld BoolOp n ((Fin r → Fin r → Fin r → Arg n) × (Fin (r + 1) → Fin r → Arg n)) :=
  seqB (pairB (pureB fun p => p) fun p => layersB r (p.1, p.2.1)) (pairB predsB targetsB)

/-- The context of the downward pass, `6r³ + 6r(r + 1) + 3(r + 1)` gates. -/
theorem pathCtxB_impl :
    Impl (pathInR r) (pathCtxR (n := n) r) pathCtxB (6 * r ^ 3 + 6 * r * (r + 1) + 3 * (r + 1))
      (fun t => (fun i : Fin r => predHotV t.1 t.2.1 i, targetV t.1 t.2.1 t.2.2)) :=
  ((Impl.self.pair ((layersB_impl r).pre (R := pathInR r) (g := fun p => (p.1, p.2.1))
    (G := fun t => (t.1, t.2.1)) fun _ _ _ hs => ⟨hs.1, hs.2.1⟩)).comp
    (predsB_impl.pair targetsB_impl)).cost (by ring)

/-- One round of the downward pass, for the layer `i`: from the context `(Pred, T)` and the state
`(cur, acc)`, with `c = T_i ∪ Pred_i(cur)`, the state `(c, acc ∪ c)`. -/
def downRoundB (i : Fin r) :
    ((Fin r → Fin r → Fin r → Arg n) × (Fin (r + 1) → Fin r → Arg n)) ×
      ((Fin r → Arg n) × (Fin r → Arg n)) → Bld BoolOp n ((Fin r → Arg n) × (Fin r → Arg n)) :=
  seqB (pairB (pureB fun p => p.2.2) fun p => relImageAccB (p.1.1 i, p.2.1, p.1.2 i.castSucc))
    (pairB (pureB Prod.snd) vecOrB)

/-- One round of the downward pass, `2r² + r` gates. -/
theorem downRoundB_impl (i : Fin r) :
    Impl ((pathCtxR r).prod ((vecR r).prod (vecR r))) ((vecR (n := n) r).prod (vecR r))
      (downRoundB i) (2 * r ^ 2 + r) (fun t => downStep t.1.1 t.1.2 i t.2) :=
  ((((Impl.free (R₁ := (pathCtxR r).prod ((vecR r).prod (vecR r))) (R₂ := vecR r)
    (g := fun p => p.2.2) (F := fun t => t.2.2) fun _ _ _ hs => hs.2.2).pair
    (relImageAccB_impl.pre (R := (pathCtxR r).prod ((vecR r).prod (vecR r)))
      (g := fun p => (p.1.1 i, p.2.1, p.1.2 i.castSucc))
      (G := fun t => (t.1.1 i, t.2.1, t.1.2 i.castSucc))
      fun _ _ _ hs => ⟨hs.1.1 i, hs.2.1, hs.1.2 i.castSucc⟩)).comp
    (Impl.snd.pair vecOrB_impl)).cost (by ring)).congr fun t => (downStep_of_lt i.isLt t.2).symm

/-- The pivots `r - 1, …, 0`, as elements of `Fin r` or of `ℕ`. -/
theorem foldl_finRange_reverse {β : Type} (f : β → ℕ → β) (b : β) :
    (List.finRange r).reverse.foldl (fun s (i : Fin r) => f s i) b =
      (List.range r).reverse.foldl f b := by
  rw [← List.map_coe_finRange_eq_range, ← List.map_reverse, List.foldl_map]

/-- The downward pass: from `(Pred, T)`, start with `cur = acc = T_r` and run the rounds for the
layers `r - 1, …, 0`; the result is `acc`. -/
def downB (c : (Fin r → Fin r → Fin r → Arg n) × (Fin (r + 1) → Fin r → Arg n)) :
    Bld BoolOp n (Fin r → Arg n) := fun gs =>
  let q := seqB (pairB (pureB fun s => s) (pureB fun c => (c.2 (Fin.last r), c.2 (Fin.last r))))
    (foldCtxB downRoundB (List.finRange r).reverse) c gs
  (q.1, q.2.2)

/-- The downward pass, `r(2r² + r)` gates. -/
theorem downB_impl :
    Impl (pathCtxR r) (vecR (n := n) r) downB (r * (2 * r ^ 2 + r)) (fun t => downV t.1 t.2) :=
  ((((Impl.self.pair (Impl.free (R₁ := pathCtxR r) (R₂ := (vecR r).prod (vecR r))
    (g := fun c => (c.2 (Fin.last r), c.2 (Fin.last r)))
    (F := fun t => (t.2 (Fin.last r), t.2 (Fin.last r)))
    fun _ _ _ hs => ⟨hs.2 (Fin.last r), hs.2 (Fin.last r)⟩)).comp
    (Impl.foldCtx (F := fun (i : Fin r) (c : (Fin r → Fin r → Fin r → Bool) ×
      (Fin (r + 1) → Fin r → Bool)) s => downStep c.1 c.2 i s)
      fun i _ => downRoundB_impl i)).post (g := Prod.snd) (G := Prod.snd)
    fun _ _ _ hs => hs.2).cost (by simp)).congr fun t =>
    congrArg Prod.snd (foldl_finRange_reverse (fun s i => downStep t.1 t.2 i s) _)

/-- The least-index shortest path from `S` to `Y` in `G`, from `(G, S, Y)`. -/
def pathB : ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) →
    Bld BoolOp n (Fin r → Arg n) :=
  seqB pathCtxB downB

/-- The gates of `pathB`. -/
def pathCost (r : ℕ) : ℕ := 8 * r ^ 3 + 7 * r ^ 2 + 9 * r + 3

/-- **Least-index shortest paths**: `pathB` computes `pathV G S Y`, the bits of `pathSet G S Y`
(`pathV_eq_true_iff`), from `(G, S, Y)` with `pathCost r = 8r³ + 7r² + 9r + 3` gates. -/
theorem pathB_impl :
    Impl (pathInR r) (vecR (n := n) r) pathB (pathCost r) (fun t => pathV t.1 t.2.1 t.2.2) :=
  (pathCtxB_impl.comp downB_impl).cost (by unfold pathCost; ring)

/-- The exchange along the least-index shortest path, from `(I, (G, S, Y))`. -/
def exchangeB : (Fin r → Arg n) × ((Fin r → Fin r → Arg n) × (Fin r → Arg n) × (Fin r → Arg n)) →
    Bld BoolOp n (Fin r → Arg n) :=
  seqB (pairB (pureB Prod.fst) fun p => pathB p.2) vecXorB

/-- **The exchange along the least-index shortest path**: `I ⊕ pathV G S Y`, that is
`I ∆ pathSet G S Y`, with `pathCost r + 4r` gates (for the exchange graph this is one round of
the augmenting path algorithm, `augStep_bits` of `BoolAlg/ExchangeBits.lean`). -/
theorem exchangeB_impl :
    Impl ((vecR r).prod (pathInR r)) (vecR (n := n) r) exchangeB (pathCost r + 4 * r)
      (fun t u => t.1 u ^^ pathV t.2.1 t.2.2.1 t.2.2.2 u) :=
  ((Impl.fst.pair (pathB_impl.pre (R := (vecR r).prod (pathInR r)) (g := Prod.snd)
    (G := Prod.snd) fun _ _ _ hs => hs.2)).comp vecXorB_impl).cost (by ring)

end SignedTropical.BoolAlg
