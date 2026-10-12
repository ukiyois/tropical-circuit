import SignedTropical.BoolAlg.Bits

/-!
# Relations: images, breadth-first layers, Warshall's algorithm

A relation `G` on `Fin r`, the arcs `u → v` with `G u v`, is carried by `r²` operands (`relR r`
of `BoolAlg/Bits.lean`), an `r × s` matrix by `rs` operands (`matR r s`), and a subset of
`Fin r` by `r` operands (`vecR r`).  Gadgets over `BoolOp` with exact gate counts (`Impl` of
`BoolAlg/Impl.lean`), each with its value:

* **Image of a set** `U` under an `r × s` matrix (`relImageB`, `2rs` gates):
  `v ↦ ∃ u, U u ∧ G u v`; with an accumulator `A` (`relImageAccB`, `2rs` gates):
  `v ↦ A v ∨ ∃ u, U u ∧ G u v`.  For a one-hot `U` this selects a row.  Transposition is free
  (`transpose_impl`).
* **Breadth-first layers** from a set `S` (`layersB d`, `2dr²` gates): `L_0 = S` and
  `L_{i+1} = L_i ∪ G(L_i)` for `i < d` (`layerV`).  `layerV_eq_true_iff`: `v ∈ L_i` if and only if
  a path of at most `i` arcs leads from `S` to `v`.  `layerV_card_eq_true_iff`: `v ∈ L_r` if and
  only if `v` is reachable from `S` (`Relation.ReflTransGen`).
* **Warshall's algorithm** (`warshallB`, `2r³` gates, the count of `lem:observer`): one round
  `R i j ∨ (R i k ∧ R k j)` per pivot `k`; the result is the transitive closure
  (`warshallV_eq_true_iff`, `Relation.TransGen`).  With the diagonal set (`rtcB`, `2r³ + 1`
  gates), the reflexive transitive closure (`rtcV_eq_true_iff`, `Relation.ReflTransGen`).
-/

namespace SignedTropical.BoolAlg

open Finset

variable {n r s : ℕ}

/-! ### Two gadgets on bits -/

/-- `acc ∨ (a₀ ∧ b₀) ∨ ⋯ ∨ (a_{r-1} ∧ b_{r-1})`, `2r` gates (`dotAccB` of `BoolAlg/Bits.lean`). -/
theorem dotAccB_impl :
    Impl ((vecR r).prod ((vecR r).prod bitR)) (bitR (n := n)) (fun p => dotAccB p.1 p.2.1 p.2.2)
      (2 * r) (fun P => P.2.2 || decide (∃ i, P.1 i = true ∧ P.2.1 i = true)) :=
  fun _ _ _ hs => dotAccB_spec hs.1 hs.2.1 hs.2.2

/-- `a ∨ (b ∧ c)`, two gates. -/
def orAndB (a b c : Arg n) : Bld BoolOp n (Arg n) := fun gs =>
  let p := emit .and b c gs
  emit .or a p.2 p.1

/-- `a ∨ (b ∧ c)`, two gates. -/
theorem orAndB_impl :
    Impl (bitR.prod (bitR.prod bitR)) (bitR (n := n)) (fun p => orAndB p.1 p.2.1 p.2.2) 2
      (fun P => P.1 || (P.2.1 && P.2.2)) := by
  intro gs p P hs
  have p₁ := isPrefix_emit BoolOp.and p.2.1 p.2.2 gs
  exact ⟨p₁.trans (isPrefix_emit _ _ _ _), by simp [orAndB, length_emit],
    den_emit BoolOp.or (hs.1.mono p₁) (den_emit BoolOp.and hs.2.1 hs.2.2)⟩

/-! ### Image of a set under a relation -/

/-- **Transposition** `G i j ↦ G j i`: free. -/
theorem transpose_impl :
    Impl (relR r) (relR (n := n) r) (pureB fun R i j => R j i) 0 (fun G i j => G j i) :=
  Impl.free fun _ _ _ hs i j => hs j i

/-- `A v ∨ ∃ u, U u ∧ G u v` for every `v`, from `(G, U, A)`. -/
def relImageAccB (p : (Fin r → Fin s → Arg n) × (Fin r → Arg n) × (Fin s → Arg n)) :
    Bld BoolOp n (Fin s → Arg n) :=
  tabB fun v => dotAccB p.2.1 (fun u => p.1 u v) (p.2.2 v)

/-- **Image of a set, with an accumulator**: for an `r × s` matrix `G`, a subset `U` of `Fin r`
and a subset `A` of `Fin s`, the set `A ∪ G(U)`, that is `v ↦ A v ∨ ∃ u, U u ∧ G u v`:
`2rs` gates. -/
theorem relImageAccB_impl :
    Impl ((matR r s).prod ((vecR r).prod (vecR s))) (vecR (n := n) s) relImageAccB (2 * r * s)
      (fun P v => P.2.2 v || decide (∃ u, P.2.1 u = true ∧ P.1 u v = true)) :=
  (Impl.tab fun v => dotAccB_impl.pre (R := (matR r s).prod ((vecR r).prod (vecR s)))
    (g := fun p => (p.2.1, fun u => p.1 u v, p.2.2 v))
    (G := fun P => (P.2.1, fun u => P.1 u v, P.2.2 v))
    fun _ _ _ hs => ⟨hs.2.1, fun u => hs.1 u v, hs.2.2 v⟩).cost (by ring)

/-- `v ↦ ∃ u, U u ∧ G u v`, from `(G, U)`. -/
def relImageB (p : (Fin r → Fin s → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin s → Arg n) :=
  relImageAccB (p.1, p.2, fun _ => .const)

/-- **Image of a set** under an `r × s` matrix `G`: the set `G(U)`, that is
`v ↦ ∃ u, U u ∧ G u v`, `2rs` gates.  For a one-hot `U` marking `u`, this is row `u` of `G`. -/
theorem relImageB_impl :
    Impl ((matR r s).prod (vecR r)) (vecR (n := n) s) relImageB (2 * r * s)
      (fun P v => decide (∃ u, P.2 u = true ∧ P.1 u v = true)) :=
  (relImageAccB_impl.pre (R := (matR r s).prod (vecR r))
    (g := fun p => (p.1, p.2, fun _ => .const)) (G := fun P => (P.1, P.2, fun _ => false))
    fun gs _ _ hs => ⟨hs.1, hs.2, fun _ => den_const gs⟩).congr fun P => by
      funext v; simp

/-! ### Breadth-first layers -/

/-- One breadth-first step: `L` together with the out-neighbours of `L` in `G`. -/
def bfsStep (G : Fin r → Fin r → Bool) (L : Fin r → Bool) : Fin r → Bool :=
  fun v => L v || decide (∃ u, L u = true ∧ G u v = true)

/-- The breadth-first layers from `S` in `G`: `layerV G S 0 = S` and
`layerV G S (d + 1) = bfsStep G (layerV G S d)` (`layerV_succ`). -/
def layerV (G : Fin r → Fin r → Bool) (S : Fin r → Bool) (d : ℕ) : Fin r → Bool :=
  (bfsStep G)^[d] S

variable {G : Fin r → Fin r → Bool} {S : Fin r → Bool}

/-- Layer `0` is the set of sources. -/
@[simp] theorem layerV_zero : layerV G S 0 = S := rfl

/-- Layer `d + 1` is one breadth-first step from layer `d`. -/
theorem layerV_succ (d : ℕ) : layerV G S (d + 1) = bfsStep G (layerV G S d) :=
  Function.iterate_succ_apply' _ _ _

/-- **Layers are bounded reachability**: `v` lies in layer `d` if and only if some path
`p 0 → p 1 → ⋯ → p l` with `l ≤ d` arcs leads from an element `p 0` of `S` to `p l = v`. -/
theorem layerV_eq_true_iff {d : ℕ} {v : Fin r} :
    layerV G S d v = true ↔ ∃ (p : ℕ → Fin r) (l : ℕ), l ≤ d ∧ S (p 0) = true ∧ p l = v ∧
      ∀ i < l, G (p i) (p (i + 1)) = true := by
  induction d generalizing v with
  | zero =>
    refine ⟨fun h => ⟨fun _ => v, 0, le_rfl, h, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
      ?_⟩
    rintro ⟨p, l, hl, hs, rfl, -⟩
    obtain rfl : l = 0 := Nat.le_zero.1 hl
    exact hs
  | succ d ih =>
    rw [layerV_succ]
    simp only [bfsStep, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨u, hu, huv⟩)
      · obtain ⟨p, l, hl, hs, hv, hp⟩ := ih.1 h
        exact ⟨p, l, by omega, hs, hv, hp⟩
      · obtain ⟨p, l, hl, hs, rfl, hp⟩ := ih.1 hu
        refine ⟨fun i => if i ≤ l then p i else v, l + 1, by omega, by simpa using hs,
          by simp, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · simp [hi.le, Nat.succ_le_of_lt hi, hp i hi]
        · simpa using huv
    · rintro ⟨p, l, hl, hs, rfl, hp⟩
      rcases Nat.lt_or_ge l (d + 1) with hl' | hl'
      · exact Or.inl (ih.2 ⟨p, l, by omega, hs, rfl, hp⟩)
      · obtain rfl : l = d + 1 := le_antisymm hl hl'
        exact Or.inr ⟨p d, ih.2 ⟨p, d, le_rfl, hs, rfl, fun i hi => hp i (by omega)⟩,
          hp d (by omega)⟩

/-- The layers increase. -/
theorem layerV_le {d e : ℕ} (hde : d ≤ e) {v : Fin r} (h : layerV G S d v = true) :
    layerV G S e v = true := by
  obtain ⟨p, l, hl, hs, hv, hp⟩ := layerV_eq_true_iff.1 h
  exact layerV_eq_true_iff.2 ⟨p, l, hl.trans hde, hs, hv, hp⟩

/-- Some layer `j ≤ r` equals the next one. -/
theorem exists_layerV_succ_eq (G : Fin r → Fin r → Bool) (S : Fin r → Bool) :
    ∃ j ≤ r, layerV G S (j + 1) = layerV G S j := by
  by_contra! h
  have hcard : ∀ j ≤ r + 1, j ≤ (univ.filter fun v => layerV G S j v = true).card := by
    intro j hj
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      refine Nat.succ_le_of_lt ((ih (by omega)).trans_lt (card_lt_card ?_))
      refine Finset.ssubset_iff_subset_ne.2 ⟨fun v hv => ?_, fun heq => h j (by omega) ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hv ⊢
        exact layerV_le (Nat.le_succ j) hv
      · funext v
        have := congrArg (v ∈ ·) heq
        simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
        exact Bool.eq_iff_iff.2 this.symm
  have := (hcard (r + 1) le_rfl).trans (card_le_univ _)
  simp at this

/-- Every layer is contained in layer `r`. -/
theorem layerV_le_card (d : ℕ) {v : Fin r} (h : layerV G S d v = true) :
    layerV G S r v = true := by
  obtain ⟨j, hj, hjeq⟩ := exists_layerV_succ_eq G S
  have hstab : ∀ i, layerV G S (j + i) = layerV G S j := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [← Nat.add_assoc, layerV_succ, ih, ← layerV_succ, hjeq]
  rcases le_total d j with hdj | hjd
  · exact layerV_le (hdj.trans hj) h
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjd
    rw [hstab] at h
    exact layerV_le hj h

/-- **Reachability**: `v` lies in layer `r` if and only if `v` is reachable from `S`. -/
theorem layerV_card_eq_true_iff {v : Fin r} :
    layerV G S r v = true ↔
      ∃ s, S s = true ∧ Relation.ReflTransGen (fun a b => G a b = true) s v := by
  constructor
  · intro h
    obtain ⟨p, l, -, hs, rfl, hp⟩ := layerV_eq_true_iff.1 h
    refine ⟨p 0, hs, ?_⟩
    have key : ∀ i ≤ l, Relation.ReflTransGen (fun a b => G a b = true) (p 0) (p i) := by
      intro i hi
      induction i with
      | zero => exact .refl
      | succ i ih => exact (ih (by omega)).tail (hp i (by omega))
    exact key l le_rfl
  · rintro ⟨s, hs, h⟩
    suffices ∃ d, layerV G S d v = true from
      let ⟨d, hd⟩ := this
      layerV_le_card d hd
    induction h with
    | refl => exact ⟨0, hs⟩
    | tail _ hbc ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨d + 1, ?_⟩
      rw [layerV_succ]
      simp only [bfsStep, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨_, hd, hbc⟩

/-- One breadth-first step, from `(G, L)`. -/
def bfsStepB (p : (Fin r → Fin r → Arg n) × (Fin r → Arg n)) : Bld BoolOp n (Fin r → Arg n) :=
  relImageAccB (p.1, p.2, p.2)

/-- **One breadth-first step**, `2r²` gates. -/
theorem bfsStepB_impl :
    Impl ((relR r).prod (vecR r)) (vecR (n := n) r) bfsStepB (2 * r ^ 2)
      (fun P => bfsStep P.1 P.2) :=
  (relImageAccB_impl.pre (R := (relR r).prod (vecR r)) (g := fun p => (p.1, p.2, p.2))
    (G := fun P => (P.1, P.2, P.2)) fun _ _ _ hs => ⟨hs.1, hs.2, hs.2⟩).cost (by ring)

/-- The breadth-first layers `0, …, d` from `(G, S)`. -/
def layersB (d : ℕ) : (Fin r → Fin r → Arg n) × (Fin r → Arg n) →
    Bld BoolOp n (Fin (d + 1) → Fin r → Arg n) :=
  scanCtxB bfsStepB d

/-- **Breadth-first layers** (`lem:augment`, Step 1, "a breadth-first search"): the layers
`0, …, d` from the set `S` in the relation `G`, `2dr²` gates. -/
theorem layersB_impl (d : ℕ) :
    Impl ((relR r).prod (vecR r)) (Rep.pi (Fin (d + 1)) (vecR (n := n) r)) (layersB d)
      (2 * d * r ^ 2) (fun P i => layerV P.1 P.2 i) :=
  (bfsStepB_impl.scanCtx d).cost (by ring)

/-! ### Warshall's algorithm -/

/-- One round of Warshall's algorithm with pivot `k`: `R i j ∨ (R i k ∧ R k j)`. -/
def warshallStep (k : Fin r) (R : Fin r → Fin r → Bool) : Fin r → Fin r → Bool :=
  fun i j => R i j || (R i k && R k j)

/-- Warshall's algorithm: one round for each pivot `0, …, r - 1`, in this order. -/
def warshallV (G : Fin r → Fin r → Bool) : Fin r → Fin r → Bool :=
  (List.finRange r).foldl (fun R k => warshallStep k R) G

/-- A path `i → ⋯ → c → j` of at least one arc of `G` whose inner vertices satisfy `K`. -/
def PathVia (G : Fin r → Fin r → Bool) (K : Fin r → Prop) (i j : Fin r) : Prop :=
  ∃ c, Relation.ReflTransGen (fun a b => G a b = true ∧ K b) i c ∧ G c j = true

/-- Enlarging the set of allowed vertices keeps the paths. -/
theorem reflTransGen_restrict_mono {K K' : Fin r → Prop} (hK : ∀ b, K b → K' b)
    {i c : Fin r} (h : Relation.ReflTransGen (fun a b => G a b = true ∧ K b) i c) :
    Relation.ReflTransGen (fun a b => G a b = true ∧ K' b) i c :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, hK _ h.2⟩) _ _ h

/-- Enlarging the set of allowed inner vertices keeps the paths. -/
theorem pathVia_mono {K K' : Fin r → Prop} (hK : ∀ b, K b → K' b) {i j : Fin r}
    (h : PathVia G K i j) : PathVia G K' i j :=
  let ⟨c, hic, hcj⟩ := h
  ⟨c, reflTransGen_restrict_mono hK hic, hcj⟩

/-- **The step of Warshall's algorithm**: a path with inner vertices in `K ∪ {k}` exists if and
only if a path with inner vertices in `K` exists, or one from `i` to `k` and one from `k` to `j`. -/
theorem pathVia_or_eq {K : Fin r → Prop} {k i j : Fin r} :
    PathVia G (fun b => K b ∨ b = k) i j ↔
      PathVia G K i j ∨ (PathVia G K i k ∧ PathVia G K k j) := by
  constructor
  · rintro ⟨c, hic, hcj⟩
    -- every vertex reached from `i` through `K ∪ {k}` is reached through `K`, from `i` or `k`
    have key : ∀ c, Relation.ReflTransGen (fun a b => G a b = true ∧ (K b ∨ b = k)) i c →
        Relation.ReflTransGen (fun a b => G a b = true ∧ K b) i c ∨
          (PathVia G K i k ∧ Relation.ReflTransGen (fun a b => G a b = true ∧ K b) k c) := by
      intro c h
      induction h with
      | refl => exact Or.inl .refl
      | tail _ hbc ih =>
        obtain ⟨hG, hK | rfl⟩ := hbc
        · exact ih.imp (fun h => h.tail ⟨hG, hK⟩) fun h => ⟨h.1, h.2.tail ⟨hG, hK⟩⟩
        · exact Or.inr ⟨ih.elim (fun h => ⟨_, h, hG⟩) And.left, .refl⟩
    rcases key c hic with h | ⟨h₁, h₂⟩
    · exact Or.inl ⟨c, h, hcj⟩
    · exact Or.inr ⟨h₁, c, h₂, hcj⟩
  · rintro (h | ⟨⟨c, hic, hck⟩, ⟨c', hkc', hc'j⟩⟩)
    · exact pathVia_mono (fun _ => Or.inl) h
    · have hK : ∀ b, K b → K b ∨ b = k := fun _ => Or.inl
      exact ⟨c', ((reflTransGen_restrict_mono hK hic).tail ⟨hck, Or.inr rfl⟩).trans
        (reflTransGen_restrict_mono hK hkc'), hc'j⟩

/-- The rounds of Warshall's algorithm for the pivots of a list `l`: entry `(i, j)` is set if and
only if a path from `i` to `j` with inner vertices in `l` exists. -/
theorem foldl_warshallStep_eq_true_iff (l : List (Fin r)) {i j : Fin r} :
    l.foldl (fun R k => warshallStep k R) G i j = true ↔ PathVia G (· ∈ l) i j := by
  induction l using List.reverseRecOn generalizing i j with
  | nil =>
    simp only [List.foldl_nil]
    refine ⟨fun h => ⟨i, .refl, h⟩, fun ⟨c, hic, hcj⟩ => ?_⟩
    obtain rfl : c = i := by
      induction hic with
      | refl => rfl
      | tail _ hbc _ => exact absurd hbc.2 List.not_mem_nil
    exact hcj
  | append_singleton l k ih =>
    have hK : (· ∈ l ++ [k]) = fun b => b ∈ l ∨ b = k := by
      funext b; simp
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hK, pathVia_or_eq]
    simp only [warshallStep, Bool.or_eq_true, Bool.and_eq_true, ih]

/-- **Warshall's algorithm computes the transitive closure.** -/
theorem warshallV_eq_true_iff {i j : Fin r} :
    warshallV G i j = true ↔ Relation.TransGen (fun a b => G a b = true) i j := by
  rw [warshallV, foldl_warshallStep_eq_true_iff, Relation.TransGen.tail'_iff]
  simp only [PathVia, List.mem_finRange, and_true]

/-- One round of Warshall's algorithm with pivot `k`. -/
def warshallStepB (k : Fin r) (R : Fin r → Fin r → Arg n) :
    Bld BoolOp n (Fin r → Fin r → Arg n) :=
  tabB fun i => tabB fun j => orAndB (R i j) (R i k) (R k j)

/-- **One round of Warshall's algorithm**, `2r²` gates. -/
theorem warshallStepB_impl (k : Fin r) :
    Impl (relR r) (relR (n := n) r) (warshallStepB k) (2 * r ^ 2) (warshallStep k) :=
  (Impl.tab fun i => Impl.tab fun j => orAndB_impl.pre (R := relR r)
    (g := fun R => (R i j, R i k, R k j)) (G := fun R => (R i j, R i k, R k j))
    fun _ _ _ hs => ⟨hs i j, hs i k, hs k j⟩).cost (by ring)

/-- Warshall's algorithm: one round for each pivot `0, …, r - 1`. -/
def warshallB : (Fin r → Fin r → Arg n) → Bld BoolOp n (Fin r → Fin r → Arg n) :=
  foldB warshallStepB (List.finRange r)

/-- **Warshall's algorithm** (`lem:observer`, Step 2, "Warshall's algorithm closes them
transitively with `2m³` gates"): `2r³` gates; its value is the transitive closure
(`warshallV_eq_true_iff`). -/
theorem warshallB_impl : Impl (relR r) (relR (n := n) r) warshallB (2 * r ^ 3) warshallV :=
  (Impl.fold (l := List.finRange r) fun k _ => warshallStepB_impl k).cost
    (by simp only [List.length_finRange]; ring)

/-- The diagonal set: `R i j ∨ i = j`. -/
def reflB (R : Fin r → Fin r → Arg n) : Bld BoolOp n (Fin r → Fin r → Arg n) := fun gs =>
  let t := emit .not .const .const gs
  (t.1, fun i j => if i = j then t.2 else R i j)

/-- **Setting the diagonal**, one gate (for the constant `true`). -/
theorem reflB_impl :
    Impl (relR r) (relR (n := n) r) reflB 1 (fun R i j => R i j || decide (i = j)) := by
  intro gs R T hR
  have pt := isPrefix_emit BoolOp.not (Arg.const (n := n)) .const gs
  have ht := den_emit (I := boolInterp) BoolOp.not (den_const gs) (den_const gs)
  refine ⟨pt, length_emit _ _ _ _, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [reflB, if_true]
    exact Rep.congr _ ht fun x => by simp [boolInterp]
  · simp only [reflB, hij, if_false]
    exact Rep.congr _ ((hR i j).mono pt) fun x => by simp

/-- The reflexive transitive closure: Warshall's algorithm, then the diagonal. -/
def rtcV (G : Fin r → Fin r → Bool) : Fin r → Fin r → Bool :=
  fun i j => warshallV G i j || decide (i = j)

/-- **The reflexive transitive closure.** -/
theorem rtcV_eq_true_iff {i j : Fin r} :
    rtcV G i j = true ↔ Relation.ReflTransGen (fun a b => G a b = true) i j := by
  rw [Relation.reflTransGen_iff_eq_or_transGen, rtcV, Bool.or_eq_true, warshallV_eq_true_iff,
    decide_eq_true_iff, eq_comm, or_comm]

/-- Warshall's algorithm, then the diagonal. -/
def rtcB : (Fin r → Fin r → Arg n) → Bld BoolOp n (Fin r → Fin r → Arg n) :=
  seqB warshallB reflB

/-- **The reflexive transitive closure**, `2r³ + 1` gates (`rtcV_eq_true_iff`). -/
theorem rtcB_impl : Impl (relR r) (relR (n := n) r) rtcB (2 * r ^ 3 + 1) rtcV :=
  warshallB_impl.comp reflB_impl

end SignedTropical.BoolAlg
