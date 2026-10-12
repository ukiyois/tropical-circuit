import SignedTropical.Binary

/-!
# Graphic matroids

`greedy_intersection.tex`, Corollary `cor:classes`, item 5: graphic matroids, and the API that
Propositions `prop:star` and `prop:nphard` use.

A multigraph has vertices `Fin n` and edges `Fin m`, edge `e` joining `src e` and `tgt e`
(loops and parallel edges allowed).  A *cycle* is the edge set of a closed walk
`x₀ e₀ x₁ e₁ ⋯ x_{l-1} e_{l-1} x₀` with `l ≥ 1` pairwise distinct vertices and `l` pairwise
distinct edges (`IsCycle`): a loop is a cycle with one edge, two parallel edges form a cycle
with two edges.

* `cycleMatroid G`: the binary matroid of the vertex-edge incidence matrix over `ZMod 2`.
* `indep_iff`: its independent sets are the edge sets that contain no cycle, so it is the cycle
  matroid of `G`.
* `isCircuit_iff`: its circuits are the cycles.
* `exists_isCycle_subset`: a nonempty edge set in which every vertex has even degree contains a
  cycle (a longest path, closed by a second edge at its last vertex).
* `rankCircuit`, `corollaryC_graphic`: a Boolean rank circuit with `m(9n² + 5n) + 11n⌈log₂(n+1)⌉`
  gates (Binary.lean), and a signed tropical circuit for `h_M` with at most
  `100(m+1)²(n+1)²` gates.
-/

open Finset

namespace SignedTropical.Classes.Graphic

/-- A multigraph on the vertex set `Fin n` with edge set `Fin m`: edge `e` joins `src e` and
`tgt e`, a loop when they coincide; parallel edges are allowed. -/
structure Multigraph (n m : ℕ) where
  src : Fin m → Fin n
  tgt : Fin m → Fin n

namespace Multigraph

variable {n m : ℕ} (G : Multigraph n m)

/-- Edge `e` joins `x` and `y`. -/
def Joins (e : Fin m) (x y : Fin n) : Prop :=
  (G.src e = x ∧ G.tgt e = y) ∨ (G.src e = y ∧ G.tgt e = x)

/-- `C` is a cycle: the edge set of a closed walk `x₀ e₀ x₁ e₁ ⋯ x_{l-1} e_{l-1} x₀` with
`l ≥ 1` pairwise distinct vertices and `l` pairwise distinct edges, edge `e_i` joining `x_i`
and `x_{i+1}` (indices modulo `l`). -/
def IsCycle (C : Finset (Fin m)) : Prop :=
  ∃ l, 0 < l ∧ ∃ (e : ℕ → Fin m) (x : ℕ → Fin n),
    Set.InjOn e (Set.Iio l) ∧ Set.InjOn x (Set.Iio l) ∧
    (∀ i < l, G.Joins (e i) (x i) (x ((i + 1) % l))) ∧ C = (range l).image e

/-- The number of ends of `e` at `v`: `[src e = v] + [tgt e = v]` (two for a loop at `v`). -/
def inc (v : Fin n) (e : Fin m) : ℕ :=
  (if G.src e = v then 1 else 0) + (if G.tgt e = v then 1 else 0)

/-- The degree of `v` in the edge set `T`, a loop counting twice. -/
def deg (T : Finset (Fin m)) (v : Fin n) : ℕ := ∑ e ∈ T, G.inc v e

/-- A path in `T` with `d` edges: pairwise distinct vertices `x 0, …, x d`, and edges `e i ∈ T`
joining `x i` and `x (i + 1)` for `i < d`. -/
def IsPathIn (T : Finset (Fin m)) (d : ℕ) (x : ℕ → Fin n) (e : ℕ → Fin m) : Prop :=
  Set.InjOn x (Set.Iic d) ∧ ∀ i < d, e i ∈ T ∧ G.Joins (e i) (x i) (x (i + 1))

/-- The vertex-edge incidence matrix over `ZMod 2`; the column of a loop is zero. -/
def incidence : Matrix (Fin n) (Fin m) (ZMod 2) := fun v e => (G.inc v e : ZMod 2)

/-- The cycle matroid of `G`, as the binary matroid of the incidence matrix; `indep_iff` shows
that its independent sets are the edge sets containing no cycle. -/
noncomputable def cycleMatroid : Matroid (Fin m) := binaryMatroid G.incidence

@[simp] theorem cycleMatroid_E : G.cycleMatroid.E = Set.univ := rfl

/-! ### Ends of edges -/

variable {G}

theorem inc_of_joins {e : Fin m} {x y : Fin n} (h : G.Joins e x y) (v : Fin n) :
    G.inc v e = (if x = v then 1 else 0) + (if y = v then 1 else 0) := by
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp only [inc, hs, ht]
  exact add_comm _ _

/-- An end of an edge joining `x` and `y` is `x` or `y`. -/
theorem eq_or_eq_of_joins {e : Fin m} {x y v : Fin n} (h : G.Joins e x y) (hv : G.inc v e ≠ 0) :
    v = x ∨ v = y := by
  rw [inc_of_joins h] at hv
  by_contra hc
  push Not at hc
  simp [Ne.symm hc.1, Ne.symm hc.2] at hv

theorem inc_left_ne_zero {e : Fin m} {x y : Fin n} (h : G.Joins e x y) : G.inc x e ≠ 0 := by
  rw [inc_of_joins h]; simp

theorem inc_right_ne_zero {e : Fin m} {x y : Fin n} (h : G.Joins e x y) : G.inc y e ≠ 0 := by
  rw [inc_of_joins h]; simp

/-! ### Even degrees -/

/-- Over `ZMod 2`, the columns of `T` sum to zero iff every vertex has even degree in `T`. -/
theorem sum_colZ_eq_zero_iff (T : Finset (Fin m)) :
    ∑ e ∈ T, colZ G.incidence e = 0 ↔ ∀ v, Even (G.deg T v) := by
  rw [funext_iff]
  refine forall_congr' fun v => ?_
  rw [← ZMod.natCast_eq_zero_iff_even, deg, Nat.cast_sum, Finset.sum_apply]
  rfl

/-- `∑_{i<l} f((i+1) mod l) = ∑_{i<l} f(i)`. -/
theorem sum_range_succ_mod {l : ℕ} (hl : 0 < l) (f : ℕ → ℕ) :
    ∑ i ∈ range l, f ((i + 1) % l) = ∑ i ∈ range l, f i := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hl
  rw [zero_add, sum_range_succ, Nat.mod_self, sum_range_succ']
  congr 1
  exact sum_congr rfl fun i hi => by rw [Nat.mod_eq_of_lt (by simpa using hi)]

/-- In a cycle, the degree of `v` is twice the number of times the walk visits `v`. -/
theorem IsCycle.deg_eq {C : Finset (Fin m)} {l : ℕ} (hl : 0 < l) {e : ℕ → Fin m} {x : ℕ → Fin n}
    (he : Set.InjOn e (Set.Iio l)) (hj : ∀ i < l, G.Joins (e i) (x i) (x ((i + 1) % l)))
    (hC : C = (range l).image e) (v : Fin n) :
    G.deg C v = 2 * ∑ i ∈ range l, if x i = v then 1 else 0 := by
  rw [deg, hC, sum_image fun i hi j hj h => he (by simpa using hi) (by simpa using hj) h]
  rw [sum_congr rfl fun i hi => inc_of_joins (hj i (by simpa using hi)) v, sum_add_distrib,
    sum_range_succ_mod hl (fun i => if x i = v then 1 else 0), two_mul]

/-- Every vertex has even degree in a cycle. -/
theorem IsCycle.even_deg {C : Finset (Fin m)} (h : G.IsCycle C) (v : Fin n) : Even (G.deg C v) := by
  obtain ⟨l, hl, e, x, he, -, hj, hC⟩ := h
  rw [IsCycle.deg_eq hl he hj hC]
  exact even_two_mul _

theorem IsCycle.nonempty {C : Finset (Fin m)} (h : G.IsCycle C) : C.Nonempty := by
  obtain ⟨l, hl, e, x, -, -, -, rfl⟩ := h
  exact ⟨e 0, mem_image_of_mem e (mem_range.2 hl)⟩

/-- A cycle `C` contains no nonempty set `T` of even degrees other than `C` itself.  If `e_j ∈ T`,
the vertex `x_{j+1}` meets `C` only in `e_j` and `e_{j+1}`, so `e_{j+1} ∈ T` by parity; going
around the cycle, `C ⊆ T`. -/
theorem IsCycle.eq_of_subset {C T : Finset (Fin m)} (h : G.IsCycle C) (hTC : T ⊆ C)
    (hT : T.Nonempty) (hev : ∀ v, Even (G.deg T v)) : T = C := by
  obtain ⟨l, hl, e, x, he, hx, hj, rfl⟩ := h
  have hinj : ∀ {a b : ℕ}, a < l → b < l → x a = x b → a = b := fun ha hb hab => hx ha hb hab
  have hmod : ∀ i, (i + 1) % l < l := fun i => Nat.mod_lt _ hl
  -- the degree of `x_{(j+1) % l}` in `T` counts `e_j` and `e_{(j+1) % l}`
  have hstep : ∀ j < l, e j ∈ T → e ((j + 1) % l) ∈ T := by
    intro j hjl hjT
    by_contra hnot
    have hdeg : G.deg T (x ((j + 1) % l)) =
        ∑ i ∈ (range l).filter (fun i => e i ∈ T), G.inc (x ((j + 1) % l)) (e i) := by
      rw [deg, ← sum_image (f := fun f => G.inc (x ((j + 1) % l)) f)
        fun a ha b hb hab => he (by simpa using (mem_filter.1 ha).1)
          (by simpa using (mem_filter.1 hb).1) hab]
      congr 1
      ext f
      simp only [mem_image, mem_filter, mem_range]
      constructor
      · intro hf
        obtain ⟨i, hi, rfl⟩ := mem_image.1 (hTC hf)
        exact ⟨i, ⟨mem_range.1 hi, hf⟩, rfl⟩
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
    have hval : ∀ i ∈ (range l).filter (fun i => e i ∈ T),
        G.inc (x ((j + 1) % l)) (e i) = if i = j then 1 else 0 := by
      intro i hi
      obtain ⟨hil, hiT⟩ := mem_filter.1 hi
      rw [mem_range] at hil
      rw [inc_of_joins (hj i hil)]
      have h1 : (x i = x ((j + 1) % l)) ↔ False := by
        refine iff_false_intro fun hx' => hnot ?_
        rw [← hinj hil (hmod j) hx']
        exact hiT
      have h2 : (x ((i + 1) % l) = x ((j + 1) % l)) ↔ i = j := by
        refine ⟨fun hx' => ?_, fun hij => hij ▸ rfl⟩
        have := hinj (hmod i) (hmod j) hx'
        rcases Nat.lt_or_ge (i + 1) l with hi1 | hi1 <;> rcases Nat.lt_or_ge (j + 1) l with hj1 | hj1
        · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at this; omega
        · rw [Nat.mod_eq_of_lt hi1, show j + 1 = l by omega, Nat.mod_self] at this; omega
        · rw [Nat.mod_eq_of_lt hj1, show i + 1 = l by omega, Nat.mod_self] at this; omega
        · omega
      simp only [h1, h2, if_false, zero_add]
    have hjmem : j ∈ (range l).filter (fun i => e i ∈ T) := mem_filter.2 ⟨mem_range.2 hjl, hjT⟩
    have := hev (x ((j + 1) % l))
    rw [hdeg, sum_congr rfl hval, sum_ite_eq', if_pos hjmem] at this
    exact Nat.not_even_one this
  -- going around the cycle
  obtain ⟨f, hf⟩ := hT
  obtain ⟨j, hj', rfl⟩ := mem_image.1 (hTC hf)
  rw [mem_range] at hj'
  have hall : ∀ i, e ((j + i) % l) ∈ T := by
    intro i
    induction i with
    | zero => rwa [add_zero, Nat.mod_eq_of_lt hj']
    | succ i ih =>
      have := hstep _ (Nat.mod_lt _ hl) ih
      rwa [Nat.mod_add_mod, add_assoc] at this
  refine hTC.antisymm fun f hf => ?_
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hf
  rw [mem_range] at hi
  have := hall (i + l - j)
  rwa [show j + (i + l - j) = i + l by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi] at this

/-! ### Paths -/

variable {T : Finset (Fin m)} {d : ℕ} {x : ℕ → Fin n} {e : ℕ → Fin m}

/-- A path has at most `n - 1` edges. -/
theorem IsPathIn.succ_le (h : G.IsPathIn T d x e) : d + 1 ≤ n := by
  have := card_le_card_of_injOn x (s := range (d + 1)) (t := (univ : Finset (Fin n)))
    (fun _ _ => mem_univ _) (h.1.mono fun i hi => Nat.lt_succ_iff.1 (mem_range.1 hi))
  simpa using this

/-- The edges of a path are pairwise distinct. -/
theorem IsPathIn.edge_ne (h : G.IsPathIn T d x e) {a b : ℕ} (hab : a < b) (hb : b < d) :
    e a ≠ e b := by
  intro heq
  have ha := (h.2 a (hab.trans hb)).2
  have hb' := (h.2 b hb).2
  rcases eq_or_eq_of_joins hb' (heq ▸ inc_left_ne_zero ha) with hx | hx
  · exact hab.ne (h.1 (show a ≤ d by omega) (show b ≤ d by omega) hx)
  · have := h.1 (show a ≤ d by omega) (show b + 1 ≤ d by omega) hx; omega

/-- An edge with an end at the last vertex `x d` differs from every edge `e i` with
`i + 1 < d`. -/
theorem IsPathIn.ne_of_inc_last (h : G.IsPathIn T d x e) {f : Fin m} (hf : G.inc (x d) f ≠ 0)
    {i : ℕ} (hi : i + 1 < d) : f ≠ e i := by
  rintro rfl
  rcases eq_or_eq_of_joins (h.2 i (by omega)).2 hf with hx | hx
  · have := h.1 (le_refl d) (show i ≤ d by omega) hx; omega
  · have := h.1 (le_refl d) (show i + 1 ≤ d by omega) hx; omega

/-- A path extended by an edge `f ∈ T` from its last vertex to a new vertex `w`. -/
theorem IsPathIn.extend (h : G.IsPathIn T d x e) {f : Fin m} {w : Fin n} (hfT : f ∈ T)
    (hf : G.Joins f (x d) w) (hw : ∀ i ≤ d, x i ≠ w) :
    G.IsPathIn T (d + 1) (Function.update x (d + 1) w) (Function.update e d f) := by
  refine ⟨fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · simp only [Set.mem_Iic] at hi hj
    rcases Nat.lt_or_ge i (d + 1) with hi' | hi' <;> rcases Nat.lt_or_ge j (d + 1) with hj' | hj'
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
      exact h.1 (show i ≤ d by omega) (show j ≤ d by omega) hij
    · rw [Function.update_of_ne (by omega), show j = d + 1 by omega, Function.update_self] at hij
      exact absurd hij (hw i (by omega))
    · rw [Function.update_of_ne (show j ≠ d + 1 by omega), show i = d + 1 by omega,
        Function.update_self] at hij
      exact absurd hij.symm (hw j (by omega))
    · omega
  · rcases Nat.lt_or_ge i d with hid | hid
    · rw [Function.update_of_ne (show i ≠ d by omega), Function.update_of_ne (show i ≠ d + 1 by omega),
        Function.update_of_ne (show i + 1 ≠ d + 1 by omega)]
      exact h.2 i hid
    · obtain rfl : i = d := by omega
      rw [Function.update_self, Function.update_of_ne (show i ≠ i + 1 by omega),
        Function.update_self]
      exact ⟨hfT, hf⟩

/-- A path closed by an edge `f ∈ T` from its last vertex back to an earlier vertex `x j`
contains a cycle. -/
theorem IsPathIn.exists_isCycle (h : G.IsPathIn T d x e) {j : ℕ} (hj : j < d) {f : Fin m}
    (hfT : f ∈ T) (hf : G.Joins f (x d) (x j)) (hfe : f ≠ e (d - 1)) :
    ∃ C ⊆ T, G.IsCycle C := by
  set l := d - j + 1 with hl
  let g : ℕ → Fin m := fun i => if i + 1 < l then e (j + i) else f
  have hfne : ∀ i, i < d → f ≠ e i := fun i hi => by
    rcases Nat.lt_or_ge (i + 1) d with hi' | hi'
    · exact h.ne_of_inc_last (inc_left_ne_zero hf) hi'
    · rwa [show i = d - 1 by omega]
  refine ⟨(range l).image g, fun f' hf' => ?_, l, by omega, g, fun i => x (j + i), ?_, ?_, ?_, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hf'
    simp only [g]
    split_ifs with hi'
    · exact (h.2 (j + i) (by omega)).1
    · exact hfT
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [g] at hab
    split_ifs at hab with ha' hb' hb'
    · rcases lt_trichotomy a b with hlt | heq | hgt
      · exact absurd hab (h.edge_ne (by omega) (by omega))
      · exact heq
      · exact absurd hab.symm (h.edge_ne (by omega) (by omega))
    · exact absurd hab.symm (hfne _ (by omega))
    · exact absurd hab (hfne _ (by omega))
    · omega
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    have := h.1 (show j + a ≤ d by omega) (show j + b ≤ d by omega) hab
    omega
  · intro i hi
    simp only [g]
    split_ifs with hi'
    · rw [Nat.mod_eq_of_lt hi', ← add_assoc]
      exact (h.2 (j + i) (by omega)).2
    · rw [show i + 1 = l by omega, Nat.mod_self, add_zero, show j + i = d by omega]
      exact hf

open Classical in
/-- **A nonempty set of edges in which every vertex has even degree contains a cycle.**  A loop is
a cycle.  Otherwise take a longest path in `T`; its last vertex has even degree, so a second edge
of `T` leaves it, and by maximality that edge returns to the path and closes a cycle. -/
theorem exists_isCycle_subset (hT : T.Nonempty) (hev : ∀ v, Even (G.deg T v)) :
    ∃ C ⊆ T, G.IsCycle C := by
  by_cases hloop : ∃ f ∈ T, G.src f = G.tgt f
  · obtain ⟨f, hfT, hft⟩ := hloop
    refine ⟨{f}, singleton_subset_iff.2 hfT, 1, one_pos, fun _ => f, fun _ => G.src f,
      fun a ha b hb _ => by simp only [Set.mem_Iio] at ha hb; omega,
      fun a ha b hb _ => by simp only [Set.mem_Iio] at ha hb; omega,
      fun i _ => Or.inl ⟨rfl, hft.symm⟩, by simp⟩
  push Not at hloop
  obtain ⟨f₀, hf₀⟩ := hT
  -- a path with one edge
  have hP1 : ∃ x e, G.IsPathIn T 1 x e := by
    refine ⟨fun i => if i = 0 then G.src f₀ else G.tgt f₀, fun _ => f₀, ?_, fun i hi => ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Iic] at ha hb
      rcases Nat.lt_or_ge a 1 with ha' | ha' <;> rcases Nat.lt_or_ge b 1 with hb' | hb'
      · omega
      · simp only [show a = 0 by omega, show b ≠ 0 by omega, if_true, if_false] at hab
        exact absurd hab (hloop f₀ hf₀)
      · simp only [show b = 0 by omega, show a ≠ 0 by omega, if_true, if_false] at hab
        exact absurd hab.symm (hloop f₀ hf₀)
      · omega
    · obtain rfl : i = 0 := by omega
      exact ⟨hf₀, Or.inl ⟨by simp, by simp⟩⟩
  -- a longest path
  set P : ℕ → Prop := fun d => ∃ x e, G.IsPathIn T d x e
  have hbound : ∀ d, P d → d + 1 ≤ n := fun d ⟨x, e, h⟩ => h.succ_le
  have h1n : 1 ≤ n := by have := hbound 1 hP1; omega
  set D := Nat.findGreatest P n
  have hD : P D := Nat.findGreatest_spec h1n hP1
  have hD1 : 1 ≤ D := Nat.le_findGreatest h1n hP1
  have hmax : ¬P (D + 1) := fun hP =>
    Nat.findGreatest_is_greatest (Nat.lt_succ_self D) (by have := hbound _ hP; omega) hP
  obtain ⟨x, e, hp⟩ := hD
  -- a second edge at the last vertex
  have he₀ := hp.2 (D - 1) (by omega)
  rw [show D - 1 + 1 = D by omega] at he₀
  have hinc₀ : G.inc (x D) (e (D - 1)) = 1 := by
    rw [inc_of_joins he₀.2]
    have : x (D - 1) ≠ x D := fun hx => by
      have := hp.1 (show D - 1 ≤ D by omega) (le_refl D) hx; omega
    simp [this]
  have hrest : ∑ f ∈ T.erase (e (D - 1)), G.inc (x D) f ≠ 0 := by
    intro h0
    have := hev (x D)
    rw [deg, ← add_sum_erase _ _ he₀.1, hinc₀, h0] at this
    exact Nat.not_even_one this
  obtain ⟨f, hf, hfinc⟩ := exists_ne_zero_of_sum_ne_zero hrest
  obtain ⟨hfe, hfT⟩ := mem_erase.1 hf
  -- the other end of `f`
  set w := if G.src f = x D then G.tgt f else G.src f
  have hfw : G.Joins f (x D) w := by
    by_cases hs : G.src f = x D
    · simp only [w, hs, if_true]; exact Or.inl ⟨hs, rfl⟩
    · have ht : G.tgt f = x D := by
        unfold inc at hfinc; by_contra ht; simp [hs, ht] at hfinc
      simp only [w, hs, if_false]; exact Or.inr ⟨rfl, ht⟩
  -- by maximality the other end lies on the path
  have hon : ∃ j ≤ D, x j = w := by
    by_contra hnot
    push Not at hnot
    exact hmax ⟨_, _, hp.extend hfT hfw hnot⟩
  obtain ⟨j, hjD, hjw⟩ := hon
  have hjD' : j < D := by
    refine lt_of_le_of_ne hjD fun hjD => ?_
    subst hjD
    rcases hfw with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact hloop f hfT (hs.trans (hjw.trans ht.symm))
    · exact hloop f hfT (hs.trans (hjw.symm.trans ht.symm))
  exact hp.exists_isCycle hjD' hfT (hjw ▸ hfw) hfe

/-! ### The cycle matroid -/

/-- Over `ZMod 2`, a finite family is linearly independent iff no nonempty subfamily sums to
zero. -/
theorem linearIndepOn_iff_sum {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : Fin m → V)
    (S : Finset (Fin m)) :
    LinearIndepOn (ZMod 2) v (S : Set (Fin m)) ↔ ∀ T ⊆ S, ∑ e ∈ T, v e = 0 → T = ∅ := by
  classical
  rw [linearIndepOn_iff']
  refine ⟨fun h T hTS hsum => eq_empty_of_forall_notMem fun i hi =>
    one_ne_zero (h T (fun _ => 1) (coe_subset.2 hTS) (by simpa using hsum) i hi),
    fun h t g hts hsum i hi => ?_⟩
  have h01 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hT := h (t.filter fun i => g i ≠ 0) ((filter_subset _ _).trans (coe_subset.1 hts)) (by
    rw [← hsum, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hgj : g j = 0
    · simp [hgj]
    · simp [h01 _ hgj])
  by_contra hgi
  exact (eq_empty_iff_forall_notMem.1 hT) i (mem_filter.2 ⟨hi, hgi⟩)

/-- An edge set is independent iff every nonempty subset has a vertex of odd degree. -/
theorem indep_iff_odd (S : Finset (Fin m)) :
    G.cycleMatroid.Indep (S : Set (Fin m)) ↔
      ∀ T ⊆ S, T.Nonempty → ∃ v, ¬Even (G.deg T v) := by
  rw [cycleMatroid, binaryMatroid_indep, linearIndepOn_iff_sum]
  refine forall₂_congr fun T _ => ?_
  rw [sum_colZ_eq_zero_iff]
  refine ⟨fun h hT => ?_, fun h hev => ?_⟩
  · by_contra hall
    push Not at hall
    exact hT.ne_empty (h hall)
  · by_contra hne
    obtain ⟨v, hv⟩ := h (nonempty_iff_ne_empty.2 hne)
    exact hv (hev v)

/-- **The cycle matroid.**  An edge set is independent in `cycleMatroid G` iff it contains no
cycle. -/
theorem indep_iff (S : Finset (Fin m)) :
    G.cycleMatroid.Indep (S : Set (Fin m)) ↔ ∀ C, G.IsCycle C → ¬C ⊆ S := by
  rw [indep_iff_odd]
  refine ⟨fun h C hC hCS => ?_, fun h T hTS hT => ?_⟩
  · obtain ⟨v, hv⟩ := h C hCS hC.nonempty
    exact hv (hC.even_deg v)
  · by_contra hev
    push Not at hev
    obtain ⟨C, hCT, hC⟩ := exists_isCycle_subset hT hev
    exact h C hC (hCT.trans hTS)

/-- **The circuits of the cycle matroid are the cycles.** -/
theorem isCircuit_iff (C : Finset (Fin m)) :
    G.cycleMatroid.IsCircuit (C : Set (Fin m)) ↔ G.IsCycle C := by
  constructor
  · intro h
    have hdep := h.not_indep
    rw [indep_iff] at hdep
    push Not at hdep
    obtain ⟨C', hC', hC'C⟩ := hdep
    have hC'dep : ¬G.cycleMatroid.Indep (C' : Set (Fin m)) :=
      fun hi => (indep_iff C').1 hi C' hC' subset_rfl
    rwa [← coe_inj.1 (h.eq_of_not_indep_subset hC'dep (coe_subset.2 hC'C))]
  · intro h
    refine Matroid.isCircuit_iff_forall_ssubset.2 ⟨⟨fun hi => (indep_iff C).1 hi C h subset_rfl,
      by simp⟩, fun I hI => ?_⟩
    obtain ⟨I, rfl⟩ := exists_finset I
    refine (indep_iff I).2 fun C' hC' hC'I => ?_
    have hIC : I ⊂ C := coe_ssubset.1 hI
    have := h.eq_of_subset (hC'I.trans hIC.subset) hC'.nonempty hC'.even_deg
    exact hIC.ne (hIC.subset.antisymm (this ▸ hC'I))

/-- An edge on no cycle lies in every base (it is a coloop). -/
theorem mem_of_isBase {B : Finset (Fin m)} (hB : G.cycleMatroid.IsBase (B : Set (Fin m)))
    {f : Fin m} (hf : ∀ C, G.IsCycle C → f ∉ C) : f ∈ B := by
  by_contra hfB
  have hC := hB.fundCircuit_isCircuit (by simp) (by simpa using hfB)
  obtain ⟨C, hCeq⟩ := exists_finset (G.cycleMatroid.fundCircuit f ↑B)
  rw [← hCeq, isCircuit_iff] at hC
  exact hf C hC (by rw [← mem_coe, hCeq]; exact Matroid.mem_fundCircuit _ _ _)

/-- For a base `B`, `e ∉ B` and a cycle `C ⊆ B + e`, the fundamental circuit `C(B, e)` is `C`. -/
theorem fundCircuit_eq {B C : Finset (Fin m)} (hB : G.cycleMatroid.IsBase (B : Set (Fin m)))
    {e : Fin m} (hC : G.IsCycle C) (hCB : C ⊆ insert e B) :
    G.cycleMatroid.fundCircuit e ↑B = ↑C :=
  (((isCircuit_iff C).2 hC).eq_fundCircuit_of_subset hB.indep
    (by rw [← coe_insert]; exact coe_subset.2 hCB)).symm

/-- Every column of the incidence matrix has coordinate sum `2 = 0`. -/
theorem sum_inc (e : Fin m) : ∑ v, G.inc v e = 2 := by
  simp [inc, sum_add_distrib]

/-- **The rank of a graph is at most `n - 1`** (for `n ≥ 1`): the columns lie in the hyperplane
of vectors with coordinate sum `0`. -/
theorem rank_le (hn : 1 ≤ n) : rank G.cycleMatroid + 1 ≤ n := by
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun y => ∑ v, y v, map_add' := fun _ _ => sum_add_distrib,
      map_smul' := fun c y => by simp [mul_sum] }
  have hrange : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.2 fun c _ => ⟨Pi.single ⟨0, hn⟩ c, ?_⟩
    simp [φ]
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hdim
  have hspan : Submodule.span (ZMod 2) (colZ G.incidence '' Set.univ) ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, -, rfl⟩
    show ∑ v, (G.inc v e : ZMod 2) = 0
    rw [← Nat.cast_sum, sum_inc]
    decide
  have hrk := eRk_binaryMatroid G.incidence univ
  rw [coe_univ] at hrk
  have hle := Submodule.finrank_mono hspan
  have hcast : rank G.cycleMatroid = Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (colZ G.incidence '' Set.univ)) := by
    have h1 : rank G.cycleMatroid = (G.cycleMatroid.eRk Set.univ).toNat := by
      rw [rank, ← Matroid.eRk_ground, cycleMatroid_E]
    rw [h1, cycleMatroid, hrk, ENat.toNat_coe]
  omega

/-! ### Rank circuits and Corollary `cor:classes` -/

/-- The Boolean rank circuit of Binary.lean for the incidence matrix (`n` rows) outputs the
binary digits of the rank of the cycle matroid, with `m(9n² + 5n) + 11n⌈log₂(n+1)⌉` gates
(`Nat.size n = ⌈log₂(n+1)⌉`). -/
theorem rankCircuit :
    (binaryRankCircuit G.incidence).size = m * (9 * n ^ 2 + 5 * n) + n * (11 * Nat.size n) ∧
      ∀ S : Finset (Fin m),
        (bitsVal ((binaryRankCircuit G.incidence).eval boolInterp (indicator S)) : ℕ∞)
          = G.cycleMatroid.eRk (S : Set (Fin m)) :=
  ⟨binaryRankCircuit_size _, binaryRankCircuit_rank _⟩

/-- **Corollary `cor:classes`, item 5, graphic matroids.**  For a multigraph with `n` vertices and `m`
edges, maximum-weight spanning forests are computed at every `w ∈ ℝ^m` by a signed tropical
circuit with at most `100(m+1)²(n+1)²` gates. -/
theorem corollaryC_graphic :
    ∃ C : Circuit STOp m, C.size ≤ 100 * (m + 1) ^ 2 * (n + 1) ^ 2 ∧
      ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight G.cycleMatroid w] :=
  corollaryC_binary_poly G.incidence

end Multigraph

end SignedTropical.Classes.Graphic
