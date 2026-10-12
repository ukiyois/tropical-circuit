import SignedTropical.Rainbow.Star
import SignedTropical.Rainbow.PossiblyOptimal

/-!
# Querying `P_t` is NP-hard: the reduction

`greedy_intersection.tex`, Proposition `prop:nphard`.  Complexity classes are not formalized, so
neither the NP-completeness of rainbow `s`–`t` path, which the proof cites, nor the membership of
the problem in NP (Step 1) appears here.  This module formalizes the reduction, Steps 2 to 4.

* `HasRainbowPath G col s t`: the multigraph `G` with edge colors `col` has a rainbow path from
  `s` to `t`.
* `exists_path_of_isCycle`: deleting an edge from a cycle leaves a path between its ends.
* `isSpanningTree_image`: edges joining every vertex but a root to a vertex of smaller height form
  a spanning tree.
* `reduction H hn s t`, `redColor hq col`, `redWeight`: the instance of Step 2, for a multigraph
  `H` on `n` vertices with colors in `C = Fin q`, vertices `s, t`, and `h ≥ n, q`.  Its `h + 2`
  vertices are `V(H)` padded with isolated vertices to `h` vertices (`vP`), `z` (`vZ`) and `y`
  (`vY`).  Its `|E(H)| + 2 + h²` edges are the edges of `H` (weight `5`, their colors),
  `e* = st` and `f = ys` (weight `0`, the new color `c*`), and an edge `zx` for every `x ∈ Fin h`
  and every color of `C ∪ X = Fin h` (weight `10`).  There are `h + 1` colors.
* `rank_reduction`: the instance has rank `h + 1`, the number of colors, so its bases are its
  spanning trees.
* `hasRainbowPath_of_theta_le` (Step 3), `exists_rainbowBase_of_hasRainbowPath` (Step 4),
  `exists_rainbowBase_theta_le_iff`: the instance has a rainbow base `T` with `θ(T) ≤ 5` iff `H`
  has a rainbow `s`–`t` path.
* `exists_rainbowSpanningTree_theta_le_iff` (Proposition `prop:nphard`, Steps 2 to 4): the same
  for rainbow spanning trees, that is, `P_5` contains a rainbow spanning tree iff `H` has a
  rainbow `s`–`t` path.
-/

open Finset SignedTropical.Classes.Graphic

namespace SignedTropical.Rainbow.Graphs

open SignedTropical.Rainbow SignedTropical.Rainbow.Pos

/-! ### Paths and trees -/

section Paths

variable {n m q : ℕ} {G : Multigraph n m}

/-- `G`, with edge colors `col`, has a rainbow path from `s` to `t`: pairwise distinct vertices
`x 0 = s, x 1, …, x d = t` and edges `e 0, …, e (d - 1)` of pairwise distinct colors, `e i`
joining `x i` and `x (i + 1)`. -/
def HasRainbowPath (G : Multigraph n m) (col : Fin m → Fin q) (s t : Fin n) : Prop :=
  ∃ (d : ℕ) (x : Fin (d + 1) → Fin n) (e : Fin d → Fin m), x 0 = s ∧ x (Fin.last d) = t ∧
    Function.Injective x ∧ Function.Injective (col ∘ e) ∧
    ∀ i, G.Joins (e i) (x i.castSucc) (x i.succ)

/-- A rainbow path from `s` to `t`, read backwards, goes from `t` to `s`. -/
theorem HasRainbowPath.symm {col : Fin m → Fin q} {s t : Fin n} (h : HasRainbowPath G col s t) :
    HasRainbowPath G col t s := by
  obtain ⟨d, x, e, hs, ht, hx, he, hj⟩ := h
  refine ⟨d, x ∘ Fin.rev, e ∘ Fin.rev, by simpa using ht, by simpa using hs,
    hx.comp Fin.rev_injective, he.comp Fin.rev_injective, fun i => ?_⟩
  have := hj i.rev
  rw [← Fin.rev_succ, ← Fin.rev_castSucc] at this
  exact joins_comm.1 this

/-- **Deleting an edge from a cycle leaves a path between its ends.**  If `g` lies on the cycle
`C`, there are pairwise distinct vertices `x 0, …, x d` and pairwise distinct edges
`e 0, …, e (d - 1)` of `C - g`, `e i` joining `x i` and `x (i + 1)`, and `g` joins `x d` and
`x 0`. -/
theorem exists_path_of_isCycle {C : Finset (Fin m)} (hC : G.IsCycle C) {g : Fin m}
    (hg : g ∈ C) :
    ∃ (d : ℕ) (x : Fin (d + 1) → Fin n) (e : Fin d → Fin m), Function.Injective x ∧
      Function.Injective e ∧ (∀ i, e i ∈ C ∧ e i ≠ g ∧ G.Joins (e i) (x i.castSucc) (x i.succ)) ∧
      G.Joins g (x (Fin.last d)) (x 0) := by
  obtain ⟨l, hl, E, X, hE, hX, hJ, rfl⟩ := hC
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hg
  rw [mem_range] at hj
  obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, by omega⟩
  -- `r i = j + 1 + i (mod d + 1)` walks around the cycle, starting after `g = E j`
  let r : ℕ → ℕ := fun i => (j + 1 + i) % (d + 1)
  have hr : ∀ i, r i < d + 1 := fun i => Nat.mod_lt _ d.succ_pos
  have hrinj : ∀ {a b}, a < d + 1 → b < d + 1 → r a = r b → a = b := fun ha hb hab => by
    have := Nat.ModEq.add_left_cancel' (j + 1) hab
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hrd : r d = j := by
    show (j + 1 + d) % (d + 1) = j
    rw [show j + 1 + d = j + (d + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hrsucc : ∀ i, (r i + 1) % (d + 1) = r (i + 1) := fun i => by
    show ((j + 1 + i) % (d + 1) + 1) % (d + 1) = (j + 1 + (i + 1)) % (d + 1)
    rw [Nat.mod_add_mod, add_assoc]
  refine ⟨d, fun i => X (r i), fun i => E (r i),
    fun a b hab => Fin.ext (hrinj a.2 b.2 (hX (hr a) (hr b) hab)),
    fun a b hab => Fin.ext (hrinj (Nat.lt_succ_of_lt a.2) (Nat.lt_succ_of_lt b.2)
      (hE (hr a) (hr b) hab)),
    fun i => ⟨mem_image_of_mem E (mem_range.2 (hr i)), fun h => ?_, ?_⟩, ?_⟩
  · have := hrinj (Nat.lt_succ_of_lt i.2) (Nat.lt_succ_self d) ((hE (hr i) hj h).trans hrd.symm)
    have := i.2
    omega
  · simpa [hrsucc] using hJ (r i) (hr i)
  · have h0 : r 0 = (j + 1) % (d + 1) := by simp [r]
    simpa [hrd, h0] using hJ j hj

/-- **Spanning trees from parent edges.**  Let `r` be a vertex, `ρ` a height on the vertices, and
`p v`, for every vertex `v ≠ r`, an edge joining `v` to a vertex of smaller height.  Then the
edges `p v` are pairwise distinct and form a spanning tree. -/
theorem isSpanningTree_image (r : Fin n) (ρ : Fin n → ℕ) (p : Fin n → Fin m)
    (hp : ∀ v ≠ r, ∃ u, G.Joins (p v) v u ∧ ρ u < ρ v) :
    Set.InjOn p {v | v ≠ r} ∧ IsSpanningTree G ((univ.erase r).image p) := by
  have hinj : Set.InjOn p {v | v ≠ r} := by
    intro v hv w hw hvw
    by_contra hne
    obtain ⟨u, hu, hρu⟩ := hp v hv
    obtain ⟨u', hu', hρu'⟩ := hp w hw
    rw [hvw] at hu
    rcases Multigraph.eq_or_eq_of_joins hu' (Multigraph.inc_left_ne_zero hu) with h | h
    · exact hne h
    · rcases Multigraph.eq_or_eq_of_joins hu (Multigraph.inc_left_ne_zero hu') with h' | h'
      · exact hne h'.symm
      · subst h h'
        omega
  refine ⟨hinj, isSpanningTree_iff_indep.2
    ⟨(Multigraph.indep_iff_odd _).2 fun S hS ⟨g, hg⟩ => ?_, ?_⟩⟩
  · -- a vertex of largest height among those whose edge lies in `S` has degree `1` in `S`
    obtain ⟨v, hvA, hmax⟩ := ((univ.erase r).filter fun v => p v ∈ S).exists_max_image ρ (by
      obtain ⟨v, hv, rfl⟩ := mem_image.1 (hS hg)
      exact ⟨v, mem_filter.2 ⟨hv, hg⟩⟩)
    obtain ⟨hvr, hvS⟩ := mem_filter.1 hvA
    obtain ⟨u, hu, hρ⟩ := hp v (ne_of_mem_erase hvr)
    refine ⟨v, ?_⟩
    rw [Multigraph.deg, sum_eq_single (p v) (fun g hg hne => ?_) (absurd hvS),
      Multigraph.inc_of_joins hu, if_pos rfl, if_neg (by rintro rfl; omega)]
    · decide
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 (hS hg)
      by_contra hinc
      obtain ⟨u', hu', hρ'⟩ := hp w (ne_of_mem_erase hw)
      rcases Multigraph.eq_or_eq_of_joins hu' hinc with rfl | rfl
      · exact hne rfl
      · have := hmax w (mem_filter.2 ⟨hw, hg⟩)
        omega
  · rw [card_image_of_injOn (hinj.mono fun v hv => ne_of_mem_erase hv),
      card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]
    have := r.pos
    omega

end Paths

/-! ### The instance of Step 2 -/

section Instance

variable {h mH : ℕ}

/-- The vertex `a` of `V(H)`, padded to `Fin h`, as a vertex of the instance. -/
def vP (a : Fin h) : Fin (h + 2) := a.castSucc.castSucc

/-- The vertex `z` of the instance. -/
def vZ : Fin (h + 2) := (Fin.last h).castSucc

/-- The vertex `y` of the instance. -/
def vY : Fin (h + 2) := Fin.last (h + 1)

theorem vP_injective : Function.Injective (vP : Fin h → Fin (h + 2)) :=
  (Fin.castSucc_injective _).comp (Fin.castSucc_injective _)

@[simp] theorem vP_inj {a b : Fin h} : vP a = vP b ↔ a = b := vP_injective.eq_iff

@[simp] theorem vP_ne_vZ (a : Fin h) : vP a ≠ vZ := fun h' =>
  Fin.castSucc_ne_last a (Fin.castSucc_injective _ h')

@[simp] theorem vP_ne_vY (a : Fin h) : vP a ≠ vY := Fin.castSucc_ne_last _

@[simp] theorem vZ_ne_vY : (vZ : Fin (h + 2)) ≠ vY := Fin.castSucc_ne_last _

/-- Every vertex is `vP a`, `z` or `y`. -/
theorem vertex_cases (v : Fin (h + 2)) : (∃ a, v = vP a) ∨ v = vZ ∨ v = vY := by
  rcases Fin.eq_castSucc_or_eq_last v with ⟨w, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last w with ⟨a, rfl⟩ | rfl
    · exact .inl ⟨a, rfl⟩
    · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- A function on the vertices, by its values at the vertices `vP a`, at `z` and at `y`. -/
def onVertices {α : Type*} (fP : Fin h → α) (fz fy : α) : Fin (h + 2) → α :=
  Fin.lastCases fy (Fin.lastCases fz fP)

section OnVertices

variable {α : Type*} (fP : Fin h → α) (fz fy : α)

@[simp] theorem onVertices_vP (a : Fin h) : onVertices fP fz fy (vP a) = fP a := by
  simp [onVertices, vP]

@[simp] theorem onVertices_vZ : onVertices fP fz fy vZ = fz := by simp [onVertices, vZ]

@[simp] theorem onVertices_vY : onVertices fP fz fy vY = fy := by simp [onVertices, vY]

end OnVertices

/-- The edges of the instance: `inl (inl a)` is the edge `a` of `H`, `inl (inr 0)` is `e*`,
`inl (inr 1)` is `f`, and `inr (x, c)` is the edge `zx` of color `c`. -/
abbrev Edge (mH h : ℕ) := (Fin mH ⊕ Fin 2) ⊕ Fin h × Fin h

/-- The numbering of the `|E(H)| + 2 + h²` edges. -/
def edgeEquiv : Fin (mH + 2 + h * h) ≃ Edge mH h :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm finProdFinEquiv.symm)

/-- The edge `a` of `H`. -/
def eH (a : Fin mH) : Fin (mH + 2 + h * h) := edgeEquiv.symm (.inl (.inl a))

/-- The edge `e* = st`. -/
def eS : Fin (mH + 2 + h * h) := edgeEquiv.symm (.inl (.inr 0))

/-- The edge `f = ys`. -/
def eF : Fin (mH + 2 + h * h) := edgeEquiv.symm (.inl (.inr 1))

/-- The edge `zx` of color `c`. -/
def eZ (x c : Fin h) : Fin (mH + 2 + h * h) := edgeEquiv.symm (.inr (x, c))

/-- Every edge is an edge of `H`, `e*`, `f` or an edge `zx`. -/
theorem edge_cases (e : Fin (mH + 2 + h * h)) :
    (∃ a, e = eH a) ∨ e = eS ∨ e = eF ∨ ∃ x c, e = eZ x c := by
  obtain ⟨k, rfl⟩ := edgeEquiv.symm.surjective e
  rcases k with (a | i) | ⟨x, c⟩
  · exact .inl ⟨a, rfl⟩
  · fin_cases i
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr ⟨x, c, rfl⟩))

@[simp] theorem eH_inj {a b : Fin mH} : (eH a : Fin (mH + 2 + h * h)) = eH b ↔ a = b := by
  simp [eH]

@[simp] theorem eH_ne_eS (a : Fin mH) : (eH a : Fin (mH + 2 + h * h)) ≠ eS := by simp [eH, eS]

@[simp] theorem eH_ne_eF (a : Fin mH) : (eH a : Fin (mH + 2 + h * h)) ≠ eF := by simp [eH, eF]

@[simp] theorem eS_ne_eF : (eS : Fin (mH + 2 + h * h)) ≠ eF := by simp [eS, eF]

@[simp] theorem eZ_ne_eF (x c : Fin h) : (eZ x c : Fin (mH + 2 + h * h)) ≠ eF := by
  simp [eZ, eF]

variable {n q : ℕ} (H : Multigraph n mH) (hn : n ≤ h) (s t : Fin n)

/-- The vertex `a` of `H` as a vertex of the instance. -/
def vH (a : Fin n) : Fin (h + 2) := vP (Fin.castLE hn a)

theorem vH_injective : Function.Injective (vH hn) :=
  vP_injective.comp (Fin.castLE_injective hn)

/-- The ends of the edges of the instance. -/
def ends : Edge mH h → Fin (h + 2) × Fin (h + 2)
  | .inl (.inl a) => (vH hn (H.src a), vH hn (H.tgt a))
  | .inl (.inr i) => if i = 0 then (vH hn s, vH hn t) else (vY, vH hn s)
  | .inr (x, _) => (vZ, vP x)

/-- **The instance of Step 2**: the multigraph on `V(H)`, padded to `h` vertices, and `z`, `y`,
with the edges of `H`, the edges `e* = st` and `f = ys`, and an edge `zx` for every `x ∈ Fin h`
and every color of `C ∪ X = Fin h`. -/
def reduction : Multigraph (h + 2) (mH + 2 + h * h) :=
  ⟨fun e => (ends H hn s t (edgeEquiv e)).1, fun e => (ends H hn s t (edgeEquiv e)).2⟩

section Ends

variable {H hn s t}

@[simp] theorem src_eH (a : Fin mH) : (reduction H hn s t).src (eH a) = vH hn (H.src a) := by
  simp [reduction, eH, ends]

@[simp] theorem tgt_eH (a : Fin mH) : (reduction H hn s t).tgt (eH a) = vH hn (H.tgt a) := by
  simp [reduction, eH, ends]

@[simp] theorem src_eS : (reduction H hn s t).src eS = vH hn s := by simp [reduction, eS, ends]

@[simp] theorem tgt_eS : (reduction H hn s t).tgt eS = vH hn t := by simp [reduction, eS, ends]

@[simp] theorem src_eF : (reduction H hn s t).src eF = vY := by simp [reduction, eF, ends]

@[simp] theorem tgt_eF : (reduction H hn s t).tgt eF = vH hn s := by simp [reduction, eF, ends]

@[simp] theorem src_eZ (x c : Fin h) : (reduction H hn s t).src (eZ x c) = vZ := by
  simp [reduction, eZ, ends]

@[simp] theorem tgt_eZ (x c : Fin h) : (reduction H hn s t).tgt (eZ x c) = vP x := by
  simp [reduction, eZ, ends]

theorem joins_eH_iff {a : Fin mH} {u w : Fin n} :
    (reduction H hn s t).Joins (eH a) (vH hn u) (vH hn w) ↔ H.Joins a u w := by
  simp [Multigraph.Joins, (vH_injective hn).eq_iff]

theorem joins_eH_vH {a : Fin mH} {u w : Fin (h + 2)}
    (hj : (reduction H hn s t).Joins (eH a) u w) : (∃ u', u = vH hn u') ∧ ∃ w', w = vH hn w' := by
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [src_eH] at h1 <;> rw [tgt_eH] at h2
  · exact ⟨⟨_, h1.symm⟩, _, h2.symm⟩
  · exact ⟨⟨_, h2.symm⟩, _, h1.symm⟩

theorem joins_eS_iff {u w : Fin (h + 2)} : (reduction H hn s t).Joins eS u w ↔
    (u = vH hn s ∧ w = vH hn t) ∨ (u = vH hn t ∧ w = vH hn s) := by
  rw [Multigraph.Joins, src_eS, tgt_eS]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  exacts [.inl ⟨h1.symm, h2.symm⟩, .inr ⟨h2.symm, h1.symm⟩, .inl ⟨h1.symm, h2.symm⟩,
    .inr ⟨h2.symm, h1.symm⟩]

theorem joins_eF : (reduction H hn s t).Joins eF vY (vH hn s) :=
  .inl ⟨src_eF, tgt_eF⟩

theorem joins_eZ (x c : Fin h) : (reduction H hn s t).Joins (eZ x c) (vP x) vZ :=
  .inr ⟨src_eZ x c, tgt_eZ x c⟩

/-- Only `f` has an end at `y`. -/
theorem inc_vY (e : Fin (mH + 2 + h * h)) :
    (reduction H hn s t).inc vY e = if e = eF then 1 else 0 := by
  rcases edge_cases e with ⟨a, rfl⟩ | rfl | rfl | ⟨x, c, rfl⟩ <;>
    simp [Multigraph.inc, vH]

end Ends

variable (hq : q ≤ h) (col : Fin mH → Fin q)

/-- The colors of the instance, in `Fin (h + 1)`: an edge of `H` keeps its color, in
`C = Fin q ⊆ Fin h`; `e*` and `f` have the new color `c* = h`; the edge `zx` of color
`c ∈ C ∪ X = Fin h` has color `c`. -/
def redColor (e : Fin (mH + 2 + h * h)) : Fin (h + 1) :=
  match edgeEquiv e with
  | .inl (.inl a) => (Fin.castLE hq (col a)).castSucc
  | .inl (.inr _) => Fin.last h
  | .inr (_, c) => c.castSucc

/-- The weights of the instance: `5` on the edges of `H`, `0` on `e*` and `f`, and `10` on the
edges `zx`. -/
def redWeight (e : Fin (mH + 2 + h * h)) : ℝ :=
  match edgeEquiv e with
  | .inl (.inl _) => 5
  | .inl (.inr _) => 0
  | .inr _ => 10

section Values

variable {hq col}

@[simp] theorem redColor_eH (a : Fin mH) :
    redColor hq col (eH a) = (Fin.castLE hq (col a)).castSucc := by simp [redColor, eH]

@[simp] theorem redColor_eS : redColor hq col eS = Fin.last h := by simp [redColor, eS]

@[simp] theorem redColor_eF : redColor hq col eF = Fin.last h := by simp [redColor, eF]

@[simp] theorem redColor_eZ (x c : Fin h) : redColor hq col (eZ x c) = c.castSucc := by
  simp [redColor, eZ]

@[simp] theorem redWeight_eH (a : Fin mH) : redWeight (eH a : Fin (mH + 2 + h * h)) = 5 := by
  simp [redWeight, eH]

@[simp] theorem redWeight_eS : redWeight (eS : Fin (mH + 2 + h * h)) = 0 := by
  simp [redWeight, eS]

@[simp] theorem redWeight_eF : redWeight (eF : Fin (mH + 2 + h * h)) = 0 := by
  simp [redWeight, eF]

@[simp] theorem redWeight_eZ (x c : Fin h) : redWeight (eZ x c : Fin (mH + 2 + h * h)) = 10 := by
  simp [redWeight, eZ]

theorem redWeight_le (e : Fin (mH + 2 + h * h)) : redWeight e ≤ 10 := by
  rcases edge_cases e with ⟨a, rfl⟩ | rfl | rfl | ⟨x, c, rfl⟩ <;> norm_num

end Values

/-! ### Steps 3 and 4 -/

/-- The instance is connected: its rank is `h + 1`, the number of its colors.  So its bases are
its spanning trees (`isSpanningTree_iff_isBase`). -/
theorem rank_reduction : rank (reduction H hn s t).cycleMatroid = h + 1 := by
  have hh : 0 < h := lt_of_lt_of_le s.pos hn
  have := (isSpanningTree_image (G := reduction H hn s t) vZ (onVertices (fun _ => 1) 0 2)
    (onVertices (fun b => eZ b ⟨0, hh⟩) eF eF) fun v hv => ?_).2.rank_eq
  · omega
  · rcases vertex_cases v with ⟨b, rfl⟩ | rfl | rfl
    · exact ⟨vZ, by simpa using joins_eZ b ⟨0, hh⟩, by simp⟩
    · exact absurd rfl hv
    · exact ⟨vH hn s, by simpa using joins_eF, by simp [vH]⟩

/-- **Step 3, forward.**  If the instance has a rainbow base `T` with `θ(T) ≤ 5`, then `H` has a
rainbow `s`–`t` path.  The edge `f` lies on no cycle, so `f ∈ T` and `e* ∉ T`; the
fundamental cycle of `e*` weighs at most `5`, so it avoids the edges at `z`, and deleting `e*`
from it leaves a rainbow path of `H` between `s` and `t`. -/
theorem hasRainbowPath_of_theta_le {T : Finset (Fin (mH + 2 + h * h))}
    (hT : IsRainbowBase (reduction H hn s t).cycleMatroid (redColor hq col) T)
    (hθ : theta (reduction H hn s t).cycleMatroid redWeight T ≤ 5) :
    HasRainbowPath H col s t := by
  set G := reduction H hn s t
  obtain ⟨hB, hR⟩ := hT
  -- `f` lies on no cycle, since `y` is an end of `f` only; so `f ∈ T`, and `e* ∉ T`
  have hfC : ∀ C, G.IsCycle C → eF ∉ C := fun C hC hf => by
    have hev := hC.even_deg vY
    rw [Multigraph.deg, sum_eq_single eF (fun g _ hg => by simp [G, inc_vY, hg])
      (fun h' => absurd hf h'), inc_vY, if_pos rfl] at hev
    exact Nat.not_even_one hev
  have hfT : eF ∈ T := Multigraph.mem_of_isBase hB hfC
  have heT : eS ∉ T := fun he => eS_ne_eF (hR (mem_coe.2 he) (mem_coe.2 hfT) (by simp))
  -- the fundamental cycle `C` of `e*`: its edges other than `e*` lie in `T` and weigh at most 5
  obtain ⟨C, hCeq⟩ := exists_finset (G.cycleMatroid.fundCircuit eS ↑T)
  have hC : G.IsCycle C := (Multigraph.isCircuit_iff C).1
    (hCeq ▸ hB.fundCircuit_isCircuit (by simp) (by simpa using heT))
  have hmem : ∀ g, g ∈ C ↔ g ∈ G.cycleMatroid.fundCircuit eS ↑T := fun g => by
    rw [← hCeq, mem_coe]
  have hCT : ∀ g ∈ C, g ≠ eS → g ∈ T := fun g hg hne =>
    mem_of_mem_fundCircuit ((hmem g).1 hg) hne
  have hw : ∀ g ∈ C, redWeight g ≤ 5 := fun g hg => by
    simpa using (theta_le_iff.1 hθ).2 eS heT g ((hmem g).1 hg)
  -- deleting `e*` from `C` leaves a path, whose edges are edges of `H`
  obtain ⟨d, X, E, hX, hE, hEC, hJ⟩ :=
    exists_path_of_isCycle hC ((hmem eS).2 (Matroid.mem_fundCircuit _ _ _))
  have hold : ∀ i, ∃ a, E i = eH a := fun i => by
    obtain ⟨hEi, hne, -⟩ := hEC i
    rcases edge_cases (E i) with ha | h' | h' | ⟨x, c, h'⟩
    · exact ha
    · exact absurd h' hne
    · exact absurd (h' ▸ hEi) (hfC C hC)
    · have := hw _ hEi
      rw [h', redWeight_eZ] at this
      norm_num at this
  choose a ha using hold
  have hvert : ∀ i, ∃ u, X i = vH hn u := fun i => by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have := (hEC j).2.2
      rw [ha] at this
      exact (joins_eH_vH this).1
    · rcases joins_eS_iff.1 hJ with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact ⟨_, h1⟩
  choose x hx using hvert
  -- its vertices are vertices of `H`, and it is rainbow since `T` is
  have hpath : HasRainbowPath H col (x 0) (x (Fin.last d)) := by
    refine ⟨d, x, a, rfl, rfl, fun i j hij => hX (by rw [hx, hx, hij]),
      fun i j hij => hE (hR (mem_coe.2 (hCT _ (hEC i).1 (hEC i).2.1))
        (mem_coe.2 (hCT _ (hEC j).1 (hEC j).2.1)) ?_), fun i => ?_⟩
    · simp only [Function.comp_apply] at hij
      rw [ha, ha, redColor_eH, redColor_eH, hij]
    · have := (hEC i).2.2
      rwa [ha, hx, hx, joins_eH_iff] at this
  have hst : G.Joins eS (vH hn (x (Fin.last d))) (vH hn (x 0)) := by
    rw [← hx, ← hx]
    exact hJ
  rcases joins_eS_iff.1 hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [vH_injective hn h1, vH_injective hn h2] at hpath
    exact hpath.symm
  · rwa [vH_injective hn h1, vH_injective hn h2] at hpath

/-- **Step 4, backward.**  If `H` has a rainbow `s`–`t` path `P`, the instance has a rainbow base
`T` with `θ(T) ≤ 5`: `P`, `f`, and an edge `zx` at every vertex `x` of `Fin h` other than the
vertices of `P` after `s`, colored by the colors of `C ∪ X` not on `P`. -/
theorem exists_rainbowBase_of_hasRainbowPath (hP : HasRainbowPath H col s t) :
    ∃ T, IsRainbowBase (reduction H hn s t).cycleMatroid (redColor hq col) T ∧
      theta (reduction H hn s t).cycleMatroid redWeight T ≤ 5 := by
  classical
  set G := reduction H hn s t
  obtain ⟨d, x, e, hs, ht, hx, hc, hJ⟩ := hP
  have he : Function.Injective e := hc.of_comp
  -- `f₁ j` is the vertex `x (j + 1)` and `f₂ j` the color of `e j`; a permutation `κ` of `Fin h`
  -- maps the first to the second
  let f₁ : Fin d → Fin h := fun j => Fin.castLE hn (x j.succ)
  have hf₁ : Function.Injective f₁ := fun j j' hjj =>
    Fin.succ_injective _ (hx (Fin.castLE_injective hn hjj))
  let f₂ : Fin d → Fin h := fun j => Fin.castLE hq (col (e j))
  have hf₂ : Function.Injective f₂ := fun j j' hjj => hc (Fin.castLE_injective hq hjj)
  let φ : Set.range f₁ ≃ Set.range f₂ :=
    (Equiv.ofInjective f₁ hf₁).symm.trans (Equiv.ofInjective f₂ hf₂)
  let κ : Equiv.Perm (Fin h) := φ.extendSubtype
  have hκ : ∀ j, κ (f₁ j) = f₂ j := fun j => by
    rw [Equiv.extendSubtype_apply_of_mem φ (f₁ j) ⟨j, rfl⟩]
    simp [φ]
  -- the tree: the edge `e j` from `x (j + 1)`, the edge `zx` of color `κ x` from every other
  -- vertex `x` of `Fin h`, and `f` from `y`; heights `ρ (x i) = i + 1`, `ρ z = 0`, `ρ y = 2`
  let teP : Fin h → Fin (mH + 2 + h * h) := fun b =>
    if hb : ∃ j, f₁ j = b then eH (e hb.choose) else eZ b (κ b)
  have hteP : ∀ j, teP (f₁ j) = eH (e j) := fun j => by
    have hb : ∃ j', f₁ j' = f₁ j := ⟨j, rfl⟩
    simp only [teP, dif_pos hb, hf₁ hb.choose_spec]
  let ρP : Fin h → ℕ := fun b =>
    if hb : ∃ i, Fin.castLE hn (x i) = b then hb.choose.val + 1 else 1
  have hρP : ∀ i, ρP (Fin.castLE hn (x i)) = i + 1 := fun i => by
    have hb : ∃ i', Fin.castLE hn (x i') = Fin.castLE hn (x i) := ⟨i, rfl⟩
    simp only [ρP, dif_pos hb, hx (Fin.castLE_injective hn hb.choose_spec)]
  have hρP1 : ∀ b, 1 ≤ ρP b := fun b => by
    simp only [ρP]
    split_ifs <;> omega
  let te := onVertices teP eF eF
  have hpar : ∀ v ≠ vZ, ∃ u, G.Joins (te v) v u ∧ onVertices ρP 0 2 u < onVertices ρP 0 2 v := by
    intro v hv
    rcases vertex_cases v with ⟨b, rfl⟩ | rfl | rfl
    · by_cases hb : ∃ j, f₁ j = b
      · obtain ⟨j, rfl⟩ := hb
        refine ⟨vH hn (x j.castSucc), ?_, ?_⟩
        · simp only [te, onVertices_vP, hteP]
          exact joins_comm.1 (joins_eH_iff.2 (hJ j))
        · simp only [vH, onVertices_vP, f₁, hρP, Fin.val_castSucc, Fin.val_succ]
          omega
      · refine ⟨vZ, ?_, ?_⟩
        · simp only [te, onVertices_vP, teP, dif_neg hb]
          exact joins_eZ b (κ b)
        · simp only [onVertices_vP, onVertices_vZ]
          exact hρP1 b
    · exact absurd rfl hv
    · refine ⟨vH hn s, ?_, ?_⟩
      · simp only [te, onVertices_vY]
        exact joins_eF
      · simp only [vH, onVertices_vP, onVertices_vY, ← hs, hρP, Fin.val_zero]
        omega
  obtain ⟨-, hST⟩ := isSpanningTree_image vZ _ te hpar
  set T := (univ.erase vZ).image te
  have hB := hST.isBase
  have hmemT : ∀ v ≠ vZ, te v ∈ T := fun v hv =>
    mem_image_of_mem te (mem_erase.2 ⟨hv, mem_univ v⟩)
  -- `T` is rainbow: the tree edge from `vP b` has color `κ b`, the one from `y` has color `c*`
  have hcolP : ∀ b, redColor hq col (teP b) = (κ b).castSucc := fun b => by
    by_cases hb : ∃ j, f₁ j = b
    · obtain ⟨j, rfl⟩ := hb
      rw [hteP, redColor_eH, hκ]
    · simp only [teP, dif_neg hb, redColor_eZ]
  have hR : IsRainbow (redColor hq col) T := by
    rintro _ hg _ hg' hgg
    obtain ⟨v, hv, rfl⟩ := mem_image.1 (mem_coe.1 hg)
    obtain ⟨w, hw, rfl⟩ := mem_image.1 (mem_coe.1 hg')
    have hvz := ne_of_mem_erase hv
    have hwz := ne_of_mem_erase hw
    rcases vertex_cases v with ⟨b, rfl⟩ | rfl | rfl <;>
      rcases vertex_cases w with ⟨b', rfl⟩ | rfl | rfl <;>
      simp_all [te, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  -- the cycle `P + e*` is the fundamental cycle of `e*`
  let Es : ℕ → Fin (mH + 2 + h * h) := fun k => if hk : k < d then eH (e ⟨k, hk⟩) else eS
  let Xs : ℕ → Fin (h + 2) := fun k => if hk : k < d + 1 then vH hn (x ⟨k, hk⟩) else vH hn s
  have hCcyc : G.IsCycle (insert eS (univ.image fun j => eH (e j))) := by
    refine ⟨d + 1, d.succ_pos, Es, Xs, fun k hk k' hk' hkk => ?_, fun k hk k' hk' hkk => ?_,
      fun k hk => ?_, ?_⟩
    · simp only [Set.mem_Iio] at hk hk'
      simp only [Es] at hkk
      split_ifs at hkk with h1 h2 h2
      · simpa using he (eH_inj.1 hkk)
      · exact absurd hkk (eH_ne_eS _)
      · exact absurd hkk.symm (eH_ne_eS _)
      · omega
    · simp only [Set.mem_Iio] at hk hk'
      simp only [Xs, dif_pos hk, dif_pos hk'] at hkk
      simpa using hx (vH_injective hn hkk)
    · by_cases hkd : k < d
      · have hk1 : k + 1 < d + 1 := by omega
        simp only [Es, Xs, dif_pos hkd, dif_pos hk, Nat.mod_eq_of_lt hk1, dif_pos hk1]
        exact joins_eH_iff.2 (hJ ⟨k, hkd⟩)
      · obtain rfl : k = d := by omega
        simp only [Es, Xs, dif_neg (lt_irrefl k), dif_pos hk, Nat.mod_self, dif_pos k.succ_pos]
        exact joins_eS_iff.2 (.inr ⟨by rw [← ht]; rfl, by rw [← hs]; rfl⟩)
    · ext g
      simp only [mem_insert, mem_image, mem_univ, true_and, mem_range, Es]
      constructor
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨d, by omega, by simp⟩
        · exact ⟨j, by omega, by simp [j.2]⟩
      · rintro ⟨k, -, rfl⟩
        split_ifs with hkd
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
  have hfund := Multigraph.fundCircuit_eq hB hCcyc (by
    intro g hg
    rcases mem_insert.1 hg with rfl | hg
    · exact mem_insert_self _ _
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hg
      refine mem_insert_of_mem ?_
      have := hmemT (vP (f₁ j)) (vP_ne_vZ _)
      simpa only [te, onVertices_vP, hteP] using this)
  -- every exchange gains at most `5`
  refine ⟨T, ⟨hB, hR⟩, theta_le_iff.2 ⟨by norm_num, fun g hg g' hg' => ?_⟩⟩
  rcases edge_cases g with ⟨a, rfl⟩ | rfl | rfl | ⟨z', c, rfl⟩
  · linarith [redWeight_le g', redWeight_eH (h := h) a]
  · rw [hfund, mem_coe] at hg'
    rcases mem_insert.1 hg' with rfl | hg'
    · simp
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hg'
      norm_num
  · have := hmemT vY vZ_ne_vY.symm
    simp only [te, onVertices_vY] at this
    exact absurd this hg
  · linarith [redWeight_le g', redWeight_eZ (mH := mH) z' c]

/-- **Steps 3 and 4, for rainbow bases.**  The instance of Step 2 has a rainbow base `T`, the
colors as blocks, with `θ(T) ≤ 5` iff `H` has a rainbow `s`–`t` path. -/
theorem exists_rainbowBase_theta_le_iff :
    (∃ T, IsRainbowBase (reduction H hn s t).cycleMatroid (redColor hq col) T ∧
      theta (reduction H hn s t).cycleMatroid redWeight T ≤ 5) ↔ HasRainbowPath H col s t :=
  ⟨fun ⟨_, hT, hθ⟩ => hasRainbowPath_of_theta_le H hn s t hq col hT hθ,
    exists_rainbowBase_of_hasRainbowPath H hn s t hq col⟩

/-- **Proposition `prop:nphard`, the reduction (Steps 2 to 4).**  Let `H` be a multigraph on `n`
vertices with edge colors in `C = Fin q`, let `s, t` be vertices of `H`, and let `h ≥ n, q`.  The
instance of Step 2 has a rainbow spanning tree `T` with `θ(T) ≤ 5`, that is, `P_5` contains a
rainbow spanning tree, iff `H` has a rainbow `s`–`t` path.  The instance has `h + 2` vertices,
`|E(H)| + 2 + h²` edges, `h + 1` colors and weights `0, 5, 10` (its type records the first three),
so for `h = max(n, q)` its size is polynomial in that of `H`. -/
theorem exists_rainbowSpanningTree_theta_le_iff :
    (∃ T, IsSpanningTree (reduction H hn s t) T ∧ IsRainbow (redColor hq col) T ∧
      theta (reduction H hn s t).cycleMatroid redWeight T ≤ 5) ↔ HasRainbowPath H col s t := by
  rw [← exists_rainbowBase_theta_le_iff H hn s t hq col]
  refine exists_congr fun T => ?_
  rw [isSpanningTree_iff_isBase (G := reduction H hn s t) (by rw [rank_reduction]), IsRainbowBase,
    and_assoc]

end Instance

end SignedTropical.Rainbow.Graphs
