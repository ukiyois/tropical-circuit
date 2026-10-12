import SignedTropical.Matroid
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Circuit

/-!
# Rainbow bases: shared definitions

`greedy_intersection.tex`, Sections 4 and 5.  This module fixes the objects that every module
of the Phase 2 development refers to.  It contains definitions only, and the two facts needed
to state them (the ground set of a level piece and the disjointness of the level pieces).

Conventions, as in Phase 1: a matroid is `M : Matroid (Fin m)`, used with the hypothesis
`M.E = Set.univ`; sets of elements are `Finset (Fin m)`, coerced to `Set (Fin m)` for
Mathlib's API; `rk M S : ℕ` is the rank (`SignedTropical.rk`); weights are `Fin m → ℝ`.
The blocks `R_1, …, R_k` of the paper are the fibres of `blk : Fin m → Fin k`.

* `IsRainbow blk S`: `S` meets every block at most once.
* `blockSet blk Q`: `E_Q`, the union of the blocks in `Q`.
* `blocksMet blk S`: the blocks that `S` meets.
* `IsRainbowIndep N blk I`: `I` is independent in `N` and rainbow.
* `nu N blk`: `ν(N)`, the largest size of a rainbow independent set of `N`.
* `Av N blk`: `Av(N)`, the blocks missed by some rainbow independent set of size `ν(N)`.
* `IsRainbowBase M blk B`: a base of `M` that is rainbow.  When `k` is the rank of `M` it
  meets every block exactly once.
* `IsMinBase M u B`, `minBaseWeight M u`: minimum bases and `β_M(u) = min_B u(B)`.
* `Opt M blk w`: the least weight of a rainbow base.
* `shift blk w p`: `v = w - p_blk`; `Psi M blk w p`: the Lagrangian
  `Ψ(p) = Σ_b p_b + β_M(w - p_blk)`.
* `minBases M u`: the matroid `M^u`, the direct sum over the values `ℓ` of `u` of the level
  pieces `(M ↾ {u ≤ ℓ}) ／ {u < ℓ}`, whose ground sets are the level sets `{u = ℓ}`.
  That its bases are the minimum bases of `u` is Lemma `lem:minbases`(3).
* `theta M v B`, `Pos M v t`: `θ(B)` and the possibly optimal bases `P_t`
  (Definition `def:theta`).
* `connRel M e f`: `e = f`, or `e` and `f` lie on a common circuit; its classes are the
  connected components of Lemma `lem:minbases`(4).
* `IsAdmissible M blk v N`: Definition `def:admissible`, (F1)–(F5).
-/

open Finset

namespace SignedTropical.Rainbow

variable {m k : ℕ}

/-- A set is rainbow if it meets every block at most once. -/
def IsRainbow (blk : Fin m → Fin k) (S : Finset (Fin m)) : Prop :=
  Set.InjOn blk (S : Set (Fin m))

/-- `E_Q = ⋃_{b ∈ Q} R_b`. -/
def blockSet (blk : Fin m → Fin k) (Q : Finset (Fin k)) : Finset (Fin m) :=
  univ.filter fun e => blk e ∈ Q

/-- The blocks met by `S`. -/
def blocksMet (blk : Fin m → Fin k) (S : Finset (Fin m)) : Finset (Fin k) :=
  S.image blk

/-- `I` is a rainbow independent set of `N`. -/
def IsRainbowIndep (N : Matroid (Fin m)) (blk : Fin m → Fin k) (I : Finset (Fin m)) : Prop :=
  N.Indep (I : Set (Fin m)) ∧ IsRainbow blk I

open Classical in
/-- `ν(N)`, the largest size of a rainbow independent set of `N`. -/
noncomputable def nu (N : Matroid (Fin m)) (blk : Fin m → Fin k) : ℕ :=
  ((univ : Finset (Finset (Fin m))).filter (IsRainbowIndep N blk)).sup card

open Classical in
/-- `Av(N)`, the blocks missed by some rainbow independent set of size `ν(N)`: the avoidable
blocks. -/
noncomputable def Av (N : Matroid (Fin m)) (blk : Fin m → Fin k) : Finset (Fin k) :=
  univ.filter fun b => ∃ I : Finset (Fin m),
    IsRainbowIndep N blk I ∧ I.card = nu N blk ∧ b ∉ blocksMet blk I

/-- A rainbow base of `M`. -/
def IsRainbowBase (M : Matroid (Fin m)) (blk : Fin m → Fin k) (B : Finset (Fin m)) : Prop :=
  M.IsBase (B : Set (Fin m)) ∧ IsRainbow blk B

/-- `B` is a minimum base of `u`. -/
def IsMinBase (M : Matroid (Fin m)) (u : Fin m → ℝ) (B : Finset (Fin m)) : Prop :=
  M.IsBase (B : Set (Fin m)) ∧
    ∀ B' : Finset (Fin m), M.IsBase (B' : Set (Fin m)) → ∑ e ∈ B, u e ≤ ∑ e ∈ B', u e

/-- `β_M(u) = min_B u(B)`, the least weight of a base (`basisWeights` is the set of base
weights of Phase 1). -/
noncomputable def minBaseWeight (M : Matroid (Fin m)) (u : Fin m → ℝ) : ℝ :=
  sInf (basisWeights M u)

/-- `Opt(w)`, the least weight of a rainbow base. -/
noncomputable def Opt (M : Matroid (Fin m)) (blk : Fin m → Fin k) (w : Fin m → ℝ) : ℝ :=
  sInf {x | ∃ B : Finset (Fin m), IsRainbowBase M blk B ∧ x = ∑ e ∈ B, w e}

/-- `v = w - p_blk`, that is `v_e = w_e - p_{blk(e)}`. -/
def shift (blk : Fin m → Fin k) (w : Fin m → ℝ) (p : Fin k → ℝ) : Fin m → ℝ :=
  fun e => w e - p (blk e)

/-- The Lagrangian `Ψ(p) = Σ_b p_b + β_M(w - p_blk)`. -/
noncomputable def Psi (M : Matroid (Fin m)) (blk : Fin m → Fin k) (w : Fin m → ℝ)
    (p : Fin k → ℝ) : ℝ :=
  ∑ b, p b + minBaseWeight M (shift blk w p)

/-- The level piece `(M ↾ {u ≤ ℓ}) ／ {u < ℓ}` of `M^u`. -/
def levelPiece (M : Matroid (Fin m)) (u : Fin m → ℝ) (ℓ : ℝ) : Matroid (Fin m) :=
  (M.restrict {e | u e ≤ ℓ}).contract {e | u e < ℓ}

theorem levelPiece_ground (M : Matroid (Fin m)) (u : Fin m → ℝ) (ℓ : ℝ) :
    (levelPiece M u ℓ).E = {e | u e = ℓ} := by
  ext e
  simp only [levelPiece, Matroid.contract_ground, Matroid.restrict_ground_eq, Set.mem_sdiff,
    Set.mem_setOf_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem levelPiece_disjoint (M : Matroid (Fin m)) (u : Fin m → ℝ) :
    Pairwise (Function.onFun Disjoint fun ℓ => (levelPiece M u ℓ).E) := by
  intro ℓ ℓ' h
  simp only [Function.onFun, levelPiece_ground]
  exact Set.disjoint_left.2 fun e he he' => h ((Set.mem_setOf_eq ▸ he).symm.trans he')

/-- The matroid `M^u` whose bases are the minimum bases of `u`
(Lemma `lem:minbases`(3)). -/
noncomputable def minBases (M : Matroid (Fin m)) (u : Fin m → ℝ) : Matroid (Fin m) :=
  Matroid.disjointSigma (levelPiece M u) (levelPiece_disjoint M u)

open Classical in
/-- `θ(B) = max({0} ∪ {v_f - v_e : e ∉ B, f ∈ C(B, e)})`, the largest gain of a single
exchange, where `C(B, e)` is Mathlib's fundamental circuit `M.fundCircuit e B`. -/
noncomputable def theta (M : Matroid (Fin m)) (v : Fin m → ℝ) (B : Finset (Fin m)) : ℝ :=
  ((univ ×ˢ univ).filter fun p : Fin m × Fin m =>
      p.1 ∉ B ∧ p.2 ∈ M.fundCircuit p.1 (B : Set (Fin m))).fold max 0
    fun p => v p.2 - v p.1

/-- `P_t = {B ∈ Bases(M) : θ(B) ≤ t}`, the possibly optimal bases. -/
def Pos (M : Matroid (Fin m)) (v : Fin m → ℝ) (t : ℝ) : Set (Finset (Fin m)) :=
  {B | M.IsBase (B : Set (Fin m)) ∧ theta M v B ≤ t}

/-- `e = f`, or `e` and `f` lie on a common circuit of `M`.  Its classes are the connected
components of Lemma `lem:minbases`(4). -/
def connRel (M : Matroid (Fin m)) (e f : Fin m) : Prop :=
  e = f ∨ ∃ C : Set (Fin m), M.IsCircuit C ∧ e ∈ C ∧ f ∈ C

/-- Definition `def:admissible`: a family `N(t)`, `t ≥ 0`, of matroids on `E` with

* (F1) `N(0) = M^v`;
* (F2) every base of `N(t)` is a base of `N(t')` whenever `t ≤ t'`;
* (F3) `P_t ⊆ Bases(N(t))`;
* (F4) `N(t)` has a rainbow base for all large `t`;
* (F5) there are finitely many levels, `0` among them, such that `N` is constant on every
  interval `[t, t']` with no level in `(t, t']`, that is on each `[c_i, c_{i+1})` and on
  `[c_q, ∞)`.

The standing hypothesis `ν₀ = r < k` of the paper is carried by the theorems about the
family. -/
structure IsAdmissible (M : Matroid (Fin m)) (blk : Fin m → Fin k) (v : Fin m → ℝ)
    (N : ℝ → Matroid (Fin m)) : Prop where
  ground : ∀ t, 0 ≤ t → (N t).E = Set.univ
  F1 : N 0 = minBases M v
  F2 : ∀ t t', 0 ≤ t → t ≤ t' → ∀ B : Finset (Fin m),
    (N t).IsBase (B : Set (Fin m)) → (N t').IsBase (B : Set (Fin m))
  F3 : ∀ t, 0 ≤ t → ∀ B ∈ Pos M v t, (N t).IsBase (B : Set (Fin m))
  F4 : ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → ∃ B, IsRainbowBase (N t) blk B
  F5 : ∃ c : Finset ℝ, 0 ∈ c ∧ ∀ t t', 0 ≤ t → t ≤ t' →
    (∀ x ∈ c, ¬(t < x ∧ x ≤ t')) → N t = N t'

end SignedTropical.Rainbow
