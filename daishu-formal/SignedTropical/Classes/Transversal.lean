import SignedTropical.Rainbow.Partition
import SignedTropical.Rainbow.MICircuit
import SignedTropical.TheoremA

/-!
# Transversal matroids

`greedy_intersection.tex`, Corollary `cor:transversal`(1): transversal matroids, with explicit
Boolean rank circuits from the matroid intersection circuit of Lemma `lem:augment`
(`Rainbow/MICircuit.lean`), and signed tropical circuits for `h_M` by Theorem A.

A family `A₀, …, A_{n-1}` of subsets of `E = Fin m` is `A : Fin n → Finset (Fin m)`.

1. **The matroid.**  `IsPartialTransversal A X`: some injection `φ : X → Fin n` has
   `x ∈ A (φ x)` for every `x ∈ X`.  `transversal A` is the matroid on `Fin m` with ground set
   `univ` whose independent sets are the partial transversals (`transversal_indep`,
   `transversal_ground`).
2. **Bipartite graphs.**  `Presents A col blk`: the bipartite graph with edges `Fin p`, edge `j`
   joining the element `col j` and the set `blk j`, has an edge between `e` and `i` exactly when
   `e ∈ A i`; the incidences `e ∈ A i` form such a graph with `p = |A₀| + ⋯ + |A_{n-1}|` edges
   (`incCol`, `incBlk`, `presents_incidence`).  `edgeMatroid col S` is the matroid `N_S` on the
   edges: the partition matroid of the elements (`colMatroid` of `Rainbow/Partition.lean`)
   restricted to the edges at `S`.  With the blocks `blk⁻¹(i)`, one for each set, its rainbow
   independent sets are the matchings of parts of `S` into the family
   (`isPartialTransversal_image`, `exists_isRainbowIndep`), and `ν(N_X) = |X|` for a partial
   transversal `X` (`nu_edgeMatroid`).
3. **Augmentation** (`exists_insert`), through Lemma `lem:avoidable` (`Rainbow/Exchange.lean`):
   if `X`, `Y` are partial transversals with `|X| < |Y|` and no `X + y`, `y ∈ Y \ X`, is one,
   then every element of `Y` in a set of `Q = Av(N_X)` lies in `X`, and items (1) and (2) of the
   lemma at `Q` give `|Y| ≤ |X|`.
4. **The rank** (`rk_eq_nu`): `r(S) = ν(N_S)`.
5. **The rank circuit** (`rankCircuit`, `rankCircuit_spec`): the circuit for `ν(N_x)` of
   `Rainbow/MICircuit.lean` (`nuCircuit`, `n` rounds of the augmenting path algorithm), whose
   context is the input `x` and whose independence oracle (`indepOfRankB` of `BoolAlg/Count`,
   `oracleCost m p` gates) compares `|A|` with the rank query `r_{N_x}(A)`, the number of elements `e` with `x_e` that
   `A` meets (`rkQueryB`: one `∨` per edge, one `∧` per element and a population count,
   `p + m + popCost m` gates).  It has `n · roundCost p (oracleCost m p) + popCost p ≤
   36 (n+1)(p+1)²(p+m+1)` gates (`rankCost_le`).
6. **Theorem A** (`theoremA_rankCircuit`): `h_M` has a signed tropical circuit of size at most
   `120 (m+1)(n+1)(p+1)²(p+m+1)`.  For `p = |A₀| + ⋯ + |A_{n-1}| ≤ mn`:
   `transversal_rankCircuit` (a Boolean rank circuit of size at most `36 (m+1)³(n+1)⁴`) and
   `theoremA_transversal` (a signed tropical circuit of size at most `120 (m+1)⁴(n+1)⁴`).
-/

open Finset SignedTropical.BoolAlg SignedTropical.Rainbow SignedTropical.Rainbow.Exchange
  SignedTropical.Rainbow.MI

namespace SignedTropical.Classes.Transversal

/-! ### Partial transversals and bipartite graphs -/

section Matroid

variable {m n p : ℕ}

/-- `X` is a **partial transversal** of the family `A₀, …, A_{n-1}` of subsets of `Fin m`:
there is an injection `φ : X → Fin n` with `x ∈ A (φ x)` for every `x ∈ X`. -/
def IsPartialTransversal (A : Fin n → Finset (Fin m)) (X : Set (Fin m)) : Prop :=
  ∃ φ : X → Fin n, Function.Injective φ ∧ ∀ x : X, (x : Fin m) ∈ A (φ x)

/-- A bipartite graph with edges `Fin p`, edge `j` joining the element `col j` and the set
`blk j`, **presents** the family `A` when `e ∈ A i` exactly if some edge joins `e` and `i`. -/
def Presents (A : Fin n → Finset (Fin m)) (col : Fin p → Fin m) (blk : Fin p → Fin n) : Prop :=
  ∀ e i, e ∈ A i ↔ ∃ j, col j = e ∧ blk j = i

/-- The incidences `e ∈ A i`, as pairs `⟨i, e⟩`, numbered by `Fin (|A₀| + ⋯ + |A_{n-1}|)`. -/
noncomputable def incidence (A : Fin n → Finset (Fin m)) :
    Fin (∑ i, (A i).card) ≃ (univ.sigma A : Finset ((_ : Fin n) × Fin m)) :=
  (finCongr (card_sigma _ _).symm).trans (univ.sigma A).equivFin.symm

/-- The element of an incidence. -/
noncomputable def incCol (A : Fin n → Finset (Fin m)) (j : Fin (∑ i, (A i).card)) : Fin m :=
  (incidence A j).1.2

/-- The set of an incidence. -/
noncomputable def incBlk (A : Fin n → Finset (Fin m)) (j : Fin (∑ i, (A i).card)) : Fin n :=
  (incidence A j).1.1

/-- Every family is presented by the bipartite graph of its incidences `e ∈ A i`, with
`|A₀| + ⋯ + |A_{n-1}|` edges. -/
theorem presents_incidence (A : Fin n → Finset (Fin m)) : Presents A (incCol A) (incBlk A) := by
  refine fun e i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := (incidence A).surjective ⟨⟨i, e⟩, mem_sigma.2 ⟨mem_univ i, h⟩⟩
    exact ⟨j, by simp only [incCol, hj], by simp only [incBlk, hj]⟩
  · rintro ⟨j, rfl, rfl⟩
    exact (mem_sigma.1 (incidence A j).2).2

/-- The matroid `N_S` on the edges: a set of edges is independent when it meets every element
at most once and meets only elements of `S`.  It is the partition matroid of the elements
(`colMatroid col` of `Rainbow/Partition.lean`) restricted to the edges at `S`. -/
def edgeMatroid (col : Fin p → Fin m) (S : Finset (Fin m)) : Matroid (Fin p) :=
  (Partition.colMatroid col).restrict {j | col j ∈ S}

variable {A : Fin n → Finset (Fin m)} {col : Fin p → Fin m} {blk : Fin p → Fin n}

/-- A set of edges is independent in `N_S` when it meets every element at most once and only
elements of `S`. -/
theorem edgeMatroid_indep {S : Finset (Fin m)} {J : Set (Fin p)} :
    (edgeMatroid col S).Indep J ↔ Set.InjOn col J ∧ ∀ j ∈ J, col j ∈ S :=
  Iff.rfl

/-- The rank of a set `F` of edges in `N_S` is the number of elements of `S` that `F` meets. -/
theorem rk_edgeMatroid (col : Fin p → Fin m) (S : Finset (Fin m)) (F : Finset (Fin p)) :
    rk (edgeMatroid col S) F = #((F.filter fun j => col j ∈ S).image col) := by
  rw [← Partition.rk_eq]
  unfold rk edgeMatroid
  rw [Matroid.restrict_eRk_eq']
  congr 2
  ext j
  simp

/-- A set `J` of edges independent in `N_S` meets `|J|` elements, all in `S`. -/
theorem image_subset_card_image {S : Finset (Fin m)} {J : Finset (Fin p)}
    (hJ : (edgeMatroid col S).Indep (J : Set (Fin p))) :
    J.image col ⊆ S ∧ (J.image col).card = J.card := by
  refine ⟨fun e he => ?_, card_image_of_injOn (edgeMatroid_indep.1 hJ).1⟩
  obtain ⟨j, hj, rfl⟩ := mem_image.1 he
  exact (edgeMatroid_indep.1 hJ).2 j hj

/-- A rainbow independent set of `N_S` is one of `N_T` for `S ⊆ T`. -/
theorem isRainbowIndep_mono {S T : Finset (Fin m)} {J : Finset (Fin p)}
    (hJ : IsRainbowIndep (edgeMatroid col S) blk J) (hST : S ⊆ T) :
    IsRainbowIndep (edgeMatroid col T) blk J :=
  ⟨edgeMatroid_indep.2 ⟨(edgeMatroid_indep.1 hJ.1).1,
    fun j hj => hST ((edgeMatroid_indep.1 hJ.1).2 j hj)⟩, hJ.2⟩

/-- **A matching gives a partial transversal**: the elements met by a rainbow independent set
of `N_S` form a partial transversal. -/
theorem isPartialTransversal_image (hA : Presents A col blk) {S : Finset (Fin m)}
    {J : Finset (Fin p)} (hJ : IsRainbowIndep (edgeMatroid col S) blk J) :
    IsPartialTransversal A ((J.image col : Finset (Fin m)) : Set (Fin m)) := by
  have hmem : ∀ x : ((J.image col : Finset (Fin m)) : Set (Fin m)), ∃ j ∈ J, col j = x :=
    fun x => mem_image.1 x.2
  choose g hgJ hgc using hmem
  refine ⟨fun x => blk (g x), fun x y hxy => ?_, fun x => (hA _ _).2 ⟨g x, hgc x, rfl⟩⟩
  have h := hJ.2 (hgJ x) (hgJ y) hxy
  exact Subtype.ext ((hgc x).symm.trans ((congrArg col h).trans (hgc y)))

/-- **A partial transversal gives a matching**: a partial transversal `X` is the set of
elements met by a rainbow independent set of `N_X`. -/
theorem exists_isRainbowIndep (hA : Presents A col blk) {X : Finset (Fin m)}
    (hX : IsPartialTransversal A (X : Set (Fin m))) :
    ∃ J : Finset (Fin p), IsRainbowIndep (edgeMatroid col X) blk J ∧ J.image col = X := by
  classical
  obtain ⟨φ, hφ, hmem⟩ := hX
  have hex : ∀ x : (X : Set (Fin m)), ∃ j, col j = x ∧ blk j = φ x :=
    fun x => (hA _ _).1 (hmem x)
  choose g hgc hgb using hex
  refine ⟨univ.image g, ⟨edgeMatroid_indep.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ hj _ hj' h
    obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hj)
    obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hj')
    rw [hgc, hgc] at h
    rw [Subtype.ext h]
  · rintro _ hj
    obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hj)
    rw [hgc]
    exact x.2
  · rintro _ hj _ hj' h
    obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hj)
    obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hj')
    rw [hgb, hgb] at h
    rw [hφ h]
  · ext e
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [hgc]
      exact x.2
    · exact fun he => ⟨g ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, hgc _⟩

/-- **`ν(N_X) = |X|` for a partial transversal `X`.** -/
theorem nu_edgeMatroid (hA : Presents A col blk) {X : Finset (Fin m)}
    (hX : IsPartialTransversal A (X : Set (Fin m))) : nu (edgeMatroid col X) blk = X.card := by
  obtain ⟨J, hJ, hJX⟩ := exists_isRainbowIndep hA hX
  obtain ⟨J', hJ', hJ'n⟩ := exists_isRainbowIndep_card_eq_nu (edgeMatroid col X) blk
  have h1 := hJ.card_le_nu
  obtain ⟨h2, h3⟩ := image_subset_card_image hJ'.1
  have h4 := (image_subset_card_image hJ.1).2
  rw [hJX] at h4
  have := card_le_card h2
  omega

/-- **Augmentation of partial transversals**, through Lemma `lem:avoidable`.  Let `X`, `Y` be
partial transversals with `|X| < |Y|`.  Then `X + y` is a partial transversal for some
`y ∈ Y \ X`. -/
theorem exists_insert (hA : Presents A col blk) {X Y : Finset (Fin m)}
    (hX : IsPartialTransversal A (X : Set (Fin m))) (hY : IsPartialTransversal A (Y : Set (Fin m)))
    (hXY : X.card < Y.card) :
    ∃ y ∈ Y, y ∉ X ∧ IsPartialTransversal A ((insert y X : Finset (Fin m)) : Set (Fin m)) := by
  classical
  by_contra hcon
  push Not at hcon
  set Q := Av (edgeMatroid col X) blk
  -- an element of `Y` that lies in a set of `Q` lies in `X`
  have key : ∀ j, blk j ∈ Q → col j ∈ Y → col j ∈ X := by
    intro j hjQ hjY
    by_contra hjX
    obtain ⟨J, hJ, hJc, hjJ⟩ := mem_Av.1 hjQ
    rw [nu_edgeMatroid hA hX] at hJc
    obtain ⟨hsub, hcard⟩ := image_subset_card_image hJ.1
    have himage : J.image col = X := eq_of_subset_of_card_le hsub (by rw [hcard, hJc])
    have hjJ' : j ∉ J := fun h => hjJ (mem_image_of_mem blk h)
    have hind := edgeMatroid_indep.1 hJ.1
    refine hcon (col j) hjY hjX ?_
    rw [← himage, ← image_insert]
    refine isPartialTransversal_image hA (S := insert (col j) X)
      ⟨edgeMatroid_indep.2 ⟨?_, fun i hi => ?_⟩, ?_⟩
    · rw [coe_insert, Set.injOn_insert (by simpa using hjJ')]
      refine ⟨hind.1, fun ⟨i, hi, hij⟩ => hjX ?_⟩
      rw [← hij]
      exact hind.2 i hi
    · rcases mem_insert.1 (mem_coe.1 hi) with rfl | hi
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hind.2 i hi)
    · rw [IsRainbow, coe_insert, Set.injOn_insert (by simpa using hjJ')]
      exact ⟨hJ.2, fun ⟨i, hi, hij⟩ => hjJ (hij ▸ mem_image_of_mem blk hi)⟩
  have h1 : Q.card + nu (edgeMatroid col X) blk = n + rk (edgeMatroid col X) (blockSet blk Q) :=
    card_av_add_nu _ _
  have h2 := card_add_nu_le (edgeMatroid col Y) blk Q
  rw [nu_edgeMatroid hA hX, rk_edgeMatroid] at h1
  rw [nu_edgeMatroid hA hY, rk_edgeMatroid] at h2
  have h3 : ((blockSet blk Q).filter fun j => col j ∈ Y).image col ⊆
      ((blockSet blk Q).filter fun j => col j ∈ X).image col := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := mem_image.1 he
    rw [mem_filter, blockSet, mem_filter] at hj
    exact mem_image_of_mem col
      (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hj.1.2⟩, key j hj.1.2 hj.2⟩)
  have := card_le_card h3
  omega

/-- The empty set is a partial transversal. -/
theorem isPartialTransversal_empty (A : Fin n → Finset (Fin m)) : IsPartialTransversal A ∅ :=
  ⟨fun x => (Set.notMem_empty _ x.2).elim, fun x => (Set.notMem_empty _ x.2).elim,
    fun x => (Set.notMem_empty _ x.2).elim⟩

/-- A subset of a partial transversal is a partial transversal. -/
theorem IsPartialTransversal.subset {X Y : Set (Fin m)} (hY : IsPartialTransversal A Y)
    (hXY : X ⊆ Y) : IsPartialTransversal A X :=
  let ⟨φ, hφ, hmem⟩ := hY
  ⟨φ ∘ Set.inclusion hXY, hφ.comp (Set.inclusion_injective hXY), fun _ => hmem _⟩

/-- **The transversal matroid** of the family `A₀, …, A_{n-1}` of subsets of `Fin m`, with
ground set `Fin m`: its independent sets are the partial transversals (`transversal_indep`).
Augmentation is `exists_insert`, for the bipartite graph of the incidences. -/
def transversal (A : Fin n → Finset (Fin m)) : Matroid (Fin m) :=
  (IndepMatroid.ofFinite Set.finite_univ (IsPartialTransversal A) (isPartialTransversal_empty A)
    (fun _ _ hJ hIJ => hJ.subset hIJ)
    (fun I J hI hJ hIJ => by
      obtain ⟨X, rfl⟩ := exists_finset I
      obtain ⟨Y, rfl⟩ := exists_finset J
      rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at hIJ
      obtain ⟨y, hy, hyX, h⟩ := exists_insert (presents_incidence A) hI hJ hIJ
      exact ⟨y, hy, hyX, by rwa [← coe_insert]⟩)
    fun _ _ => Set.subset_univ _).matroid

@[simp] theorem transversal_ground : (transversal A).E = Set.univ := rfl

@[simp] theorem transversal_indep {X : Set (Fin m)} :
    (transversal A).Indep X ↔ IsPartialTransversal A X :=
  Iff.rfl

/-- **The rank of a transversal matroid is `ν`**: for a bipartite graph presenting `A`, the rank
of `S` is `ν(N_S)`, the largest size of a set of edges that meets every element at most once,
only elements of `S`, and every set at most once (a matching of a part of `S` into the
family). -/
theorem rk_eq_nu (hA : Presents A col blk) (S : Finset (Fin m)) :
    rk (transversal A) S = nu (edgeMatroid col S) blk := by
  apply le_antisymm
  · obtain ⟨I₀, hI₀⟩ := (transversal A).exists_isBasis (S : Set (Fin m)) (Set.subset_univ _)
    obtain ⟨I, rfl⟩ := exists_finset I₀
    rw [← card_eq_rk _ hI₀]
    obtain ⟨J, hJ, hJI⟩ := exists_isRainbowIndep hA hI₀.indep
    rw [← hJI, (image_subset_card_image hJ.1).2]
    exact (isRainbowIndep_mono hJ (coe_subset.1 hI₀.subset)).card_le_nu
  · obtain ⟨J, hJ, hJn⟩ := exists_isRainbowIndep_card_eq_nu (edgeMatroid col S) blk
    obtain ⟨hsub, hcard⟩ := image_subset_card_image hJ.1
    rw [← hJn, ← hcard]
    exact card_le_rk _ (isPartialTransversal_image hA hJ) hsub

end Matroid

/-! ### The independence oracle of `N_x` -/

section Gadgets

variable {q m p : ℕ}

/-- The edges at the element `e`, in increasing order. -/
def edgesAt (col : Fin p → Fin m) (e : Fin m) : List (Fin p) :=
  (List.finRange p).filter fun j => col j = e

/-- `j` is an edge at `e` when `col j = e`. -/
theorem mem_edgesAt {col : Fin p → Fin m} {e : Fin m} {j : Fin p} :
    j ∈ edgesAt col e ↔ col j = e := by
  simp [edgesAt]

/-- Every edge lies at one element: `Σ_e |edgesAt e| = p`. -/
theorem sum_length_edgesAt (col : Fin p → Fin m) : ∑ e, (edgesAt col e).length = p := by
  have h : ∀ e, (edgesAt col e).length = (univ.filter fun j => col j = e).card := fun e => by
    rw [edgesAt, ← List.toFinset_card_of_nodup ((List.nodup_finRange p).filter _)]
    congr 1
    ext j
    simp
  simp only [h]
  rw [← card_eq_sum_card_fiberwise fun j _ => mem_univ (col j)]
  simp

/-- The left fold of `∨` over a list: `b ∨ (V j for some j in the list)`. -/
theorem foldl_or (l : List (Fin p)) (V : Fin p → Bool) (b : Bool) :
    l.foldl (fun s j => s || V j) b = (b || decide (∃ j ∈ l, V j = true)) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    cases b <;> cases h : V a <;> simp [h]

/-- `acc ∨ A j₁ ∨ ⋯ ∨ A j_r` for a list `[j₁, …, j_r]` of edges, from `(A, acc)`. -/
def anyListB (l : List (Fin p)) : (Fin p → Arg q) × Arg q → Bld BoolOp q (Arg q) :=
  foldCtxB (fun j s => emit .or s.2 (s.1 j)) l

/-- `acc ∨ A j₁ ∨ ⋯ ∨ A j_r`: one gate per entry of the list. -/
theorem anyListB_impl (l : List (Fin p)) :
    Impl ((vecR p).prod bitR) (bitR (n := q)) (anyListB l) l.length
      (fun t => t.2 || decide (∃ j ∈ l, t.1 j = true)) :=
  ((Impl.foldCtx
    (b := fun (j : Fin p) (s : (Fin p → Arg q) × Arg q) => emit BoolOp.or s.2 (s.1 j))
    (F := fun j V a => a || V j) (l := l)
    fun j _ => emitOr_impl.pre (R := (vecR p).prod bitR) (g := fun s => (s.2, s.1 j))
      (G := fun t => (t.2, t.1 j)) fun _ _ _ hs => ⟨hs.2, hs.1 j⟩).cost (mul_one _)).congr
    fun t => foldl_or l t.1 t.2

/-- The bit of the element `e`, from `(x, A)`: `x e ∧ (A j for some edge j at e)`. -/
def elemB (col : Fin p → Fin m) (e : Fin m) :
    (Fin m → Arg q) × (Fin p → Arg q) → Bld BoolOp q (Arg q) :=
  seqB (pairB (pureB fun s => s.1 e) fun s => anyListB (edgesAt col e) (s.2, .const))
    fun r => emit .and r.1 r.2

/-- The bit of the element `e`: `|edgesAt e| + 1` gates. -/
theorem elemB_impl (col : Fin p → Fin m) (e : Fin m) :
    Impl ((vecR m).prod (vecR p)) (bitR (n := q)) (elemB col e) ((edgesAt col e).length + 1)
      (fun t => t.1 e && decide (∃ j, col j = e ∧ t.2 j = true)) := by
  have h := ((Impl.free (n := q) (R₁ := (vecR m).prod (vecR p)) (R₂ := bitR) (g := fun s => s.1 e)
    (F := fun t => t.1 e) fun _ _ _ hs => hs.1 e).pair
    ((anyListB_impl (edgesAt col e)).pre (R := (vecR m).prod (vecR p))
      (g := fun s => (s.2, .const)) (G := fun t => (t.2, false))
      fun gs _ _ hs => ⟨hs.2, den_const gs⟩)).comp emitAnd_impl
  refine (h.cost (by rw [Nat.zero_add])).congr fun t => ?_
  simp [mem_edgesAt]

/-- The rank query of `N_x` at a set `A` of edges: the number of elements `e` with `x e` that
`A` meets. -/
def rkQueryV (col : Fin p → Fin m) (t : (Fin m → Bool) × (Fin p → Bool)) : ℕ :=
  (univ.filter fun e => (t.1 e && decide (∃ j, col j = e ∧ t.2 j = true)) = true).card

/-- The rank query, from `(x, A)`: the bits of the elements, then their population count. -/
def rkQueryB (col : Fin p → Fin m) :
    (Fin m → Arg q) × (Fin p → Arg q) → Bld BoolOp q (List (Arg q)) :=
  seqB (fun s => tabB fun e => elemB col e s) vecPopcountB

/-- **The rank query**, `p + m + popCost m` gates: one `∨` per edge, one `∧` per element, and a
population count of the `m` bits of the elements. -/
theorem rkQueryB_impl (col : Fin p → Fin m) :
    Impl ((vecR m).prod (vecR p)) (numR (n := q) (Nat.size m)) (rkQueryB col)
      (p + m + popCost m) (rkQueryV col) := by
  refine ((Impl.tabSum fun e => elemB_impl col e).comp vecPopcountB_impl).cost ?_
  rw [sum_add_distrib, sum_length_edgesAt]
  simp

/-- **The rank query is the rank of `N_S`**: at the input `1_S` and a set `F` of edges, the
query is `r_{N_S}(F)`. -/
theorem rkQueryV_eq (col : Fin p → Fin m) (S : Finset (Fin m)) (F : Finset (Fin p)) :
    rkQueryV col (indicator S, indicator F) = rk (edgeMatroid col S) F := by
  rw [rk_edgeMatroid, rkQueryV]
  congr 1
  ext e
  simp only [indicator, mem_filter, mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
    mem_image]
  constructor
  · rintro ⟨he, j, rfl, hj⟩
    exact ⟨j, ⟨hj, he⟩, rfl⟩
  · rintro ⟨j, ⟨hj, he⟩, rfl⟩
    exact ⟨he, j, rfl, hj⟩

/-- The gates of the independence oracle `indepOfRankB (rkQueryB col)` of `N_x` (the rank query
compared with `|A|`, `BoolAlg/Count.lean`): `p + m + popCost m + popCost p + 5⌈log₂(p+1)⌉ + 1`. -/
def oracleCost (m p : ℕ) : ℕ := p + m + popCost m + popCost p + (5 * Nat.size p + 1)

end Gadgets

/-! ### The rank circuit and Theorem A -/

section Circuit

variable {m n p : ℕ} {A : Fin n → Finset (Fin m)} {col : Fin p → Fin m} {blk : Fin p → Fin n}

/-- **The rank circuit of a transversal matroid** presented by the bipartite graph `(col, blk)`:
the circuit for `ν(N_x)` of `Rainbow/MICircuit.lean` (`n` rounds of the augmenting path
algorithm on `N_x` with the blocks `blk⁻¹(i)`, one for each set of the family, then a population
count), whose context is the input `x` and whose independence oracle compares the rank query
`rkQueryB col` with `|A|` (`indepOfRankB`). -/
def rankCircuit (col : Fin p → Fin m) (blk : Fin p → Fin n) : Circuit BoolOp m :=
  nuCircuit (fun _ => indepOfRankB (rkQueryB col)) blk

/-- **The rank circuit** has `n · roundCost p (oracleCost m p) + popCost p` gates and outputs in
binary, for every `S ⊆ E`, the rank of `S` in the transversal matroid. -/
theorem rankCircuit_spec (hA : Presents A col blk) :
    (rankCircuit col blk).size = n * roundCost p (oracleCost m p) + popCost p ∧
      ∀ S : Finset (Fin m),
        bitsVal ((rankCircuit col blk).eval boolInterp (indicator S)) = rk (transversal A) S := by
  obtain ⟨hs, -, he⟩ :=
    nuCircuit_spec (fun _ => indepOfRankB_impl (rkQueryB_impl (q := m) col)) blk
  refine ⟨hs, fun S => ?_⟩
  exact (he (indicator S) (edgeMatroid col S)
    (ExchOracle.of_indep (indepOfRank_correct fun F => rkQueryV_eq col S F))).trans
    (rk_eq_nu hA S).symm

/-- The rank circuit satisfies the hypothesis of Theorem A. -/
theorem rankCircuit_eRk (hA : Presents A col blk) (S : Finset (Fin m)) :
    (bitsVal ((rankCircuit col blk).eval boolInterp (indicator S)) : ℕ∞) =
      (transversal A).eRk (S : Set (Fin m)) := by
  rw [(rankCircuit_spec hA).2 S, coe_rk]

/-- The rank circuit has at most `36 (n+1) (p+1)² (p+m+1)` gates. -/
theorem rankCost_le (m n p : ℕ) :
    n * roundCost p (oracleCost m p) + popCost p ≤ 36 * (n + 1) * (p + 1) ^ 2 * (p + m + 1) := by
  have h1 : oracleCost m p ≤ 28 * p + 23 * m + 1 := by
    have := popCost_le m
    have := popCost_le p
    have := size_le_self p
    unfold oracleCost
    omega
  have h2 : roundCost p (oracleCost m p) ≤
      36 * p ^ 3 + 23 * m * p ^ 2 + 13 * p ^ 2 + 12 * p + 4 := by
    have := Nat.mul_le_mul_left (p ^ 2) h1
    unfold roundCost
    nlinarith
  have h3 := popCost_le p
  have h4 := Nat.mul_le_mul_left n h2
  have h5 : 36 * (n + 1) * (p + 1) ^ 2 * (p + m + 1) =
      n * (36 * p ^ 3 + 23 * m * p ^ 2 + 13 * p ^ 2 + 12 * p + 4) + 22 * p +
        (n * (13 * m * p ^ 2 + 95 * p ^ 2 + 72 * m * p + 96 * p + 36 * m + 32) + 36 * p ^ 3 +
          36 * m * p ^ 2 + 108 * p ^ 2 + 72 * m * p + 86 * p + 36 * m + 36) := by ring
  rw [h5]
  exact (Nat.add_le_add h4 h3).trans (Nat.le_add_right _ _)

/-- The size of Theorem A for the rank circuit:
`3 m s + m L + 9 m² + 4 m + 4 L + 1 ≤ 120 (m+1)(n+1)(p+1)²(p+m+1)` when `L ≤ m`. -/
theorem theoremA_cost_le {L : ℕ} (hL : L ≤ m) :
    3 * m * (n * roundCost p (oracleCost m p) + popCost p) + m * L + 9 * m ^ 2 + 4 * m + 4 * L
      + 1 ≤ 120 * (m + 1) * (n + 1) * (p + 1) ^ 2 * (p + m + 1) := by
  obtain ⟨T, hT⟩ : ∃ T, (n + 1) * (p + 1) ^ 2 * (p + m + 1) = T := ⟨_, rfl⟩
  have hs := rankCost_le m n p
  have hmT : m + 1 ≤ T := hT ▸ (Nat.le_add_left _ _).trans
    (Nat.le_mul_of_pos_left _ (by positivity))
  rw [show 36 * (n + 1) * (p + 1) ^ 2 * (p + m + 1) = 36 * T by rw [← hT]; ring] at hs
  rw [show 120 * (m + 1) * (n + 1) * (p + 1) ^ 2 * (p + m + 1) = 120 * (m + 1) * T by
    rw [← hT]; ring]
  have h1 := Nat.mul_le_mul_left (3 * m) hs
  have h2 := Nat.mul_le_mul_left m hL
  have h3 := Nat.mul_le_mul_left m hmT
  nlinarith

/-- **Theorem A for transversal matroids**, for a family presented by a bipartite graph with `p`
edges: `h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^m` by a signed tropical circuit of size
at most `3 m s + m L + 9 m² + 4 m + 4 L + 1 ≤ 120 (m+1)(n+1)(p+1)²(p+m+1)`, where
`s = n · roundCost p (oracleCost m p) + popCost p` is the size of `rankCircuit col blk` and
`L = ⌈log₂(k+1)⌉` for the rank `k` of `M`. -/
theorem theoremA_rankCircuit (hA : Presents A col blk) :
    ∃ C : Circuit STOp m,
      C.size ≤ 3 * m * (n * roundCost p (oracleCost m p) + popCost p)
          + m * Nat.size (rank (transversal A)) + 9 * m ^ 2 + 4 * m
          + 4 * Nat.size (rank (transversal A)) + 1 ∧
        C.size ≤ 120 * (m + 1) * (n + 1) * (p + 1) ^ 2 * (p + m + 1) ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (transversal A) w] := by
  obtain ⟨C, hC, heval⟩ := theoremA (transversal A) transversal_ground (rankCircuit col blk)
    (rankCircuit_eRk hA)
  rw [(rankCircuit_spec hA).1] at hC
  exact ⟨C, hC, hC.trans (theoremA_cost_le ((size_le_self _).trans (rank_le_card _))), heval⟩

/-- The number of incidences is at most `n m`, so `p + m + 1 ≤ (m+1)(n+1)` for
`p = |A₀| + ⋯ + |A_{n-1}|`. -/
theorem sum_card_add_le (A : Fin n → Finset (Fin m)) :
    ∑ i, (A i).card + m + 1 ≤ (m + 1) * (n + 1) := by
  have h : ∑ i, (A i).card ≤ n * m := by
    calc ∑ i, (A i).card ≤ ∑ _i : Fin n, m :=
          sum_le_sum fun i _ => (card_le_univ (A i)).trans_eq (Fintype.card_fin m)
      _ = n * m := by simp
  nlinarith

/-- **Corollary `cor:transversal`(1), transversal matroids, Boolean rank circuits.**  Let
`A₀, …, A_{n-1}` be subsets of `E = Fin m` with `p = |A₀| + ⋯ + |A_{n-1}|` incidences, and `M` the
transversal matroid.  A Boolean circuit of size exactly `n · roundCost p (oracleCost m p) +
popCost p`, which is at most `36 (n+1)(p+1)²(p+m+1) ≤ 36 (m+1)³(n+1)⁴`, outputs `r(S)` in binary
for every `S ⊆ E`. -/
theorem transversal_rankCircuit (A : Fin n → Finset (Fin m)) {p : ℕ}
    (hp : ∑ i, (A i).card = p) :
    ∃ B : Circuit BoolOp m,
      B.size = n * roundCost p (oracleCost m p) + popCost p ∧
        B.size ≤ 36 * (n + 1) * (p + 1) ^ 2 * (p + m + 1) ∧
        B.size ≤ 36 * (m + 1) ^ 3 * (n + 1) ^ 4 ∧
        ∀ S : Finset (Fin m), (bitsVal (B.eval boolInterp (indicator S)) : ℕ∞) =
          (transversal A).eRk (S : Set (Fin m)) := by
  subst hp
  have hA := presents_incidence A
  have hs := (rankCircuit_spec hA).1
  have hle := rankCost_le m n (∑ i, (A i).card)
  have h1 := sum_card_add_le A
  refine ⟨rankCircuit (incCol A) (incBlk A), hs, hs.trans_le hle, hs.trans_le (hle.trans ?_),
    rankCircuit_eRk hA⟩
  calc 36 * (n + 1) * (∑ i, (A i).card + 1) ^ 2 * (∑ i, (A i).card + m + 1)
      ≤ 36 * (n + 1) * ((m + 1) * (n + 1)) ^ 2 * ((m + 1) * (n + 1)) := by
        gcongr
        exact le_trans (by omega) h1
    _ = 36 * (m + 1) ^ 3 * (n + 1) ^ 4 := by ring

/-- **Corollary `cor:transversal`(1), transversal matroids, signed tropical circuits.**  Let
`A₀, …, A_{n-1}` be subsets of `E = Fin m` with `p = |A₀| + ⋯ + |A_{n-1}|` incidences, and `M` the
transversal matroid.  Then `h_M(w) = max_B w(B)` is computed at every `w ∈ ℝ^m` by a signed
tropical circuit of size at most `120 (m+1)(n+1)(p+1)²(p+m+1) ≤ 120 (m+1)⁴(n+1)⁴`. -/
theorem theoremA_transversal (A : Fin n → Finset (Fin m)) {p : ℕ}
    (hp : ∑ i, (A i).card = p) :
    ∃ C : Circuit STOp m,
      C.size ≤ 120 * (m + 1) * (n + 1) * (p + 1) ^ 2 * (p + m + 1) ∧
        C.size ≤ 120 * (m + 1) ^ 4 * (n + 1) ^ 4 ∧
        ∀ w : Fin m → ℝ, C.eval (stInterp ℝ) w = [maxBasisWeight (transversal A) w] := by
  subst hp
  obtain ⟨C, -, hC, heval⟩ := theoremA_rankCircuit (presents_incidence A)
  have h1 := sum_card_add_le A
  refine ⟨C, hC, hC.trans ?_, heval⟩
  calc 120 * (m + 1) * (n + 1) * (∑ i, (A i).card + 1) ^ 2 * (∑ i, (A i).card + m + 1)
      ≤ 120 * (m + 1) * (n + 1) * ((m + 1) * (n + 1)) ^ 2 * ((m + 1) * (n + 1)) := by
        gcongr
        exact le_trans (by omega) h1
    _ = 120 * (m + 1) ^ 4 * (n + 1) ^ 4 := by ring

end Circuit

end SignedTropical.Classes.Transversal
