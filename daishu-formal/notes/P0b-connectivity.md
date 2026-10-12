# P0b: connected components (Lemma `lem:minbases`(4))

Natural-language companion of `SignedTropical/Rainbow/Connectivity.lean`, namespace
`SignedTropical.Rainbow.Conn`.  Source: `daishu/paper/greedy_intersection.tex`, Lemma
`lem:minbases`(4):

> The ground set splits into connected components; two non-loops lie on a common circuit
> exactly when they lie in one component, and closure and minimum bases decompose over
> components.

Build status: `lake build SignedTropical.Rainbow.Connectivity` succeeds with no error and no
warning.  No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`
or `opaque`.  Every theorem below depends only on `propext`, `Classical.choice` and
`Quot.sound` (checked with `#print axioms`).

Notation.  `E = {0, ..., m-1}` (Lean `Fin m`) and `M` is a matroid on `E` (Mathlib
`Matroid (Fin m)`).  "`M.E = E`" is the hypothesis `M.E = Set.univ`; it is stated only where
the ground set matters.  For `u ∈ ℝ^E` and `S ⊆ E`, `u(S) = Σ_{e ∈ S} u_e`.  From
`Rainbow/Defs.lean`:

* `connRel M e f`: `e = f`, or some circuit of `M` contains `e` and `f`;
* `IsMinBase M u B`: `B` is a base of `M` and `u(B) ≤ u(B')` for every base `B'` of `M`;
* `minBases M u`: the matroid `M^u`, the direct sum of the level pieces
  `(M ↾ {u ≤ ℓ}) / {u < ℓ}`;
* `rk M S`: the rank `r(S)` as a natural number (Phase 1).

`C(B, e)` is Mathlib's `M.fundCircuit e B`: for a base `B` and `e ∈ M.E \ B` it is the unique
circuit in `B + e`, and it is `{e}` when `e ∈ B` or `e ∉ M.E`.  `C*(B, f)` is Mathlib's
fundamental cocircuit `M.fundCocircuit f B`.  `M ↾ K` is the restriction of `M` to `K`.


## 1. Results

### 1.1 The equivalence relation

**Lemma 1 (circuits through two elements).**  `exists_isCircuit_of_inter_nonempty`.
Let `C₁` and `C₂` be circuits with `x ∈ C₁`, `z ∈ C₂` and `C₁ ∩ C₂ ≠ ∅`.  Then some circuit
contains both `x` and `z`.

*Proof.*  Strong induction on `|C₂ \ C₁|`, for all circuits `C₂` that contain `z` and meet
`C₁`.

Step 1, the trivial cases.  If `x ∈ C₂`, take `C₂`; if `z ∈ C₁`, take `C₁`.  Otherwise pick
`y ∈ C₁ ∩ C₂`.

Step 2, the first elimination.  Strong circuit elimination of `y` from `C₁` and `C₂`, keeping
`x ∈ C₁ \ C₂` (Mathlib's `IsCircuit.strong_elimination`), gives a circuit `C₃` with
`x ∈ C₃ ⊆ (C₁ ∪ C₂) \ {y}`.  If `z ∈ C₃`, take `C₃`.

Step 3, `C₃` meets `C₂ \ C₁`.  Otherwise `C₃ ⊆ C₁` and `y ∈ C₁ \ C₃`, so `C₃` would be a
proper subset of the circuit `C₁`.  Pick `w ∈ C₃ ∩ (C₂ \ C₁)`.

Step 4, the second elimination.  Eliminating `w` from `C₂` and `C₃`, keeping `z ∈ C₂ \ C₃`,
gives a circuit `C₄` with `z ∈ C₄ ⊆ (C₂ ∪ C₃) \ {w}`.  Since `C₃ ⊆ C₁ ∪ C₂`,
`C₄ \ C₁ ⊆ (C₂ \ C₁) \ {w}`, a proper subset of `C₂ \ C₁`, so `|C₄ \ C₁| < |C₂ \ C₁|`.

Step 5, `C₄` meets `C₁`.  Otherwise `C₄ = C₄ \ C₁ ⊆ (C₂ \ C₁) \ {w}`, a proper subset of the
circuit `C₂`.  The induction hypothesis applied to `C₄` gives the circuit.

**Proposition 2.**  `connRel_refl`, `connRel_symm`, `connRel_trans`, `connRel_equivalence`.
`connRel M` is an equivalence relation on `E`.

*Proof.*  Step 1, reflexivity and symmetry hold by definition.  Step 2, transitivity: let
`connRel M e f` and `connRel M f g`.  If `e = f` or `f = g` there is nothing to prove.
Otherwise there are circuits `C₁ ∋ e, f` and `C₂ ∋ f, g`; they meet in `f`, and Lemma 1 with
`x = e`, `z = g` gives a circuit through `e` and `g`.

### 1.2 Components

**Definition 3.**  `comp M e = {f ∈ E : connRel M e f}`, the component of `e` (a `Finset`);
`components M = {comp M e : e ∈ E}` (a `Finset` of `Finset`s).  Basic facts: `mem_comp`
(`f ∈ comp M e` iff `connRel M e f`), `mem_comp_self` (`e ∈ comp M e`), `comp_eq_comp_iff`
(`comp M e = comp M f` iff `connRel M e f`), `comp_mem_components`, `mem_components`
(`K` is a component iff `K = comp M e` for some `e`), `comp_eq_of_mem_components` (if `K` is a
component and `e ∈ K`, then `comp M e = K`).

*Proof of `comp_eq_comp_iff`.*  Step 1, if `comp M e = comp M f` then
`f ∈ comp M f = comp M e`, so `connRel M e f`.  Step 2, if `connRel M e f` then, by symmetry
and transitivity, `connRel M e g` iff `connRel M f g` for every `g`.

**Proposition 4 (the components split `E`).**  `existsUnique_mem_components`: every `e ∈ E`
lies in exactly one component.  `disjoint_of_mem_components`: two distinct components are
disjoint.

*Proof.*  Step 1, `e ∈ comp M e`.  Step 2, if `e` lies in a component `K = comp M f`, then
`connRel M f e`, and `comp_eq_comp_iff` gives `comp M e = K`.  Step 3, an element of
`K ∩ K'` gives `K = comp M e = K'` by Step 2.

**Proposition 5 (loops and coloops).**  `comp_eq_singleton_of_isLoop`,
`comp_eq_singleton_of_isColoop`.  If `e` is a loop, or a coloop, then `comp M e = {e}`.

*Proof.*  Step 1, a loop: `{e}` is a circuit, and a circuit `C ∋ e` contains the circuit
`{e}`, so `C = {e}`; hence `connRel M e f` forces `f = e`.  Step 2, a coloop lies on no
circuit (Mathlib's `IsColoop.notMem_isCircuit`), so again `connRel M e f` forces `f = e`.

**Theorem 6 (common circuits).**  `exists_isCircuit_iff_comp_eq`.  For distinct `e, f ∈ E`,
some circuit contains `e` and `f` if and only if `comp M e = comp M f`.

*Proof.*  By `comp_eq_comp_iff` the right side is `connRel M e f`, which for `e ≠ f` is the
existence of the circuit.

### 1.3 Circuits, closure and rank

**Proposition 7 (circuits lie in one component).**  `isCircuit_subset_comp`: if `C` is a
circuit and `e ∈ C`, then `C ⊆ comp M e`.  `fundCircuit_subset_comp`: if `B` is a base, then
`C(B, e) ⊆ comp M e` for every `e`.

*Proof.*  Step 1, every `f ∈ C` lies with `e` on the circuit `C`.  Step 2, if `e ∈ B` or
`e ∉ M.E`, then `C(B, e) = {e}`.  Otherwise `C(B, e)` is a circuit containing `e` (Mathlib's
`IsBase.fundCircuit_isCircuit`) and Step 1 applies.

**Theorem 8 (closure).**  `mem_closure_iff_comp`: for every `X ⊆ E` and `e ∈ E`,
`e ∈ cl(X)` if and only if `e ∈ cl(X ∩ comp M e)`.  `closure_eq_biUnion_comp`:
`cl(X) = ⋃_K cl(X ∩ K)`, the union over the components `K`.

*Proof.*  Step 1, `cl(X ∩ comp M e) ⊆ cl(X)` by monotonicity.  Step 2, let `e ∈ cl(X)` and
`e ∈ X`.  Then `e ∈ X ∩ comp M e`, and `e ∈ M.E` because closures lie in the ground set, so
`e ∈ cl(X ∩ comp M e)`.  Step 3, let `e ∈ cl(X)` and `e ∉ X`.  There is a circuit `C` with
`e ∈ C ⊆ X + e` (Mathlib's `exists_isCircuit_of_mem_closure`).  By Proposition 7,
`C ⊆ comp M e`, so `C ⊆ (X ∩ comp M e) + e`, and this circuit puts `e` in
`cl(X ∩ comp M e)` (Mathlib's `mem_closure_iff_exists_isCircuit`).  Step 4, the identity:
`e ∈ cl(X)` gives `e ∈ cl(X ∩ comp M e)` with `comp M e` a component, and each
`cl(X ∩ K)` lies in `cl(X)` by Step 1.

**Theorem 9 (rank).**  `isBasis_inter_comp`: if `I` is a basis of `X` and `K` is a component,
then `I ∩ K` is a basis of `X ∩ K`.  `sum_eq_sum_comp`: for every `S ⊆ E` and every
`f : E → β` with values in a commutative additive monoid,
`Σ_{e ∈ S} f(e) = Σ_K Σ_{e ∈ S ∩ K} f(e)`.  `rk_eq_sum_comp`: if `M.E = E`, then
`r(X) = Σ_K r(X ∩ K)` for every `X ⊆ E`.

*Proof.*  Step 1, the basis.  `I ∩ K` is independent and contained in `X ∩ K`.  Every
`e ∈ X ∩ K` lies in `cl(I)`, hence by Theorem 8 in `cl(I ∩ comp M e) = cl(I ∩ K)`.  An
independent subset of `X ∩ K` whose closure contains `X ∩ K` is a basis of it.  Step 2, the
sum.  Group the elements of `S` by their component (Mathlib's `sum_fiberwise_of_maps_to` along
`e ↦ comp M e`); the fibre over a component `K` is `S ∩ K` by `comp_eq_of_mem_components`.
Step 3, the rank.  Take a basis `I` of `X`.  Then `r(X) = |I| = Σ_K |I ∩ K| = Σ_K r(X ∩ K)`,
by Step 2 with `f = 1` and Step 1.

### 1.4 Direct sum and bases

**Theorem 10 (direct sum).**  `eq_disjointSigma`, with `pairwise_disjoint_components`.  If
`M.E = E`, then `M` is the direct sum of the restrictions `M ↾ K` over the components `K`
(Mathlib's `Matroid.disjointSigma`, indexed by the subtype of components; the ground sets
`K` are pairwise disjoint by Proposition 4).

*Proof.*  Step 1, the ground sets: the union of the components is `E = M.E`.  Step 2,
independence.  `I` is independent in the sum if and only if every `I ∩ K` is independent in
`M` (the condition `I ⊆ ⋃ K` holds always).  If `I` is independent in `M`, so are its
subsets.  Conversely, if `I` were dependent it would contain a circuit `C`; for `e ∈ C`,
Proposition 7 gives `C ⊆ I ∩ comp M e`, an independent set, which is impossible.

**Corollary 11 (bases).**  `isBase_iff_comp`.  If `M.E = E`, then `B ⊆ E` is a base of `M` if
and only if `B ∩ K` is a base of `M ↾ K` for every component `K`.

*Proof.*  Theorem 10 and Mathlib's description of the bases of a `disjointSigma`
(`disjointSigma_isBase_iff`); the condition `B ⊆ ⋃ K` holds always.

### 1.5 Minimum bases

**Theorem 12 (minimum bases decompose).**  `isMinBase_iff_comp`.  If `M.E = E`, then for
every `u ∈ ℝ^E` and `B ⊆ E`: `B` is a minimum base of `u` in `M` if and only if, for every
component `K`, `B ∩ K` is a minimum base of `u` in `M ↾ K`.

*Proof.*  Step 1, the base condition in both directions is Corollary 11.  Step 2, minimality
of `B ∩ K`.  Let `B_K` be a base of `M ↾ K`, so `B_K ⊆ K`.  The set `B' = (B \ K) ∪ B_K`
satisfies `B' ∩ K = B_K` and `B' ∩ K' = B ∩ K'` for every other component `K'`, which is
disjoint from `K`; by Corollary 11 it is a base of `M`.  Since `B \ K` and `B_K` are
disjoint, `u(B') = u(B \ K) + u(B_K)`, and `u(B) = u(B ∩ K) + u(B \ K)`.  So
`u(B) ≤ u(B')` gives `u(B ∩ K) ≤ u(B_K)`.  Step 3, minimality of `B`.  For a base `B'` of
`M`, every `B' ∩ K` is a base of `M ↾ K` (Corollary 11), so `u(B ∩ K) ≤ u(B' ∩ K)`; summing
over the components with `sum_eq_sum_comp` gives `u(B) ≤ u(B')`.

**Theorem 13 (exchange criterion, Lemma `lem:minbases`(1)).**  `isMinBase_iff_fundCircuit`,
with the two halves `le_of_mem_fundCircuit` and `isMinBase_of_forall_fundCircuit`.  For every
`u ∈ ℝ^E` and `B ⊆ E`: `B` is a minimum base of `u` if and only if `B` is a base and
`u_f ≤ u_e` whenever `e ∉ B` and `f ∈ C(B, e)`.  (No hypothesis on the ground set.)

*Proof of "only if".*  Step 1, if `f = e` there is nothing to prove; if `e ∉ M.E`, then
`C(B, e) = {e}` and `f = e`.  Step 2, otherwise `e ∈ cl(B) = M.E` and
`f ∈ C(B, e) \ {e} ⊆ B`; Mathlib's `Indep.mem_fundCircuit_iff` makes `B + e - f` independent,
hence a base (`IsBase.exchange_isBase_of_indep'`).  Step 3, minimality gives
`u(B) ≤ u(B) + u_e - u_f`.

*Proof of "if".*  Let `B'` be a base; induction on `|B' \ B|`, for all bases `B'`.  Step 1, if
`B ⊆ B'`, then `B = B'`, since no base is a proper subset of another.  Step 2, otherwise take
`f ∈ B \ B'`.  The fundamental circuit `C(B', f)` and the fundamental cocircuit `C*(B, f)`
both contain `f`; a circuit and a cocircuit that meet have at least two common elements
(Mathlib's `IsCircuit.isCocircuit_inter_nontrivial`), so they share some `e ≠ f`.  Step 3,
`e ∈ C(B', f) ⊆ B' + f` gives `e ∈ B'`; `e ∈ C*(B, f) ⊆ (E \ B) + f` gives `e ∉ B`; and
`e ∈ C*(B, f)` if and only if `f ∈ C(B, e)` (Mathlib's
`IsBase.mem_fundCocircuit_iff_mem_fundCircuit`), so the hypothesis gives `u_f ≤ u_e`.
Step 4, `e ∈ C(B', f)` makes `B'' = B' - e + f` a base.  Since `f ∈ B`,
`B'' \ B = (B' \ B) - e` has one element fewer than `B' \ B`, and the induction hypothesis
gives `u(B) ≤ u(B'') = u(B') - u_e + u_f ≤ u(B')`.

**Theorem 14 (minimum bases see only comparisons within components).**  `isMinBase_congr`:
let `u, u' ∈ ℝ^E` satisfy `u_e ≤ u_f ⇔ u'_e ≤ u'_f` for all `e, f` with `connRel M e f`
(that is, in one component).  Then `B` is a minimum base of `u` if and only if it is a
minimum base of `u'`.  `isMinBase_iff_isBase`: if `u_e = u_f` whenever `connRel M e f`, then
every base is a minimum base of `u`.

*Proof.*  Step 1, by Theorem 13 both sides say that `B` is a base and that `u_f ≤ u_e`
(respectively `u'_f ≤ u'_e`) for `e ∉ B` and `f ∈ C(B, e)`.  Step 2, for such a pair,
`f ∈ C(B, e) ⊆ comp M e` (Proposition 7), so `connRel M f e`, and the hypothesis turns one
inequality into the other.  Step 3, for `isMinBase_iff_isBase`, the hypothesis of the first
part holds for `u` and `u' = 0`, and for `u' = 0` every base has weight `0`, so every base is
minimum.

**Corollary 15 (the matroid `M^u`).**  `minBases_ground`: the ground set of `minBases M u` is
`E`.  `minBases_congr`: suppose the bases of `minBases M u` are exactly the minimum bases of
`u`, and the bases of `minBases M u'` exactly the minimum bases of `u'` (Lemma
`lem:minbases`(3) at `u` and at `u'`), and `u_e ≤ u_f ⇔ u'_e ≤ u'_f` whenever
`connRel M e f`.  Then `minBases M u = minBases M u'`.  `minBases_eq_self`: if `M.E = E`, the
bases of `minBases M u` are exactly the minimum bases of `u`, and `u_e = u_f` whenever
`connRel M e f`, then `minBases M u = M`.

*Proof.*  Step 1, the ground set of `minBases M u` is `⋃_ℓ {u = ℓ} = E`
(`levelPiece_ground`).  Step 2, two matroids with the same ground set and the same bases are
equal (Mathlib's `ext_isBase`), and every subset of `E` is a `Finset`.  Step 3, the bases
agree by the hypotheses and Theorem 14 (respectively `isMinBase_iff_isBase`).


## 2. Correspondence

| paper | Lean names | module | status |
| :-- | :-- | :-- | :-- |
| `lem:minbases`(4), "the ground set splits into connected components" | `connRel_equivalence`, `comp`, `components`, `existsUnique_mem_components`, `disjoint_of_mem_components`, `comp_eq_comp_iff` | `Rainbow/Connectivity.lean` | proved |
| (classical, used for transitivity) | `exists_isCircuit_of_inter_nonempty` | same | proved |
| loops (and coloops) are components by themselves | `comp_eq_singleton_of_isLoop`, `comp_eq_singleton_of_isColoop` | same | proved |
| `lem:minbases`(4), "two non-loops lie on a common circuit exactly when they lie in one component" | `exists_isCircuit_iff_comp_eq` | same | proved, for distinct elements (Section 3) |
| a circuit lies in one component; `C(B, e) ⊆ K_e` | `isCircuit_subset_comp`, `fundCircuit_subset_comp` | same | proved |
| `lem:minbases`(4), "closure decomposes" | `mem_closure_iff_comp`, `closure_eq_biUnion_comp` | same | proved |
| rank is additive over components | `rk_eq_sum_comp`, `isBasis_inter_comp`, `sum_eq_sum_comp` | same | proved |
| `M` is the direct sum of the `M ↾ K` | `eq_disjointSigma`, `pairwise_disjoint_components`, `isBase_iff_comp` | same | proved |
| `lem:minbases`(4), "minimum bases decompose" | `isMinBase_iff_comp` | same | proved |
| `lem:minbases`(1) | `isMinBase_iff_fundCircuit`, `le_of_mem_fundCircuit`, `isMinBase_of_forall_fundCircuit` | same | proved (also assigned to `Rainbow/MinBases.lean`) |
| minimum bases depend only on comparisons within components | `isMinBase_congr`, `isMinBase_iff_isBase` | same | proved |
| `M^u` depends only on comparisons within components | `minBases_ground`, `minBases_congr`, `minBases_eq_self` | same | proved, given `lem:minbases`(3) as a hypothesis |


## 3. Differences from the paper

1. **"Two non-loops".**  The sentence "two non-loops lie on a common circuit exactly when they
   lie in one component" holds for any two distinct elements, loops included: a loop lies
   only on the circuit `{e}` and is a component by itself (Proposition 5).  It fails for one
   element counted twice when that element is a coloop: a coloop is a non-loop that lies on
   no circuit, yet it lies in its own component.  So "two" has to mean "two distinct", and
   then the non-loop condition is not needed.  Lean: `exists_isCircuit_iff_comp_eq` assumes
   only `e ≠ f`, which contains the paper's statement.
2. **Components are not defined in the paper.**  They are taken to be the classes of the
   relation "equal, or on a common circuit" (`connRel`, Proposition 2; Oxley, Section
   4.1), as `Rainbow/Defs.lean` fixes.
3. **What "decompose" means.**  Closure: `e ∈ cl(X)` if and only if `e ∈ cl(X ∩ K_e)` for the
   component `K_e` of `e`, equivalently `cl(X) = ⋃_K cl(X ∩ K)`.  Minimum bases: `B` is
   minimum if and only if every `B ∩ K` is minimum in `M ↾ K`.  Rank additivity and the
   direct sum are formalized as well.
4. **A form the paper uses without stating it.**  The observer of Lemma `lem:observer`
   computes only comparisons `u(x) < u(y)` for `x, y` in one component (Step 2) and the rank
   of `N_G` component by component (Step 3).  Its correctness rests on Theorem 14 and
   Corollary 15: the minimum bases of `u`, and `M^u`, depend only on the comparisons of `u`
   within components.  Step 4 of Proposition `prop:posl` ("each component is one cluster, so
   `N(t) = M`") is `minBases_eq_self`.
5. **Lemma `lem:minbases`(1)** is proved here as well (Theorem 13), since Theorem 14 rests on
   it and the parallel module `Rainbow/MinBases.lean` was not available.  When the modules are
   merged, one of the two proofs can be dropped.
6. **Lemma `lem:minbases`(3) enters `minBases_congr` and `minBases_eq_self` as an explicit
   hypothesis** (the bases of `minBases M u` are the minimum bases of `u`), because item 3 is
   formalized in `Rainbow/MinBases.lean`.  With that theorem the two corollaries hold
   unconditionally.

Proposed wording for item 4 of Lemma `lem:minbases`:

> The ground set splits into connected components, the classes of the equivalence relation
> "`e = f`, or `e` and `f` lie on a common circuit"; two distinct elements lie on a common
> circuit exactly when they lie in one component, and loops and coloops are components by
> themselves.  Closure, rank and minimum bases decompose over components:
> `e ∈ cl(X)` if and only if `e ∈ cl(X ∩ K)` for the component `K` of `e`,
> `r(X) = Σ_K r(X ∩ K)`, and a base `B` is minimum if and only if every `B ∩ K` is a minimum
> base of `M ↾ K`.  In particular the minimum bases of `u`, and `M^u`, depend only on the
> comparisons `u_e ≤ u_f` between elements of one component.


## 4. Module line counts

| module | lines |
| :-- | :-- |
| `SignedTropical/Rainbow/Connectivity.lean` | 421 |


## 5. Not done

* `minBases_congr` and `minBases_eq_self` are conditional on Lemma `lem:minbases`(3), which
  belongs to `Rainbow/MinBases.lean` (agent P0a); see Section 3, item 6.
* The rank formula `eq:rank-mu` applied within components (Lemma `lem:observer`, Step 3) is
  not formalized: it is not part of item 4.  It follows from Lemma `lem:minbases`(3),
  `eq:rank-mu` and Theorem 12.
* That each restriction `M ↾ K` to a component is a connected matroid is not formalized; the
  paper does not state or use it.
