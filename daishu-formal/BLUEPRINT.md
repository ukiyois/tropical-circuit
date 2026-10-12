# Formalization blueprint: `SignedTropical`

Lean 4 `v4.32.0`, Mathlib `v4.32.0` (the stable version already used in `daishu`). Companion to
`daishu/paper/signed_assignment.tex`, `daishu/paper/greedy_intersection.tex` and
`daishu/docs/research-direction-2026-10-11.md`.  The natural-language statements and
step-structured proofs of everything proved here are in `PHASE1.md`, which agrees with the
Lean statements exactly.

## 1. Scope

| Tier | Content | Paper | Status |
|---|---|---|---|
| **1** | circuits; homomorphism lemma; inlining; sorting network; gap sum; `lem:bit`; `lem:lift` with vanishing; `thm:compiler` and `cor:integer-observable` with explicit sizes; `prop:sugeno`; `thm:lattice` (size and depth) | §3 | **done** |
| **1+** (Phase 1) | Theorem A (greedy compiled), Theorem B (simulating back) | research direction §3.2, `greedy_intersection.tex` §3 | **done** |
| 1+ corollaries | C for binary matroids; D (counting); E (virtual extension complexity); F (upper bound; lower bound) | research direction §3.2 | **done**; D, E and the lower half of F take the external results as explicit hypotheses |
| 1 (extensions) | the `±` normal form (Prop. 5.4); the integral form and Lemma `lem:lipschitz`; the asymptotic Corollary D; Corollary C for finite fields, `ℚ`, duals, graphic, cographic and transversal matroids and gammoids | §3, §5; `greedy_intersection.tex` §2, §3 | **done** (2026-10-12, `PHASE2.md`) |
| Phase 2 | `greedy_intersection.tex` §4 and §5: rainbow bases (Theorem C) and matroid intersection (Theorem D), every lemma and proposition | §4, §5 | **done** (2026-10-12, `PHASE2.md`) |
| 2 | the main theorem's heart: feasibility, bottleneck semantics, progress dichotomy, termination, optimality | §4 | after Phase 2's first milestone |
| none | the Boolean observer, a matching algorithm as a circuit | App. A | **interface only** |
| none | the lower bounds of Appendix B | App. B | **not formalized** |

The observer is a hypothesis with a precise statement: a Boolean circuit of
stated size that returns `ν(G)`, `S(G)`, `T(G)` from the adjacency bits. Its
correctness is classical algorithmics and its formal proof would cost thousands
of lines for little gain in trust.

## 2. Design decisions

**D1. Circuits: operands and gates.**  A circuit on `n` inputs is a list of gates and
a list of output operands.  An operand is an input coordinate, the constant source, or a
wire addressed by the index of the gate producing it; a gate is an operation with two
operands.  Size is the number of gates, so sources cost nothing, as in Definition
`def:models`.  Evaluation is total: a reference to a wire that does not exist yet reads
the constant, which a constant operand would read anyway.  Lattice circuits, which have no
constant, are restricted to proper operands (`Circuit.IsLattice`).  (Changed from the first
design, in which inputs and the constant were gates and size was the length of the list:
the paper counts only operation gates, and operands make inlining a renumbering.)
Sharing is not optional: the `±` normal form is linear in size only because the
two halves of a gate are shared by all its successors.

**D2. One homomorphism lemma serves many theorems.**  If `φ : α → β` maps the constant to
the constant and commutes with every operation, then `φ ∘ eval = eval ∘ φ` wire by wire
(`wires_map`); the relative form asks commutation only on values satisfying a predicate
that holds at every wire (`wires_map_of`).  Instances:

| map `φ` | result |
|---|---|
| `x ↦ [t ≤ x]` on lattice circuits | the threshold identity, hence `thm:lattice` |
| `false ↦ 0`, `true ↦ 1`, `Bool → ℝ` | the converse half of `thm:lattice` |
| `b ↦ Δ·b`, Boolean gates to the lifted gates | `lem:lift` |
| a one-point reading to `0` | vanishing of the lifted circuit at `Δ = 0` |
| `Int.cast : ℤ → ℝ` | Theorem B, sanity examples |
| `BitVec.ofInt W`, relative form with `|v| ≤ 2^S` | two's complement simulation in Theorem B |
| negation, exchanging `min` and `max` | the lower half of Corollary F |

**D3. The sorting network is insertion sort.**  The comparator network
`ins(a, b :: l) = min(a,b) :: ins(max(a,b), l)` computes Mathlib's `List.insertionSort`
exactly (`isortV_eq_insertionSort`), so correctness is Mathlib's and no 0-1 principle is
needed.  `m(m-1)/2` comparators at three gates each; the cost is absorbed by the `m²` term
of the compiler, so the bound has no `m log² m` term.  (Changed from odd-even
transposition with the 0-1 principle: the identification with `List.insertionSort` is
shorter than a proof that odd-even transposition sorts 0-1 vectors.)

**D4. `C_F` is defined as the gap sum.**  `C_F(D) = Σ_k (s_{k+1} − s_k) F(G_k)`
with the sorted values and a zero prepended.  The integral form and the Lipschitz bound are
remarks in the paper and are not needed for any size theorem, so no measure theory enters.

**D5. Lovász extension through the sorted order.**  Proved: `h_M(1_T) = r(T)`;
`h_M(w + μ·1) = h_M(w) + μ·k`; and, on `D ≥ 0`, `h_M(D) = C_F(D)` for
`F(S) = r(E \ S)`, through the layer-cake identity `D_e = Σ_k Δ_k [s_k < D_e]` and a basis
that restricts to a basis of every level set of a chain.

**D6. Matroids are Mathlib's.**  `Matroid (Fin m)` with ground set `univ`, rank `eRk`,
and its natural-number value `rk`; no separate rank axioms (the bridge planned here turned
out unnecessary).  Greedy optimality is not in Mathlib and is proved here
(`maxBasisWeight_eq_gapSum`).

**D7. Bipartite graphs for Tier 2.**  `Finset (Fin n × Fin n)`, matchings as
sets of pairs with distinct rows and distinct columns.  Mathlib `v4.32.0` has
perfect matchings, alternating structures, Tutte and Hall, but **no König, no
Berge for maximum matchings and no Dulmage-Mendelsohn**; those are built here.
`SimpleGraph` is avoided because its single vertex type makes the two sides
awkward.

**D8. Builders.**  Every construction appends gates to a list and returns operands.
`Den I gs a f` (operand `a` carries `f x` at every input `x`) is stable under appending, and
one generic combinator inlines a circuit with one gadget per gate (`inline`, `inline_spec`),
where a source wire is represented by one operand (lifting, Corollary F) or by a list of
operands carrying bits (Theorem B).

**D9. Theorem B through `BitVec`.**  Two's complement values are Lean core `BitVec W`;
the ripple-carry adder is proved against `BitVec` addition with Lean's bitblasting lemmas
(`getLsbD_add_add_bool`, `carry_succ`, `slt_eq_not_carry`).

**D10. Binary matroids.**  `IndepMatroid.ofFinset` with linear independence over `ZMod 2`;
rank equals the dimension of the column span and Mathlib's `Matrix.rank`; the rank circuit
is a branch-free echelon elimination proved correct by a span invariant.  Since 2026-10-12 the
column matroid and the span invariant are proved once over every field (`Elimination.lean`), and
the Boolean elimination is read over `GF(2)` through it (`zst_elimV`).

## 3. Module map

| Module | Contents | Paper | Lines | Status |
|---|---|---|---|---|
| `SignedTropical/Circuit.lean` | operands, gates, circuits, evaluation, size; **homomorphism lemma**; builders, `Den` | D1, D2, D8 | 348 | **done** |
| `SignedTropical/Inline.lean` | inlining with one gadget per gate | D8 | 166 | **done** |
| `SignedTropical/Models.lean` | gate sets; `bitsVal` | `def:models` | 128 | **done** |
| `SignedTropical/Sorting.lean` | insertion-sort network as a signed tropical builder | D3 | 163 | **done** |
| `SignedTropical/GapSum.lean` | sorted values, gap sum, `lem:bit`, layer cake | `def:filtration`, `lem:bit` | 188 | **done** |
| `SignedTropical/Lift.lean` | amplitude lifting, vanishing at `Δ = 0` | `lem:lift` | 173 | **done** |
| `SignedTropical/Compiler.lean` | the compiled circuit, its value, its size; Horner | `thm:compiler`, `cor:integer-observable` | 531 | **done** |
| `SignedTropical/Lattice.lean` | lattice circuits, threshold identity, Sugeno form, `Lat = Mon` | `prop:sugeno`, `thm:lattice` | 383 | **done** |
| `SignedTropical/Matroid.lean` | rank bridge, `h_M`, bases along a chain, greedy as a gap sum | Phase 1, D5, D6 | 244 | **done** |
| `SignedTropical/TheoremA.lean` | Theorem A | Phase 1 | 326 | **done** |
| `SignedTropical/Converse.lean` | Theorem B: integer bound, `BitVec` simulation, Boolean gadgets | Phase 1, `thm:equivalence` | 690 | **done** |
| `SignedTropical/Subtractionfree.lean` | Corollary F, upper bound proved, lower bound under JSS | Phase 1 | 481 | **done** |
| `SignedTropical/Elimination.lean` | column matroids over a field, elimination without branching | Phase 1, D10 | 436 | **done** |
| `SignedTropical/Binary.lean` | binary matroids, Boolean elimination, rank circuit, Corollary C | Phase 1, D10 | 671 | **done** |
| `SignedTropical/Counting.lean` | counting Boolean circuits, Corollary D under a matroid count | Phase 1 | 293 | **done** |
| `SignedTropical/Polytope.lean` | base polytope support function, Corollary E under Hertrich-Loho | Phase 1 | 87 | **done** |
| `SignedTropical/Examples.lean` | kernel-checked sanity examples | | 190 | **done** |
| `SignedTropical/NormalForm.lean` | `±` decomposition, `eval C = eval A − eval B`, `size ≤ c·size C` | Prop 5.4 | | not started |

Dependency order: `Circuit` → { `Inline`, `Models` } → { `Sorting`, `Lift` } → `GapSum` →
{ `Compiler`, `Lattice`, `Matroid` } → `TheoremA` → { `Converse`, `Subtractionfree` } →
{ `Binary`, `Counting` } → `Polytope` → `Examples`.

## 4. Milestones

1. Toolchain, Mathlib cache, `SLP` with the homomorphism lemma proved. **Done
   2026-10-11.**
2. Circuits with operands (D1), inlining (D8). **Done 2026-10-11.**
3. Sorting network, gap sum, `lem:bit`, `lem:lift`. **Done 2026-10-11.**
4. `thm:compiler` with the size `3ms + mN + 6m²` and `cor:integer-observable`. **Done
   2026-10-11.**
5. `prop:sugeno`, `thm:lattice` with size and depth. **Done 2026-10-11.**
6. Greedy as a gap sum and Theorem A with the size `3ms + mL + 9m² + 4m + 4L + 1`. **Done
   2026-10-11.**
7. Theorem B with the size `15S² + 40S`, on `{0,1}^E`. **Done 2026-10-11.**
8. Corollary C for binary matroids, `O(m²r²)`; Corollaries D, E, F. **Done 2026-10-11.**
9. `NormalForm` (Prop 5.4); the integral form and `lem:lipschitz`; the asymptotic Corollary
   D; Corollary C for further classes.  **Done 2026-10-12.**
10. Phase 2: the shared interface `Rainbow/Defs.lean`, then minimum bases, components, exchange
    graphs, possibly optimal bases, validity, PO-SL, the potential, the Boolean gadget
    library, the matroid intersection circuit, the observer, Theorems C and D.  **Done
    2026-10-12**, by dependency-scheduled agents and the coordinator; module map and
    correspondence in `PHASE2.md`.
11. Open: Tier 2 of the companion paper (the assignment main theorem).

`lake build`: no warnings; `#print axioms` on every main theorem: `propext`,
`Classical.choice`, `Quot.sound`.

## 5. Conventions

No `sorry` in a merged module; a statement that is not yet proved lives in this
file, not in the code.  Lemma names follow Mathlib style.  Each paper result
carries a docstring naming its label in `signed_assignment.tex` or the research
direction.  External results enter as explicit hypotheses of the theorems that use them,
never as axioms.
