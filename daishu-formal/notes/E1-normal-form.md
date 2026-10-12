# E1. The `±` normal form

Natural-language companion of `SignedTropical/NormalForm.lean` (namespace
`SignedTropical.NormalForm`).  Source: `daishu/paper/signed_assignment.tex`, Proposition
`prop:normal-form` (line 1428) and display `eq:normal-form`.

Every statement below is the reading of the Lean declaration named next to it, with the same
hypotheses, the same conclusion and the same constants.  Proofs follow the Lean proofs step
by step.

**Build status.**  `lake build SignedTropical.NormalForm` succeeds with no error and no
warning.  The module contains no `sorry`, `admit`, `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe` or `opaque`.  Every theorem of the table in Section 2
depends only on `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`).

Notation.  Circuits, readings, evaluation and size are those of `PHASE1.md`, Definitions 1.1
to 1.3: a circuit on `n` inputs is a list of gates and a list of output operands, an operand is
an input coordinate, the constant source or a wire, and the size `|C|` is the number of gates.
For a reading `I` and an input `x`, `C_I(x)` is the list of output values.  `σ` ranges over
`{max, min}` and `σ̄` is the other element.  "Linearly ordered additive commutative group"
means Lean's `[AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]`; `ℝ` is one.  For
lists, `u - v` is the componentwise difference `List.zipWith (· - ·) u v`.


## 1. Definitions and results

### 1.1 Definitions

**Definition 1 (the two bases).**  `Sel` has the two elements `max` and `min`; `σ.op` is `max`
or `min` in a linear order (`Sel.op`), and `σ.swap = σ̄` (`Sel.swap`).  `SignedOp` has three
gates `sel`, `add`, `sub`; `PlusOp` has two gates `sel`, `add`.  For an additive commutative
group `R` with a linear order:

* `signedInterp σ R` reads `sel` as `σ`, `add` as `+`, `sub` as `-`, and the constant source as
  `0`;
* `plusInterp σ R` reads `sel` as `σ`, `add` as `+`, and the constant source as `0`.

A *circuit over `σ`, `+`, `-` and the constant `0`* is a `Circuit SignedOp n` read with
`signedInterp σ R`; a *circuit over `σ`, `+` and the constant `0`* is a `Circuit PlusOp n` read
with `plusInterp σ R`.  Inputs and the constant are free sources in both.

**Definition 2 (renaming).**  For `f : Op → Op'`, `relabel f C` replaces the operation `o` of
every gate of `C` by `f o` and keeps all operands and outputs (`relabel`).  Three renamings
connect the bases to Phase 1: `ofSTOp` sends Phase 1's signed tropical gates `max, +, -`
(`STOp`) to `sel, add, sub`; `toSTOp` is its inverse; `toTropOp σ` sends `sel` to `σ` and `add`
to `+` in Phase 1's `(min, +, max)` gates (`TropOp`).

**Definition 3 (the pair construction).**  A *pair* is two operands `(p⁺, p⁻)`.  The gadget of
one gate on the pairs `a = (a⁺, a⁻)` and `b = (b⁺, b⁻)` appends gates over `σ`, `+` and returns
a pair (`pairGad`, with the two-addition builder `add2`):

* `a + b`: two gates, returns `(a⁺ + b⁺, a⁻ + b⁻)`;
* `a - b`: two gates, returns `(a⁺ + b⁻, a⁻ + b⁺)`;
* `σ(a, b)`: four gates `u = a⁺ + b⁻`, `v = b⁺ + a⁻`, `q = σ(u, v)`, `r = a⁻ + b⁻`, returns
  `(q, r)`.

`pairs C` inlines these gadgets for the gates of `C` in order into one gate list, starting
from the empty list, with an input `x_i` represented by `(x_i, 0)` and the constant by `(0, 0)`,
and returns the gate list and one pair per output of `C` (Phase 1's `inline`).  `posCircuit C`
is this gate list with the first halves of the output pairs as outputs, and `negCircuit C` is
the same gate list with the second halves.  The construction depends neither on `σ` nor on
`R`.

**Definition 4 (the interchange circuit).**  The gadget `swapGad` replaces a gate `sel(a, b)`
by three gates `t₁ = a + b`, `t₂ = sel(a, b)`, `t₃ = t₁ - t₂` and returns `t₃`; it copies an
`add` or `sub` gate.  `swapCircuit C` inlines these gadgets for the gates of `C`, with inputs and
the constant represented by themselves.

### 1.2 Lemmas

**Lemma 1.1 (renaming; `eval_relabel`, `size_relabel`, `outs_relabel`).**  Let `I` read `Op`
and `J` read `Op'` in the same carrier, with the same constant (`J.zero = I.zero`) and with
`J.op (f o) = I.op o` for every `o`.  Then for every circuit `C` and every input `x`,
`(relabel f C)_J(x) = C_I(x)`.  Moreover `|relabel f C| = |C|` and `relabel f C` has the outputs
of `C`.

*Proof.*
1. An operand reads the same value under `J` and under `I` in the same wire list, since only
   the constant could differ and the constants agree.
2. Induction on the gate list, appending one gate at a time: the wire values of the renamed
   list under `J` equal those of the original list under `I`.  At the appended gate both sides
   read the same operand values (Step 1 and the induction hypothesis), and
   `J.op (f o) = I.op o`.
3. The outputs are read from equal wire lists (Step 1).  The size and the outputs are unchanged
   by definition.

**Corollary 1.2 (the bridges; `eval_relabel_ofSTOp`, `eval_relabel_toSTOp`,
`eval_relabel_toTropOp`).**  For an additive commutative group `R` with a linear order:
`(relabel ofSTOp C)` read with `signedInterp max R` has the outputs of the Phase 1 circuit `C`
read with `stInterp R`; `(relabel toSTOp C)` read with `stInterp R` has the outputs of `C` read
with `signedInterp max R`.  Over `ℝ`, `relabel (toTropOp σ) A` read with Phase 1's `tropInterp`
has the outputs of `A` read with `plusInterp σ ℝ`.

*Proof.*  Lemma 1.1; the constants are `0` on both sides and the operations agree gate by gate.

**Lemma 1.3 (gate counts; `sum_cost_le`, `size_posCircuit`, `size_posCircuit_le`,
`size_swapCircuit`, `size_swapCircuit_le`).**  If every gate costs at most `c`, a gate list
costs at most `c` times its length.  `|posCircuit C| = 4·#σ + 2·#(+) + 2·#(-)`, where `#o` is
the number of gates `o` of `C`, so `|posCircuit C| ≤ 4 |C|`; and
`|swapCircuit C| = 3·#σ + #(+) + #(-) ≤ 3 |C|`.

*Proof.*
1. The sum of a list of numbers each at most `c` is at most `c` times its length (Mathlib's
   `List.sum_le_card_nsmul`).
2. Each gadget appends exactly its cost: `4, 2, 2` for `pairGad` (`length_pairGad`), `3, 1, 1`
   for `swapGad` (`length_swapGad`).  Phase 1's `length_inline` gives the exact counts.
3. Step 1 with `c = 4` and `c = 3`.

**Lemma 1.4 (translation; `Sel.op_sub_sub`).**  In a linearly ordered additive commutative
group, `σ(a - c, b - c) = σ(a, b) - c` for all `a, b, c`.

*Proof.*  Mathlib's `max_sub_sub_right` and `min_sub_sub_right`.

**Lemma 1.5 (the gadgets; `add2_spec`, `pairGad_spec`).**  Let `R` be a linearly ordered
additive commutative group.  Say that a pair `(p⁺, p⁻)` *carries* `f : R^n → R` in a gate list
`gs` if, read with `plusInterp σ R` in `gs`, `p⁺` and `p⁻` are valid operands with values
`f⁺(x)` and `f⁻(x)` at every input `x`, and `f = f⁺ - f⁻` (`PairDen σ gs p f`).  If `a` carries
`f` and `b` carries `g` in `gs`, then the gadget of the gate `o` appends to `gs` and its pair
carries `o(f, g)`, read with `signedInterp σ R`, in the extended list.

*Proof.*
1. `add2` appends two additions; their values are `a⁺ + b⁺` and `a⁻ + b⁻` for the arguments
   given (Phase 1's `den_emit`), and earlier operands keep their values (`Den.mono`).
2. `+`: `(f⁺ + g⁺) - (f⁻ + g⁻) = (f⁺ - f⁻) + (g⁺ - g⁻)`.
3. `-`: `(f⁺ + g⁻) - (f⁻ + g⁺) = (f⁺ - f⁻) - (g⁺ - g⁻)`.
4. `σ`: the four gates have values `u = f⁺ + g⁻`, `v = g⁺ + f⁻`, `q = σ(u, v)` and
   `r = f⁻ + g⁻`.  By Lemma 1.4 with `c = f⁻ + g⁻`,
   `q - r = σ(u - c, v - c) = σ(f⁺ - f⁻, g⁺ - g⁻) = σ(f, g)`.

### 1.3 The normal form

**Theorem 1.6 (the `±` decomposition; `eval_eq_sub`).**  Let `σ ∈ {max, min}` and `R` a linearly
ordered additive commutative group.  For every circuit `C` on `n` inputs over `σ`, `+`, `-` and
every `x ∈ R^n`,
`C_{signedInterp σ R}(x) = (posCircuit C)_{plusInterp σ R}(x) - (negCircuit C)_{plusInterp σ R}(x)`
componentwise.

*Proof.*
1. (`pairs_spec`)  Phase 1's inlining lemma `inline_spec`, with "carries" of Lemma 1.5 as the
   representation relation: carrying is stable under appending gates (`PairDen.mono`); the pair
   `(0, 0)` carries `0` since `0 = 0 - 0`; the pair `(x_i, 0)` carries `x_i`; and the gadgets are
   correct by Lemma 1.5.  So the `j`-th output pair carries the `j`-th output of `C`, read with
   `signedInterp σ R`.
2. (`eval_of_forall₂`)  Induction on the output list: reading the first halves of the pairs
   gives the outputs of `posCircuit C`, the second halves those of `negCircuit C`, and their
   differences are the outputs of `C` by Step 1.

**Proposition 1.7 (`prop:normal-form`, shared form; `normal_form_shared`).**  Let `σ` be `max`
or `min` and `R` a linearly ordered additive commutative group.  For every circuit `C` on `n`
inputs over `σ`, `+`, `-` and the constant `0` with `N` outputs, there are circuits `A` and `B`
on `n` inputs over `σ`, `+` and the constant `0` such that `A` and `B` have the same list of
gates, `|A| ≤ 4 |C|`, `A` and `B` have `N` outputs each, and
`C(x) = A(x) - B(x)` componentwise at every `x ∈ R^n`.

Taking all wires of `C` as its outputs (which does not change `|C|`), the proposition gives one
gate list of at most `4 |C|` gates computing, for every gate `g` of `C`, values `g⁺` and `g⁻`
with `g = g⁺ - g⁻`: the shared form of the paper's proof.

*Proof.*
1. `A = posCircuit C`, `B = negCircuit C`; they have the same gates by definition
   (`gates_negCircuit`).
2. `|A| ≤ 4 |C|` by Lemma 1.3.
3. One pair per output of `C` (`length_outs_posCircuit`, `length_outs_negCircuit`).
4. The values by Theorem 1.6.

**Proposition 1.8 (`prop:normal-form`; `normal_form`).**  Let `σ` be `max` or `min` and `R` a
linearly ordered additive commutative group.  For every circuit `C` on `n` inputs over `σ`, `+`,
`-` and the constant `0` with `N` outputs, there are circuits `A` and `B` on `n` inputs over `σ`,
`+` and the constant `0`, with `N` outputs each and `|A| + |B| ≤ 8 |C|`, such that
`C(x) = A(x) - B(x)` componentwise at every `x ∈ R^n`.

*Proof.*
1. Proposition 1.7 gives `A` and `B` with the same gates and `|A| ≤ 4 |C|`.
2. Same gates give `|B| = |A|`, so `|A| + |B| ≤ 8 |C|`.

**Corollary 1.9 (Phase 1's circuits, `σ = max`; `normal_form_stOp`).**  Let `R` be a linearly
ordered additive commutative group.  For every Phase 1 signed tropical circuit `C` (gates
`max`, `+`, `-`, constant `0`, read with `stInterp R`) with `N` outputs, there are circuits `A`
and `B` over `max`, `+` and the constant `0`, with `N` outputs each and `|A| + |B| ≤ 8 |C|`, such
that `C(x) = A(x) - B(x)` componentwise at every `x ∈ R^n`.

*Proof.*
1. Proposition 1.8 at `σ = max` for `relabel ofSTOp C`, which has the size and the outputs of
   `C` (Lemma 1.1).
2. Its values are those of `C` (Corollary 1.2).

### 1.4 Interchanging the bases

**Lemma 1.10 (`Sel.add_sub_swap`).**  In an additive commutative group with a linear order,
`a + b - σ̄(a, b) = σ(a, b)`.

*Proof.*  `min(a, b) + max(a, b) = a + b` (Mathlib's `min_add_max`), rearranged.

**Proposition 1.11 (`prop:normal-form`, interchange of the bases; `eval_swapCircuit`,
`interchange`).**  Let `σ` be `max` or `min` and `R` an additive commutative group with a linear
order.  For every circuit `C` on `n` inputs over `σ`, `+`, `-` and the constant `0`, the circuit
`swapCircuit C` over `σ̄`, `+`, `-` and the constant `0` has `|swapCircuit C| ≤ 3 |C|` and, at
every `x ∈ R^n`, the same outputs as `C`.  In particular every circuit over `max`, `+`, `-` of
size `s` has the outputs of a circuit over `min`, `+`, `-` of size at most `3 s`, and conversely.

*Proof.*
1. (`swapGad_spec`)  The gadget of `sel(a, b)`, read with `signedInterp σ̄ R`, has values
   `t₁ = a + b`, `t₂ = σ̄(a, b)` and `t₃ = a + b - σ̄(a, b) = σ(a, b)` by Lemma 1.10; the gadgets
   of `+` and `-` emit the same gate.
2. Phase 1's `inline_spec` with the representation relation "denotes, read with
   `signedInterp σ̄ R`" (Phase 1's `Den`): every output of `swapCircuit C` read with `σ̄` is the
   corresponding output of `C` read with `σ`.
3. The size by Lemma 1.3.

**Corollary 1.12 (Phase 1's circuits; `stOp_to_min`, `min_to_stOp`).**  Let `R` be an additive
commutative group with a linear order.  Every Phase 1 signed tropical circuit `C` (read with
`stInterp R`) has, at every `x ∈ R^n`, the outputs of a circuit over `min`, `+`, `-` and the
constant `0` (read with `signedInterp min R`) of size at most `3 |C|`; and every circuit over
`min`, `+`, `-` and the constant `0` has the outputs of a Phase 1 signed tropical circuit of size
at most three times its size.

*Proof.*
1. Max to min: `swapCircuit (relabel ofSTOp C)`; Proposition 1.11 at `σ = max`, then
   Corollary 1.2 and Lemma 1.1 for the values and the size.
2. Min to max: `relabel toSTOp (swapCircuit C)`; Proposition 1.11 at `σ = min`, then
   Corollary 1.2 and Lemma 1.1.

**Corollary 1.13 (the route of `eq:normal-form`; `normal_form_stOp_min`).**  Let `R` be a
linearly ordered additive commutative group.  For every Phase 1 signed tropical circuit `C` with
`N` outputs there are circuits `A` and `B` over `min`, `+` and the constant `0`, with `N` outputs
each and `|A| + |B| ≤ 24 |C|`, such that `C(x) = A(x) - B(x)` componentwise at every `x ∈ R^n`.

*Proof.*
1. `C' = swapCircuit (relabel ofSTOp C)` is over `min`, `+`, `-`, has `|C'| ≤ 3 |C|`, the outputs
   of `C` at every input (Corollary 1.12, Step 1), and as many outputs as `C`.
2. Proposition 1.8 at `σ = min` for `C'`: `|A| + |B| ≤ 8 |C'| ≤ 24 |C|`.
3. `C(x) = C'(x) = A(x) - B(x)`.

### 1.5 Theorem A in normal form

**Corollary 1.14 (`theoremA_normal_form`).**  Let `M` be a matroid on `E = {0, …, m-1}` with
ground set `E` and rank `k`, and let a Boolean circuit `B` of size `s` output `r(S)` in binary
from the indicator vector of `S`, for every `S ⊆ E` (the hypotheses of Phase 1's `theoremA`).
Then there are circuits `P` and `Q` on `m` inputs over `max`, `+` and the constant `0` with
`|P| + |Q| ≤ 8 (3 m s + m L + 9 m² + 4 m + 4 L + 1)`, `L = ⌈log₂(k + 1)⌉` (Lean `Nat.size k`),
such that at every `w ∈ ℝ^m`, `P` outputs a single value `p`, `Q` outputs a single value `q`, and
`h_M(w) = max_B w(B) = p - q`.

*Proof.*
1. Phase 1's Theorem A gives a signed tropical circuit `C` with
   `|C| ≤ 3 m s + m L + 9 m² + 4 m + 4 L + 1` and `C(w) = [h_M(w)]` at every `w`.
2. Corollary 1.9 over `ℝ` gives `P` and `Q` with `|P| + |Q| ≤ 8 |C|`, as many outputs as `C`, and
   `C(w) = P(w) - Q(w)` componentwise.
3. `C` has one output (Step 1), so `P(w) = [p]`, `Q(w) = [q]`, and `[h_M(w)] = [p - q]`.


## 2. Correspondence table

| Paper | Lean names | Module | Status |
|:--|:--|:--|:--|
| `prop:normal-form`, the normal form, `σ ∈ {max, min}` | `normal_form` | `NormalForm.lean` | proved, `\|A\| + \|B\| ≤ 8 s` |
| `prop:normal-form`, proof: pairs `(g⁺, g⁻)` shared by all successors | `normal_form_shared`, `eval_eq_sub`, `posCircuit`, `negCircuit`, `pairGad`, `size_posCircuit`, `size_posCircuit_le` | `NormalForm.lean` | proved, one gate list of at most `4 s` gates |
| `prop:normal-form` for signed tropical circuits (`σ = max`) | `normal_form_stOp` | `NormalForm.lean` | proved, `8 s` |
| `prop:normal-form`, interchange of the bases | `interchange`, `swapCircuit`, `eval_swapCircuit`, `size_swapCircuit_le`, `stOp_to_min`, `min_to_stOp` | `NormalForm.lean` | proved, `3 s` |
| `prop:normal-form`, proof of `eq:normal-form`: to the `min` basis, then normalize | `normal_form_stOp_min` | `NormalForm.lean` | proved for every signed tropical circuit, `24 s` |
| `eq:normal-form`, `Assign_n = A_n - B_n`, `\|A_n\| + \|B_n\| = O(n⁸)` | none | | not done: rests on `thm:main` |
| none (Phase 1, Theorem A) | `theoremA_normal_form` | `NormalForm.lean` | proved, `8 (3 m s + m L + 9 m² + 4 m + 4 L + 1)` |
| none (bridges) | `relabel`, `eval_relabel`, `ofSTOp`, `toSTOp`, `toTropOp`, `eval_relabel_ofSTOp`, `eval_relabel_toSTOp`, `eval_relabel_toTropOp` | `NormalForm.lean` | proved |


## 3. Differences from the paper

1. **Carrier.**  The paper's circuits take real inputs.  The Lean statements hold in every
   linearly ordered additive commutative group `R`, and the interchange in every additive
   commutative group with a linear order, without compatibility of order and addition.  `ℝ` is
   an instance.  No change to the paper is needed.
2. **Explicit constants.**  The paper writes `|A| + |B| = O(s)`.  The Lean statements give
   `|A| + |B| ≤ 8 s` as two circuits, one shared gate list of at most `4 s` gates (exactly
   `4·#σ + 2·#(+) + 2·#(-)`), `3 s` for the interchange (exactly `3·#σ + #(+) + #(-)`), and
   `24 s` for the route of `eq:normal-form`.  Optional wording for the paper, after
   "`|A|+|B|=O(s)`": "; more precisely, $A$ and $B$ share one gate list of at most $4s$ gates,
   so $|A|+|B|\le 8s$", and in the proof "Each gate contributes at most four new gates".
3. **Several outputs.**  The Lean statements apply to circuits with any number `N` of outputs,
   componentwise; the paper's statement concerns one output.  No change needed.
4. **Model conventions.**  Phase 1's circuits read a wire that is not yet built as the constant
   (`PHASE1.md`, Definition 1.3).  For gate sets with the constant source `0`, as here, this is
   the paper's DAG model.  The circuits `A` and `B` built here refer only to wires already
   built.  No change needed.
5. **Gate sets.**  The paper's two bases `σ, +, -` and the two bases `σ, +` are, in Lean, one
   gate type each (`SignedOp`, `PlusOp`) whose gate `sel` is read as `σ`.  Phase 1's signed
   tropical gates `STOp` are `SignedOp` read at `σ = max`, up to renaming
   (`eval_relabel_ofSTOp`, `eval_relabel_toSTOp`).  Not a matter for the paper.
6. **`eq:normal-form`.**  The Lean development proves the reduction, not the display: every
   signed tropical circuit of size `s` is `A - B` with `A`, `B` over `min`, `+`, `0` and
   `|A| + |B| ≤ 24 s` (`normal_form_stOp_min`).  With the circuit of `thm:main` this gives
   `eq:normal-form` with `|A_n| + |B_n| ≤ 24 s_n`, where `s_n = O(n⁸)` is its size.  Optional
   wording for the proof of `eq:normal-form`: "convert the circuit of Theorem~\ref{thm:main} to
   the $\min$ basis at a factor of three and then normalize, at a factor of eight for the two
   circuits".


## 4. Module line counts

| Module | Lines | Content |
|:--|:--|:--|
| `SignedTropical/NormalForm.lean` | 529 | gate sets, renaming, the pair construction, `prop:normal-form`, interchange, Theorem A in normal form |


## 5. Not done

* **`eq:normal-form` for `Assign_n`** (`A_n`, `B_n` over `min`, `+`, `0` with
  `|A_n| + |B_n| = O(n⁸)`): it rests on Theorem `thm:main` of `signed_assignment.tex`, the
  `O(n⁸)` signed tropical circuit for `Assign_n`, which is not formalized.  Corollary 1.13
  (`normal_form_stOp_min`) is the remaining step: applied to that circuit, it gives the display
  with `|A_n| + |B_n| ≤ 24 s_n`.  For the same reason Corollary `cor:jss`(1) is not formalized;
  its basis conversion is Corollary 1.12 (`stOp_to_min`).
* **The maxout reading** after the proposition (a maxout network with `O(s)` units and weights
  in `{-1, 0, 1}`): outside the proposition; the development has no network model.
* **One subtraction at the output** (the sentence after Corollary `cor:jss`): it follows from
  Proposition 1.7 by appending one subtraction gate per output to the shared gate list, and is
  not stated as a separate theorem.
* **The attribution** to Jukna, Seiwert and Sergeev: a citation, nothing to formalize.
