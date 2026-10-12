# daishu

Proof-oriented framework for extension-robust interface complexity.  The
active result is a four-layer argument:

$$
\text{visible relation}
\longrightarrow
\text{semantic rectangle branchwidth}
\longrightarrow
\text{pure tropical DAG lower bound}
\longrightarrow
\text{right-language tree upper bound}.
$$

For a binary linear code `C`, the semantic parameter is exactly

$$
\operatorname{rbw}(\mathcal C)=\operatorname{bw}(\mathcal C)-1,
$$

and every exact existential extension `F` with `pi_X(F)=C` satisfies

$$
\operatorname{TropSize}(\Phi_F)
\ge 2^{\operatorname{bw}(\mathcal C)-1}
$$

in the stated pure `min/+` models.  The sparse nonnegative binary ILP is a
parameter-preserving host for this abstract theorem.

## Source of Truth

- `paper/extension_invariance.tex`: independent four-layer proof note;
  semantic rectangle branchwidth, pure tropical transfer, and right-language
  tree upper bounds.
- `docs/mainline.md`: current theorem statement, candidate upper bound, sparse
  ILP host, and model boundary.
- `docs/submission.md`: exact Lean theorem scope and verification commands for
  a submission; it records the remaining width-definition boundary explicitly.
- `docs/novelty-audit.md`: literature record and overlap audit.
- `paper/references.bib`: persistent bibliography for the active line.

The former `main.tex`, Band/carry manuscript, exploratory theory notes, and
archived benchmark material were removed to prevent the old route from being
mistaken for the current result.

## Scope

The current transfer covers arbitrary finite visible alphabets, arbitrary DAG
sharing, arbitrary exact existential auxiliaries (including heterogeneous finite
hidden alphabets in the projection argument), finite tropical constants, and
full-real or finite-constant nonnegative pure `min/+` circuits.  It does not cover internal subtraction,
`min/max/+` alternation, division, unrestricted semiring circuits, or arbitrary
unrestricted optimization algorithms.  The function `Phi_F` is the universal
parametric optimal-value map over unary objective weights.

The proof note now includes a general finite-relation upper bound.  For a finite
alphabet `Sigma` with `q=|Sigma|`, if `dbw_q(R)` is the deterministic
right-language interface branchwidth, then

$$
q^{\operatorname{rbw}_q(\mathcal R)}
\le \operatorname{xTrop}_{\Sigma,\mathsf M}(\mathcal R)
\le O(nq+nq^{2\operatorname{dbw}_q(\mathcal R)}).
$$

For a `q`-ary linear code this collapses to

$$
q^\rho\le \operatorname{xTrop}_{q,\mathsf M}(\mathcal C)
\le O(nq+nq^{2\rho}),
\qquad \rho=\operatorname{bw}_q(\mathcal C)-1.
$$

For fixed `q`, the note derives polynomial and subexponential classifications
from this sandwich.  The upper proof is a right-language dynamic program;
Kashyap's minimal tree-realization theorem is retained as a code-specific
cross-check.  For a supplied width decomposition, the code transition wiring
can be compiled in `q^{O(rho)} poly(n)` finite-field operations.  Arbitrary DAG
sharing is allowed in the lower-bound model.

The distinction is intentional:

$$
\text{gate size}\ne\text{circuit description length}\ne\text{compilation time}.
$$

The general relation upper bound is nonuniform; only the represented-code
specialization has the supplied-decomposition compiler statement.

## Code and Checks

| Path | Role |
|---|---|
| `src/core.py` | Instances, binary expansion, and exact-cover assertions |
| `src/carry_dag.py` | Reference residual/carry implementation retained for the ILP host |
| `src/binary_ideal.py` | Homogeneous binary selector fiber utilities |
| `src/binary_bridge.py` | Binary fiber to carry certificate bridge |
| `src/normalize.py` | General bounds to exact-cover normalization |
| `src/native/carry_dag.cpp` | Native reference solver |
| `tests/run_checks.py` | Core correctness gate |
| `tests/run_boundary_checks.py` | Selector boundary and branchwidth-family checks |
| `tests/run_multipartition_checks.py` | Code cuts, incidence rank, and rectangle checks |
| `tests/run_b8_checks.py` | Exhaustive B8 projection and sparsity sanity checks |
| `tests/run_relation_checks.py` | Finite-alphabet language and q-ary code checks |
| `tests/run_algebraic_interface.py` | LAT/interface checks |
| `tests/run_apery_checks.py` | Narrow one-row Apéry checks |
| `bench/fourti2_check.py` | Optional selector-fiber CAS check |
| `bench/smoke_big.py` | Large-instance smoke test |
| `docs/theorem-dependency.md` | Theorem dependency DAG and convention audit |

The proof note compiles successfully with its bibliography.  The Python
correctness gates, B8 sanity check, multipartition checks, and C++ cross-check
pass.
