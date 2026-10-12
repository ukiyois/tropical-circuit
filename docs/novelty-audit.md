# Novelty Audit

This is a working literature record for the current four-layer proof note.  It
is not a final priority or novelty claim.  The active mathematical source is
`paper/extension_invariance.tex`; this file only records overlap, citations,
and unresolved audit obligations.

## Target Statement

The intended central theorem is:

$$
\forall F\subseteq\{0,1\}^{X\mathbin{\dot\cup}Z},
\quad \pi_X(F)=\mathcal C
\quad\Longrightarrow\quad
\operatorname{TropSize}(\Phi_F)
\ge 2^{\operatorname{bw}(\mathcal C)-1}.
$$

The intended scope is arbitrary exact existential auxiliaries and arbitrary
sharing in a pure `min/+` DAG.  The abstract relation theorem uses semantic
rectangle branchwidth; for a linear code the visible parameter is exactly
`bw(C)-1` after taking logarithms in the alphabet base.

The proof note now separates the arbitrary finite-alphabet relation layer from
the finite-field code layer.  For a finite alphabet `Sigma` with `q=|Sigma|`,
the new upper layer uses deterministic
right-language interface width:

$$
q^{\operatorname{rbw}_q(\mathcal R)}
\leq \operatorname{xTrop}_{\Sigma,\mathsf M}(\mathcal R)
\leq O(nq+nq^{2\operatorname{dbw}_q(\mathcal R)}).
$$

For a linear code, `dbw_q(C)=bw_q(C)-1=:rho`, giving

$$
q^\rho\leq \operatorname{xTrop}_{q,\mathsf M}(\mathcal C)
\leq O(nq+nq^{2\rho}).
$$

## Preliminary Conclusion

The audit has not found an existing theorem with all four components together:

1. an arbitrary finite relation or linear code;
2. exact existential extension/projection invariance;
3. a semantic rectangle-branchwidth parameter;
4. a lower bound for an unrestricted pure tropical/min-plus DAG.

The individual ingredients are established or closely related in the
literature.  The defensible novelty candidate is therefore the theorem-level
transfer principle, not the claim that branchwidth, rectangles, tropical
circuits, or code tree realizations are individually new.

## Closest Literature

| Work | Link | What it supplies | Difference from the current target |
|---|---|---|---|
| Jukna, *Tropical Complexity, Sidon Sets, and Dynamic Programming* (2016) | [DOI 10.1137/16M1064738](https://doi.org/10.1137/16m1064738) | General tropical lower-bound machinery; homogeneous/nonhomogeneous optimization and cover-free feasible sets. | Does not state the current arbitrary-extension/code-branchwidth transfer. |
| Jukna, *Tropical Circuit Complexity* (2023) | [Book DOI 10.1007/978-3-031-42354-3](https://doi.org/10.1007/978-3-031-42354-3) | Modern reference for pure dynamic programming and tropical circuits. | Background and possible prior art source; exact theorem overlap still requires chapter-level checking. |
| Jukna, `Rectangle Bounds` (2023) | [Chapter DOI 10.1007/978-3-031-42354-3_3](https://doi.org/10.1007/978-3-031-42354-3_3) | Rectangle-size and communication-style lower-bound methods. | General rectangle machinery, not an extension-robust semantic branchwidth theorem. |
| Jukna, `Extended Tropical Circuits` (2023) | [Chapter DOI 10.1007/978-3-031-42354-3_6](https://doi.org/10.1007/978-3-031-42354-3_6) | Why subtraction, max, and extended tropical operations can change complexity. | Supports the model frontier; it is not the current pure `min/+` transfer. |
| Korhonen, *Lower Bounds on Dynamic Programming for Maximum Weight Independent Set* (ICALP 2021) | [arXiv:2102.06901](https://arxiv.org/abs/2102.06901), [DOI 10.4230/LIPIcs.ICALP.2021.87](https://doi.org/10.4230/LIPIcs.ICALP.2021.87) | Tropical-circuit lower bounds from treewidth for MWIS, including arbitrary circuit sharing. | Problem-specific feasible-set structure; no arbitrary relation, existential extension, or code invariant. |
| Kluk and Nederlof, *Lower Bounds on Pure Dynamic Programming for Connectivity Problems on Graphs of Bounded Path-Width* (2025) | [arXiv:2512.23121](https://arxiv.org/abs/2512.23121) | Very close modern pure-DP result using compatibility matrices and nondeterministic communication. | Connectivity/TSP/DST and pathwidth-specific; it does not give the current relation-level extension theorem. |
| Kashyap, *On Minimal Tree Realizations of Linear Codes* (2009) | [DOI 10.1109/TIT.2009.2023718](https://doi.org/10.1109/TIT.2009.2023718), [arXiv:0711.1383](https://arxiv.org/abs/0711.1383) | Minimal tree realizations and state/constraint complexity of linear codes. | Supplies the tree-realization ingredient, not an arbitrary-DAG lower bound or existential-extension result. |
| Kashyap, *Constraint Complexity of Realizations of Linear Codes on Arbitrary Graphs* (2009) | [DOI 10.1109/TIT.2009.2030492](https://doi.org/10.1109/TIT.2009.2030492) | Code realization complexity on graphs. | Graphical code realizations are not the same as arbitrary pure tropical circuits. |
| Hlineny, *Branch-width, parse trees, and monadic second-order logic for matroids* (2005) | [DOI 10.1016/j.jctb.2005.08.005](https://doi.org/10.1016/j.jctb.2005.08.005) | Branchwidth as a finite-state/parse-tree parameter for matroids. | MSO/tree-automata framework, not tropical circuit lower bounds or rectangle covers. |
| Funk, Mayhew, and Newman, *Tree Automata and Pigeonhole Classes of Matroids* (2022/2023) | [arXiv:1910.04360](https://arxiv.org/abs/1910.04360) | Further finite-state branchwidth machinery for matroid classes. | No pure min-plus circuit or existential projection theorem. |
| Amarilli, Capelli, Monet, and Senellart, *Connecting Knowledge Compilation Classes and Width Parameters* (2019) | [DOI 10.1007/s00224-019-09930-2](https://doi.org/10.1007/s00224-019-09930-2), [arXiv:1811.02944](https://arxiv.org/abs/1811.02944) | Projection/compilation lower bounds from pathwidth/treewidth in Boolean settings. | Restricted Boolean representations; no tropical semantics or arbitrary extension invariant. |
| Gottlob, Lanzinger, and Pichler, *Semantic Width of Conjunctive Queries and Constraint Satisfaction Problems* (2018) | [arXiv:1812.04329](https://arxiv.org/abs/1812.04329) | A formal semantic-width viewpoint under equivalent reformulations. | Different query/CSP setting; motivates avoiding an unqualified use of `semantic width`. |
| Hicks and McMurray, *The Branchwidth of Graphs and Their Cycle Matroids* (2007) | [DOI 10.1016/j.jctb.2006.12.007](https://doi.org/10.1016/j.jctb.2006.12.007) | Graph/cycle-matroid branchwidth relationship. | Graph-theoretic input only. |
| Ajtai, *Recursive Construction for 3-Regular Expanders* (1994) | [DOI 10.1007/BF01302963](https://doi.org/10.1007/BF01302963) | Explicit infinite family of bounded-degree expanders for the sparse host. | Does not concern circuit complexity. |
| Bodlaender et al., *Bandwidth, Expansion, Treewidth, Separators and Universality for Bounded-Degree Graphs* | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0195669809002017?utm_source=chatgpt.com) | Expansion/separator/treewidth background for bounded-degree graphs. | Graph-theoretic input only. |
| Hlineny and Oum, *Finding Branch-Decompositions of Matroids, Hypergraphs, and More* | [arXiv:1711.01381](https://arxiv.org/abs/1711.01381) | Represented-matroid branch-decomposition algorithmic background. | The compiler assumes a decomposition and does not solve the optimization problem. |
| Morgenstern, *Existence and Explicit Constructions of q+1 Regular Ramanujan Graphs for Every Prime Power q* (1994) | [DOI 10.1006/jctb.1994.1054](https://doi.org/10.1006/jctb.1994.1054) | Explicit cubic expander family for the sparse host construction. | Does not concern circuit complexity. |
| Jukna and Seiwert, *Greedy Can Beat Pure Dynamic Programming* (2019) | [DOI 10.1016/j.ipl.2018.10.018](https://doi.org/10.1016/j.ipl.2018.10.018) | Shows that pure DP can be beaten by other algorithmic structure. | Context for why the pure model must be stated precisely; not the current lower bound. |
| Jukna and Seiwert, *Sorting Can Exponentially Speed Up Pure Dynamic Programming* (2020) | [DOI 10.1016/j.ipl.2020.105962](https://doi.org/10.1016/j.ipl.2020.105962) | A model-boundary warning about enhancements to pure DP. | Does not address code branchwidth or existential extensions. |
| Jukna, Seiwert, and Sergeev, *Reciprocal Inputs in Monotone Arithmetic and in Tropical Circuits Are Almost Useless* (2020) | [ResearchGate record](https://www.researchgate.net/publication/346573403_Reciprocal_Inputs_in_Arithmetic_and_Tropical_Circuits?utm_source=chatgpt.com) | Candidate route for allowing reciprocal input literals with a weaker exponential bound. | The simulation statement must be checked from the original report before inclusion. |

## Theorem-Level Position

The sentence to defend is:

> Every exact existential extension of a visible relation preserves its semantic
> rectangle-branchwidth obstruction, and every pure `min/+` DAG computing the
> extension value function must pay exponentially in that visible obstruction.

For linear codes, the second layer identifies the obstruction exactly with
`bw(C)-1`.  The sparse ILP is then a parameter-preserving host, not the source
of the conceptual theorem.

Do not claim:

- that the first branchwidth lower bound for tropical circuits is new;
- that rectangle-size bounds and rectangle-cover complexity are equivalent for
  arbitrary relations;
- that the current lower bound covers `min/max/+`, internal subtraction, or
  unrestricted optimization algorithms;
- that the q-ary upper bound applies without the fixed-alphabet and pure
  `min/+` qualifications;
- that a general relation upper bound is uniform in the relation encoding;
- that compact `log(q)`-bit encodings are covered by the one-hot input model;
- that `semantic width` is an unused term in the CSP literature.

## Upper-Bound Status

The current proof note contains the following finite-alphabet result.  For a
finite alphabet `Sigma` with `q=|Sigma|`:

$$
\operatorname{xTrop}_{\Sigma,\mathsf M}(\mathcal R)
 :=\inf_{\pi_X(F)=\mathcal R}
   \operatorname{TropSize}_{\Sigma,\mathsf M}(\Phi_F^\Sigma),
$$

with the general relation upper bound

$$
 q^{\operatorname{rbw}_q(\mathcal R)}
  \le \operatorname{xTrop}_{\Sigma,\mathsf M}(\mathcal R)
 \le O(nq+nq^{2\operatorname{dbw}_q(\mathcal R)}).
$$

For a linear code, `dbw_q(C)=bw_q(C)-1=:rho`, so

$$
 q^{\rho}
 \le \operatorname{xTrop}_{q,\mathsf M}(\mathcal C)
 \le O(nq+nq^{2\rho}).
$$

The lower-bound transfer and right-language upper construction are both written
in the current proof note.  Kashyap's minimal tree-realization theorem is a
code-specific cross-check.  The formal audit explicitly checks:

1. the right-language composition rule and representative membership test;
2. treatment of one-hot unary costs and finite constants;
3. gate counting, including literal leaves and binary joins;
4. the finite-alphabet formulation and the fixed-`q` qualification of the resulting
   polynomial/subexponential classification.

The linear-code compiler is output-sensitive and assumes a supplied branch
decomposition.  Its finite-field linear-algebra time is separate from the
nonuniform circuit gate-size theorem.

The resulting polynomial and subexponential classifications are claimed only
for fixed `q`, finite constants, and the two explicitly stated pure `min/+`
input models.  A chapter-level comparison with the cited tropical-circuit
literature is still required before making a priority claim.

## Source Log

The original user-provided links are retained here so the audit does not depend
on chat history:

- [Rectangle Bounds, ResearchGate](https://www.researchgate.net/publication/375440519_Rectangle_Bounds?utm_source=chatgpt.com)
- [Tropical Complexity, Sidon Sets, and Dynamic Programming](https://epubs.siam.org/doi/pdf/10.1137/16M1064738?utm_source=chatgpt.com)
- [Tropical Circuit Complexity, Springer](https://link.springer.com/book/10.1007/978-3-031-42354-3?utm_source=chatgpt.com)
- [Korhonen ICALP 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2021.87?utm_source=chatgpt.com)
- [Connectivity lower bounds on bounded path-width](https://www.researchgate.net/publication/399176582_Lower_bounds_on_pure_dynamic_programming_for_connectivity_problems_on_graphs_of_bounded_path-width?utm_source=chatgpt.com)
- [Minimal tree realizations of linear codes](https://citeseerx.ist.psu.edu/document?doi=314ff599f53ffd1bfbb7b83c7c8b8e6a6aaec947&repid=rep1&type=pdf&utm_source=chatgpt.com)
- [Code treewidth background](https://www.researchgate.net/publication/48207695_On_the_treewidth_of_MDS_and_Reed-Muller_codes?utm_source=chatgpt.com)
- [Rectangle size bounds and threshold covers](https://www.researchgate.net/publication/4023766_Rectangle_size_bounds_and_threshold_covers_in_communication_complexity?utm_source=chatgpt.com)
- [Reciprocal inputs](https://www.researchgate.net/publication/346573403_Reciprocal_Inputs_in_Arithmetic_and_Tropical_Circuits?utm_source=chatgpt.com)
- [Extended tropical circuits](https://www.researchgate.net/publication/375427942_Extended_Tropical_Circuits?utm_source=chatgpt.com)
- [Semantic width of CQs and CSPs](https://arxiv.org/abs/1812.04329?utm_source=chatgpt.com)
- [Recursive construction for 3-regular expanders](https://research.ibm.com/publications/recursive-construction-for-3-regular-expanders?utm_source=chatgpt.com)
- [Expansion, treewidth, and separators for bounded-degree graphs](https://www.sciencedirect.com/science/article/pii/S0195669809002017?utm_source=chatgpt.com)
- [Finding branch-decompositions of matroids](https://arxiv.org/abs/1711.01381)
- [Tropical circuits with scalar multiplication gates](https://arxiv.org/abs/2607.11540?utm_source=chatgpt.com)

Crossref and OpenAlex searches also covered `branchwidth tropical circuits`,
`matroid branchwidth circuit complexity`, `rectangle branchwidth monotone
circuits`, `existential extension tropical circuit`, and `dynamic programming
branchwidth rectangle cover`.  Those searches returned no exact general
theorem, but the indexes were incomplete and several results were duplicates
or unrelated uses of the word `circuit`.
