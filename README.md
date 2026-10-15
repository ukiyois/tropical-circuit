# tropical-circuit

[English](#english) | [中文](#中文)

## English

Exact circuits over `max`, `+` and `-` for combinatorial optimization, with a Lean 4
formalization.

A *signed tropical circuit* computes with `max`, `+` and `-` over the reals and the
constant `0`. Its output is a continuous function of the input, so it cannot compare
two weights and branch on the answer. The papers in this repository build exact
circuits of polynomial size, correct at every real weight vector, for problems that
are usually solved by comparing and branching.

### Papers

| Source | Title | Main results |
|---|---|---|
| `paper/signed_assignment.tex` | Polynomial-Size Signed Tropical Circuits for the Assignment Problem | The minimum weight of a perfect matching, with an optimal dual pair, in `O(n^8)` gates (dense case); circuits without subtraction need `2^Ω(n)` gates |
| `paper/greedy_intersection.tex` | Greedy and Matroid Intersection without Branching | Weighted bases of a matroid in `3ms + O(m^2)` gates from a Boolean rank circuit of size `s`, and a converse of size `O(S^2)`; rainbow bases in `O(k^3 m^5 (s+m))`; weighted matroid intersection in `O(m^8 (s_1+s_2+m))` |

Neither paper depends on the other: `greedy_intersection.tex` proves the compiler it
uses. To build one:

```
cd paper
pdflatex greedy_intersection
bibtex greedy_intersection
pdflatex greedy_intersection
pdflatex greedy_intersection
```

`signed_assignment.tex` builds the same way and uses `references.bib` and the figures
in `paper/fig/`.

### Lean formalization

`daishu-formal/` is a Lake package (library `SignedTropical`) on Lean 4 `v4.32.0`
and Mathlib `v4.32.0`. It proves:

- the results of `greedy_intersection.tex`, Sections 2 to 5, with the constants
  stated there;
- Section 3 of `signed_assignment.tex` (the compiler of Boolean observers on a
  threshold filtration) and its Proposition `prop:normal-form`.

The development contains no `sorry`. Every main theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. Three things are not formalized:
- uniformity of the circuit families;
- the complexity classes in Proposition `prop:nphard` (the reduction itself is
  formalized);
- the example of Proposition `prop:ladder`, which is checked by computation.

| File | Contents |
|---|---|
| `PHASE1.md` | Index and natural-language proofs for weighted bases and the compiler |
| `PHASE2.md` | Index for rainbow bases and matroid intersection |
| `notes/` | One companion per module, stating each result as the Lean statement reads |
| `BLUEPRINT.md` | Design notes |

To build:

```
cd daishu-formal
lake exe cache get
lake build
```

### Computational checks

`experiments/` holds Python 3 scripts that use only the standard library and exact
rational arithmetic. They run the checks reported in the papers' verification
sections and in the research notes. `experiments/referee_phase2a/` is an independent
second implementation of the rainbow-base construction, and `experiments/*_logs/` holds
the logs.

### Research notes

`docs/` holds dated research notes: the proofs, data and refuted conjectures behind
the papers, and audits of the assignment paper.

### License

MIT, see `LICENSE`.

## 中文

用 `max`、`+`、`-` 为组合优化问题构造精确电路，并附 Lean 4 形式化。

*带符号热带电路*（signed tropical circuit）在实数上只用 `max`、`+`、`-` 和常数 `0`
计算。它的输出是输入的连续函数，因此无法比较两个权重再按结果分支。本仓库的论文为通常
靠比较和分支求解的问题构造多项式规模的精确电路，在每个实数权重向量上都给出正确值。

### 论文

| 源文件 | 标题 | 主要结果 |
|---|---|---|
| `paper/signed_assignment.tex` | Polynomial-Size Signed Tropical Circuits for the Assignment Problem | 完美匹配的最小权重连同一组最优对偶解，`O(n^8)` 个门（稠密情形）；不允许减法的电路需要 `2^Ω(n)` 个门 |
| `paper/greedy_intersection.tex` | Greedy and Matroid Intersection without Branching | 由规模为 `s` 的布尔秩电路得到拟阵加权基的 `3ms + O(m^2)` 门电路，反方向得到规模 `O(S^2)` 的布尔秩电路；彩虹基（rainbow base）`O(k^3 m^5 (s+m))`；加权拟阵交 `O(m^8 (s_1+s_2+m))` |

两篇论文互不依赖：`greedy_intersection.tex` 自行证明了它所用的编译器。编译方法：

```
cd paper
pdflatex greedy_intersection
bibtex greedy_intersection
pdflatex greedy_intersection
pdflatex greedy_intersection
```

`signed_assignment.tex` 的编译方式相同，需要 `references.bib` 和 `paper/fig/` 中的图。

### Lean 形式化

`daishu-formal/` 是一个 Lake 包（库名 `SignedTropical`），基于 Lean 4 `v4.32.0` 和
Mathlib `v4.32.0`。它证明了：

- `greedy_intersection.tex` 第 2 至 5 节的结果，常数与文中一致；
- `signed_assignment.tex` 第 3 节（阈值滤链上布尔观测的编译器）及其 Proposition
  `prop:normal-form`。

整个开发不含 `sorry`，每个主定理只依赖公理 `propext`、`Classical.choice` 和
`Quot.sound`。以下三项未形式化：
- 电路族的一致性（uniformity）；
- Proposition `prop:nphard` 中的复杂性类（归约本身已形式化）；
- Proposition `prop:ladder` 中的例子，由计算验证。

| 文件 | 内容 |
|---|---|
| `PHASE1.md` | 加权基与编译器部分的索引和自然语言证明 |
| `PHASE2.md` | 彩虹基与拟阵交部分的索引 |
| `notes/` | 每个模块一份说明，按 Lean 陈述逐条写出结果 |
| `BLUEPRINT.md` | 设计笔记 |

编译：

```
cd daishu-formal
lake exe cache get
lake build
```

### 计算验证

`experiments/` 中是只用标准库、采用精确有理数运算的 Python 3 脚本，运行论文验证部分
和研究笔记中报告的检查。`experiments/referee_phase2a/` 是彩虹基构造的独立第二实现，
`experiments/*_logs/` 存放日志。

### 研究笔记

`docs/` 中是带日期的研究笔记：论文背后的证明、数据和被推翻的猜想，以及对指派论文的
审读记录。

### 许可证

MIT，见 `LICENSE`。
