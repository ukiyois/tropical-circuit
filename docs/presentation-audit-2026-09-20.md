# Presentation audit — `paper/signed_assignment.tex`, 28 pages (2026-09-20)

Three issues raised: missing figures, prose-shaped proofs, bloated passages.
Analysis only; nothing in the manuscript was changed.

Block sizes, in source lines, for reference:

```
Introduction            268   of which: construction 59, mechanism 37,
                              separation 64, compiler/JSS 25, related work 45
Section 2                85
Section 3               368   preamble 173, monotone 62, reverse 68, bottleneck 65
Section 4               419   update 107, progress 139, termination 64, selectors 89
Section 5               257   quoted 30, what we add 77, power 105, JSS 45
Section 6                42
Section 7               127
Appendix A              127
Appendix B              337
Appendix C               41
```

## 1. Figures

The paper currently has none. Seven places would carry real load, ranked. Each
entry gives what the figure must contain, not how to style it.

### F1. The threshold filtration and the gap decomposition — Section 3, after (8)

**Highest value. This is the paper's central mechanism and it is invisible.**

One panel, a horizontal axis `t`. On it mark `s_0 = 0 <= s_1 <= ... <= s_m`, the
sorted slacks, with the gaps `Delta_k` as the intervals between consecutive
marks. Above the axis, draw the edge set as `m` horizontal bars, bar `e` starting
at `t = D_e`, so that the vertical slice at `t` is exactly `G_t(D)`. Below the
axis, draw the step function `F(G_t)` taking values in `{0,1}`, and shade the
region under it: the shaded area is `C_F(D)`, and it decomposes into rectangles
of width `Delta_k` and height `F(G_k)`.

Mark one place where two sorted values coincide, so `Delta_k = 0`, and annotate
it: *the observable may be wrong here; its rectangle has zero width*. That single
annotation is the whole Lemma 3.4 to 3.5 mechanism.

An optional second panel, shifted slightly, would show a perturbed `D'` and the
band of `t` where the two filtrations differ, illustrating
`|C_F(D) - C_F(D')| <= ||D - D'||_1`.

### F2. The bottleneck transform — Section 4, at Proposition 4.3

**Turns three formulas into one picture.**

Horizontal axis `t` again. Mark `lambda_i` for two or three left vertices, `mu_j`
for two right vertices, and `tau` to the right of all of them. Draw
`a_i = (tau - lambda_i)_+` and `c_j = (tau - mu_j)_+` as bracketed lengths.
Include one vertex with `lambda_i > tau` whose bracket is empty, so the clamp
`(.)_+` is visible rather than notational.

Optionally overlay the guard: shade `t >= tau` and label it *guard off*.

### F3. The progress step — Section 4.2, inside Theorem 4.6

**The hardest proof in the paper is entirely verbal.**

A bipartite picture. Left column `L`, right column `R`. Draw `S_0` and `T_0` as
enclosed regions, the matching `M` as horizontal double lines between `T_0` and
`S_0`, one free left vertex at the top of `S_0`, and an alternating path from it.
Then draw the boundary edge `ij` from `i in S_0` to `j notin T_0`, dashed, with
the label `delta`. Show both branches of Step 6 as two variants of the same
picture: `j` free, giving an augmenting path, and `j` matched to `i' notin S_0`,
which extends `S_0` by one vertex.

The reader needs to see that the only way out of `S_0 u T_0` is rightward, which
is Step 4 and is currently three sentences of case analysis.

### F4. The tightness family — Section 4.3, at Remark 4.11

**One picture replaces a whole paragraph.**

The chain `L_0 - R_1 - L_1 - R_2 - ... - L_r - R_0`. Draw the zero edges
`L_i R_i` horizontally as solid lines with label `0`, the chain edges
`e_i = L_{i-1} R_i` diagonally as dashed lines with labels `1, 2, ..., r`, and
`e_{r+1} = L_r R_0` closing the cycle with label `r+1`. Annotate one update as
*every dashed label drops by one*.

### F5. The gate-set diamond — Section 1, replacing equation (6)

**Currently an inline array of arrows; it reads as a typographic accident.**

Three boxes. Bottom: pure tropical, `min, +, 0`. Upper left: positive-scalar,
with the annotation `sqrt(2) x` in one gate. Upper right: signed with unit
coefficients, with the annotation *integer slopes only*. Two upward inclusion
arrows from the bottom box, and a crossed-out horizontal arrow between the two
upper boxes to mark incomparability. Put the assignment verdict inside each box:
`2^{Omega(n)}`, `2^{Omega(n)}`, `O(n^8)`.

### F6. The complexity landscape — Section 3.2, after Corollary 3.13

**The paper's structural summary, currently only in words.**

A two-by-two diagram:

```
   general Boolean  <--- polynomially equivalent --->  signed tropical on Lovasz extensions
          |                                                      |
      contains                                               contains
          |                                                      |
   monotone Boolean <---------- equal ----------->  lattice (min,max) circuits
```

with the bottom equality labelled `Theorem 3.10` and the top equivalence
labelled `Theorem 3.12`. Add one marginal note: *lower bounds are known on the
bottom row and open on the top*, which is the barrier in one line.

### F7. The fixed-cardinality reduction — Section 7

**The counting argument is much clearer drawn than written.**

Four blocks: `L`, `R`, `L'`, `R'`, with `|L'| = |R'| = n - k`. Draw the three
allowed edge blocks, `L x R` at the original costs, `L x R'` and `L' x R` at cost
`0`, and cross out `L' x R'`. Annotate the forced counts: all of `L'` goes into
`R`, all of `R'` receives from `L`, hence exactly `k` original edges remain.

### Not worth a figure

The braid-cone witness in Remark 3.14 lives in four dimensions; a schematic would
either mislead or need its own explanation. The schedule staircase adds nothing
beyond equation (10). Example 4.8 is better as a small table than a figure, see
section 3 below.

## 2. Proofs that are shaped like prose

The house style is step-structured, and the steps exist. What is missing inside
the steps is the chain: most steps are a sentence of the form "since A, B, hence
C", where a displayed implication chain would be shorter, checkable line by line,
and harder to hide an error in. Four proofs account for most of it.

### P1. Theorem 4.6, the progress dichotomy — 139 lines, the worst offender

Steps 0 to 6 are seven prose paragraphs. Step 0 is typical:

> Let `k` be active. Then `G^0(D) subset G_k` gives `nu(G_k) >= r`, and minimality
> of `tau` gives `nu(G_k) <= r`, so `nu(G_k) = r`, the guards are on, and `M` is a
> maximum matching of `G_k`. For `i in S_0`, Lemma A.1(4) supplies a maximum
> matching of `G^0(D)` leaving `i` free; it has `r = nu(G_k)` edges, hence is
> maximum in `G_k` as well, so `i in S(G_k)`.

The same content as a chain:

```
k active
    G^0(D) ⊆ G_k                          ⟹  ν(G_k) ≥ r
    minimality of τ                       ⟹  ν(G_k) ≤ r
                                          ⟹  ν(G_k) = r,  M maximum in G_k
i ∈ S_0
    Lemma A.1(4)                          ⟹  ∃ M' maximum in G^0(D), i free
    |M'| = r = ν(G_k)                     ⟹  M' maximum in G_k
                                          ⟹  i ∈ S(G_k)
                                          ⟹  S_0 ⊆ S(G_k),  T_0 ⊆ T(G_k)
```

Every step of the theorem admits this treatment. Step 1 is a two-line
biconditional, Step 4 is a three-case exclusion that should be a displayed list,
Step 6 is two branches that should be two displayed cases. My estimate is that
the proof shrinks from 139 lines to about 90 while becoming easier to check.

### P2. Proposition A.2, the Boolean observer — mixed

The reachability recurrences are already displayed. The parent assignment is not:

> A right vertex `j` first discovered at half-level `t+1` takes as parent the
> least `i`, in the fixed edge order, with `g_ij and not x_ij and z^(t)_i`; a left
> vertex `i` first discovered at half-level `t+1` takes as parent its unique
> `x`-partner.

This should be two displayed definitions, `parent(j)` and `parent(i)`, next to
the priority encoder `p_u = c_u and (and_{u'<u} not c_{u'})` which is already a
formula. The gate counts should be a four-row table rather than a sentence each:
reachability `O(nm)`, first-discovery `O(nm)`, selection `O(m)` per step,
complement `O(m)`, total per round `O(nm)`, `n` rounds, `O(n^2 m)`.

### P3. Proposition 4.14(1), the primal selector — a case table wants to exist

The three cost comparisons at `W^0 + sV` are currently a sentence. They are a
table:

```
            cost at W^0 + sV     cost at W^0 - sV
M_1              -2s                  +2s
M_0              +2s                  -2s
any other      >= 1 - 2s            >= 1 - 2s
```

with the single line `0 < s < 1/4` above it. Three rows replace four lines of
prose and make the argument inspectable.

### P4. Lemma A.1, the canonical cover — parts (2) and (3)

Part (3) is a two-line computation dressed as a paragraph:

```
C = (L \ S(G)) ∪ T(G)
edge ij,  i ∈ S(G)      ⟹  j ∈ N_G(S(G)) = T(G)      covered
edge ij,  i ∉ S(G)                                    covered
|C| = n - |S(G)| + |T(G)| = ν(G)                      by (2)
every vertex cover has ≥ ν(G) vertices                 minimum
```

Part (4)'s converse direction, the symmetric-difference path argument, is the one
place in that lemma where prose is the right medium; it should stay.

### Proofs that are already in the right shape

`lem:pin-full` in Appendix B, the five probes, is a numbered chain with displays
and needs no change. `thm:pure-full` and `thm:scalar-full` are step-structured
with the algebra displayed. `prop:normal-form` is three displayed identities.
`thm:lattice` is one displayed induction. These are the template the four above
should be brought to.

### One suggested global convention

Introduce a house macro for the implication chain, so that the steps line up
vertically and the justification sits in the right margin. Something of the form

```
\begin{steps}
  \step{G^0(D) ⊆ G_k}{ν(G_k) ≥ r}
  \step{minimality of τ}{ν(G_k) ≤ r}
\end{steps}
```

rendered as a two-column aligned block. Doing this once makes the four rewrites
mechanical and keeps the style uniform for a referee.

## 3. Passages that are too heavy

### V1. The branching obstruction is explained twice, at full length

Section 1, "The mechanism", opens with four sentences on the Hungarian method
reading the slack matrix and branching. Section 2, "Why polynomial time is not
enough", is ten lines saying the same thing with the perturbation argument added.

They should not both be full. The introduction needs two sentences; Section 2 is
the right place for the perturbation argument and the finite-precision remark.
Saving about 8 lines and, more importantly, removing the sense of being told the
same thing twice within three pages.

### V2. Equation (7), the two-mechanisms display, is both redundant and broken

```
\underbrace{\Delta_k b(G_k)}_{legal continuous gates}  together with
\underbrace{rank rises or |S| grows}_{fixed number of rounds}
```

It restates the two preceding paragraphs in a display that carries no new
content. **It also uses `b(G_k)`, which no longer exists**: the guards were
renamed `F^L_{r,i}` and `F^R_{r,j}` when Section 3 was rewritten. This is a live
defect, not only a stylistic one. Delete the display.

### V3. The introduction is 268 lines, about four printed pages

"The separation" alone is 64 lines and overlaps with "A compiler, and three
questions it closes" on the separation narrative, and both are followed by a
45-line related-work block that states the separation a third time. The budget
we agreed was two pages for Section 1. Suggested cuts:

- fold the diamond discussion into F5 and one sentence;
- let "The separation" state Theorem 1.3 and 1.4 and stop;
- let "A compiler, and three questions" carry the compiler statement and the
  three answers, with no restatement of the positive-scalar bound;
- related work keeps its three paragraphs.

Target about 180 lines, saving roughly a page.

### V4. The depth mechanism is written out twice

Remark 3.16 in Section 3.3 and the "Depth" paragraph in Section 7 both explain
that the sorting network is `O(log^2 m)` deep, the `m` gaps are independent, and
the gap sum is a balanced tree. The two results differ, `Lambda_n` against the
assignment circuit, so both statements should stay, but the shared mechanism
belongs in Section 3.3 only, with Section 7 reduced to the count
`O(n^2 polylog n)` and the caveat about the Boolean model. Saving about 8 lines.

### V5. Section 3.2's closing paragraph restates its own corollary

> The barrier comes from the compiler, not from the simulation: it is the upper
> bound in (17) that makes signed lower bounds expensive. It applies only to
> functions of the form `C_F`, and Remark 3.14 shows that the assignment value
> function is not one of them.

The first clause is already the content of Corollary 3.13, and the second is the
first sentence of Remark 3.14. One sentence suffices: *the barrier applies only
to compiled integrals, and Remark 3.14 shows the assignment value function is not
one.*

### V6. Section 5, "Where the power sits", is 105 lines

It now carries the three-level display, the normal form with its proof, the
attribution paragraph, the maxout translation, and the monotone-against-general
corollary. The normal form proof is short and should stay; the attribution
paragraph and the maxout paragraph can be halved. Saving about 15 lines.

### V7. Section 6 and Appendix C overlap

The four verification layers are described in Section 6 and tabulated again in
Appendix C with the same numbers, and the three controls appear in both. Section
6 should keep the four layers and the trust argument; Appendix C should keep the
table and the cone-certificate detail and drop the repeated controls. Saving
about 10 lines.

## 4. Suggested order of work

1. V2 first: it is a live notation defect, not a matter of taste.
2. F1, F2, F3 as the figures that change how the paper reads; F4 to F7 after.
3. P1, then P3 and P4, which are short; P2 last.
4. V1, V3, V4 for length; V5, V6, V7 are polish.

Net effect if all of it is done: the introduction loses about a page, Section 4.2
loses about a third of its proof while gaining a figure, and the paper stays near
28 pages with three to seven figures added.

## 5. Applied (2026-09-20), and the package

31 pages, five figures. Builds clean: exit 0, zero overfull boxes, zero
undefined references, zero undefined citations, zero multiply-defined labels,
zero em-dashes, zero pointer words, zero proof shortcuts (`similarly`,
`analogous`, `verbatim`, `clearly` all at zero). 24 cited keys, all resolved.

Layout: 1 (p.1), 2 (p.5), 3 (p.6), 4 (p.11), 5 (p.18), 6 (p.21), 7 (p.22),
references (p.23), A (p.25), B (p.26), C (p.30).

### 5.1 Figures, five of the seven proposed

| File | Where | Label |
|---|---|---|
| `fig/5.png` | Section 1, replacing the ASCII diamond | `fig:diamond` |
| `fig/1.png` | Section 3, after `prop:two-readings` | `fig:filtration` |
| `fig/2.png` | Section 4.1, at `prop:bottleneck` | `fig:bottleneck` |
| `fig/3.png` | Section 4.2, facing `thm:progress` | `fig:progress` |
| `fig/4.png` | Section 4.3, at `rem:tight` | `fig:tight` |

Two drawing details are absorbed by the captions rather than redrawn. In
`fig/1.png` panel (3) the step heights lie strictly between `0` and `1` while
`F` is `{0,1}`-valued; the caption says the heights are schematic and notes that
the same decomposition covers the integer-valued observables of
`cor:integer-observable`. In `fig/3.png` the zero-slack graph is written `G_0`
where the text writes `G^0`; the caption records the substitution.

`fig:diamond` also carries a caption line stating that the two horizontal arrows
mark incomparability and are not inclusions, since they are drawn as a pair of
opposing arrows.

### 5.2 Proofs formalized

**P1, `thm:progress`.** The seven steps are now implication chains in `align*`
rather than paragraphs. Step 4 in particular is a two-row exclusion table for
the two possible first departures from `S_0 u T_0`, which was the place a reader
had to reconstruct a case analysis from prose.

**P2, `prop:observer`.** The parent assignment is two displayed implications
with the priority encoder named `pi`, and the gate count is a six-row table
ending at `O(n^2 m)`.

**P3, `prop:selectors`(1).** The three cost comparisons at `W^0 +- sV` are a
three-row table.

**P4, `lem:canonical`(3).** The vertex-cover argument is a three-line chain with
the appeal to part (2) marked over the equality sign. Part (4)'s
symmetric-difference argument stays in prose, which is the right medium for it.

### 5.3 Verbosity

- **V1** The branching obstruction was stated at full length in Section 1 and
  again in Section 2. Section 1 now states it in one sentence and points to
  Section 2, which keeps the perturbation and finite-precision argument.
- **V2** Equation (7), the two-mechanisms display, is deleted. It restated the
  two preceding paragraphs and used `b(G_k)`, a symbol that stopped existing when
  Section 3 was rewritten. This was a live defect.
- **V3** The introduction's separation block loses the duplicated verdict
  sentence, the "does not rebuild them" aside, and four lines after
  `thm:robust`.
- **V4** The depth mechanism was written out in Section 3.3 and again in
  Section 7. Section 7 now cites `rem:depth-separation` and keeps only the count.
- **V5** Section 3.2's closing paragraph restated its own corollary; reduced to
  one sentence.
- **V6** The attribution and maxout paragraphs in Section 5 are halved.
- **V7** Section 6's three controls are now named in one sentence with the detail
  left in Appendix C, where the table already had it.

### 5.4 Metadata

Author set to Shuhuan Wang, `ukiyo7@gmail.com`. The `hertrich-sering25` entry is
corrected to Mathematical Programming 210(1):377--406, 2025, confirmed against
the published version.

### 5.5 Package

`paper/signed-assignment-arxiv.tar.gz`, 5.8 MB: `signed_assignment.tex`,
`references.bib`, `signed_assignment.bbl`, `fig/1.png` to `fig/5.png`. Verified
by two `pdflatex` passes in a clean directory with no `bibtex` run and no
warnings. Well inside the arXiv limit; the five PNGs are `1448x1086` and account
for 5.7 MB of it, so they could be recompressed if a smaller upload is wanted,
with no change to the source.

Remaining checklist items: an acknowledgements line if wanted, and the
verification repository URL once it is public.
