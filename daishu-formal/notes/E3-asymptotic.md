# E3: Corollary `cor:count` without external hypotheses

Modules: `SignedTropical/SparsePaving.lean` (namespace `SignedTropical.SparsePaving`) and
`SignedTropical/Asymptotic.lean` (namespace `SignedTropical.Asymptotic`).  Both build with
`lake build` with zero errors and zero warnings.  `#print axioms` of every declaration listed
below reports only `propext`, `Classical.choice` and `Quot.sound`.  No external result enters
as a hypothesis.

Conventions, as in Phase 1 (`Counting.lean`).  A matroid on `m` labeled elements is
`M : Matroid (Fin m)` with `M.E = Set.univ`, and `N(m) = Set.ncard {M : Matroid (Fin m) |
M.E = Set.univ}` is their number.  A signed tropical circuit `C : Circuit STOp m` computes
`h_M` on `{0,1}^m` if `C.eval (stInterp ℝ) 1_T = [maxBasisWeight M 1_T]` for every
`T : Finset (Fin m)`, where `1_T` is the indicator vector of `T`; it computes `h_M` (on `ℝ^m`)
if `C.eval (stInterp ℝ) w = [maxBasisWeight M w]` for every `w : Fin m → ℝ`.  The size of `C`
is its number of gates.  `codeCount m s L = (s+1)(3(m+s+1)²)^s (m+s+1)^L` is the count of
`Counting.lean`, and `⌈log₂(m+1)⌉` is `Nat.size m`.  Division of reals by `0` gives `0`, as in
Lean.  Throughout, `A(m)` is the number of matroids `M` on `Fin m` with ground set `univ` for
which some signed tropical circuit of size less than `2^{m/2}/m²` computes `h_M` on `{0,1}^m`.


## 1. Results and proofs

### 1.1 Sparse paving matroids (`cor:count`, Step 1)

**Definition (`IsSparse r H`).**  A family `H` of subsets of `Fin m` is `r`-sparse if any two
distinct members `X, Y` of `H` satisfy `|X ∩ Y| + 2 ≤ r`, that is, share at most `r - 2`
elements (with `r - 2` read as an integer).

**Lemma (`IsSparse.eq_of_subset_inter`).**  If `H` is `r`-sparse, `X, Y ∈ H`, `W ⊆ X ∩ Y` and
`|W| + 1 = r`, then `X = Y`.

*Proof.*  Step 1, if `X ≠ Y`, then `r - 1 = |W| ≤ |X ∩ Y| ≤ r - 2`, which is impossible.  ∎

**Lemma (`exchangeProperty`).**  If `H` is `r`-sparse, the predicate "`B` is an `r`-subset of
`Fin m` not in `H`" has the base exchange property: for such `X, Y` and `a ∈ X \ Y` there is
`b ∈ Y \ X` such that `X - a + b` is again an `r`-subset not in `H`.

*Proof.*
Step 1, the candidates.  `|X - a| + 1 = r`, and for `b ∉ X` the set `Z_b = X - a + b` has `r`
elements.  It suffices to find `b ∈ Y \ X` with `Z_b ∉ H`.
Step 2, a first candidate.  `Y ⊄ X`, since otherwise `Y = X` (equal sizes) and `a ∈ Y`.  Take
`b ∈ Y \ X`.  If `Z_b ∉ H`, we are done.
Step 3, a second candidate.  Otherwise `Z_b ∈ H`, so `Z_b ≠ Y` (as `Y ∉ H`), and since
`|Z_b| = |Y|`, there is `b' ∈ Y \ Z_b`.  Then `b' ≠ a` (as `a ∉ Y`) and `b' ∉ X - a`, so
`b' ∉ X`.
Step 4.  If `Z_{b'} ∈ H`, the lemma above applied to `Z_b, Z_{b'} ⊇ X - a` gives
`Z_b = Z_{b'}`, so `b ∈ Z_{b'}`; but `b ≠ b'` and `b ∉ X`.  Hence `Z_{b'} ∉ H`.  ∎

**Lemma (`exists_card_eq_notMem`).**  If `0 < r < m` and `H` is `r`-sparse, some `r`-subset of
`Fin m` is not in `H`.

*Proof.*  Step 1, take an `r`-subset `X` (as `r ≤ m`); if `X ∉ H` we are done.  Step 2,
otherwise pick `a ∈ X` (as `r > 0`) and `b ∉ X` (as `r < m`).  `Z = X - a + b` has `r`
elements, and `Z ∉ H` by the first lemma, since `Z ≠ X` and both contain `X - a`.  ∎

**Theorem (`exists_matroid`; construction `matroid`, `matroid_E`, `isBase_matroid_iff`).**
Let `0 < r < m` and let `H` be a family of subsets of `Fin m`, two distinct members of which
share at most `r - 2` elements.  There is a matroid `M` on `Fin m` with ground set `univ` such
that for every `B : Finset (Fin m)`, `B` is a base of `M` if and only if `|B| = r` and
`B ∉ H`.

*Proof.*  Step 1, `matroid r H hH hne` is Mathlib's `Matroid.ofIsBaseOfFinite` on the finite
ground set `univ`, with the base predicate "is the coercion of an `r`-subset not in `H`"; it
is nonempty by `exists_card_eq_notMem` and has the exchange property by `exchangeProperty`.
Step 2, `isBase_matroid_iff` unfolds the base predicate, using that the coercion
`Finset → Set` is injective.  ∎

The definition `matroid` needs only that `H` is `r`-sparse and that some `r`-subset lies
outside `H` (hypothesis `hne`).

**Theorem (`two_pow_card_le_ncard_matroids`).**  Let `0 < r < m` and let `A` be a family of
`r`-subsets of `Fin m`, two distinct members of which share at most `r - 2` elements.  Then
`N(m) ≥ 2^{|A|}`.

*Proof.*
Step 1, the map.  For every family `H`, `H ∩ A` is `r`-sparse (`IsSparse.mono`), so
`f(H) = matroid r (H ∩ A)` is defined (`exists_card_eq_notMem`), with ground set `univ`.
Step 2, injectivity on the subfamilies of `A`.  If `f(H) = f(H')` with `H, H' ⊆ A`, then for
every `X ∈ A`, which has `r` elements, `X ∉ H` if and only if `X` is a base of `f(H) = f(H')`,
if and only if `X ∉ H'`.  So `H` and `H'` have the same members.
Step 3.  The `2^{|A|}` subfamilies of `A` have distinct images among the matroids with ground
set `univ`, a finite set (`finite_matroids` of `Counting.lean`).  ∎

### 1.2 The family of Graham and Sloane (`cor:count`, Step 1)

**Definition (`gsFamily m r c`).**  The `r`-subsets `X` of `Fin m` with
`(∑_{x ∈ X} x) mod m = c`.

**Theorem (`isSparse_gsFamily`).**  For all `m, r, c`, two distinct sets of `gsFamily m r c`
share at most `r - 2` elements.

*Proof.*
Step 1.  Let `X ≠ Y` be in the family with `|X ∩ Y| + 2 > r`.  Since `|X| = |Y| = r` and
`X ≠ Y`, `X ⊄ Y`, so `|X \ Y| ≥ 1`; with `|X \ Y| + |X ∩ Y| = r = |Y \ X| + |X ∩ Y|` this gives
`X \ Y = {a}` and `Y \ X = {b}`.
Step 2.  `∑ X = ∑ (X ∩ Y) + a` and `∑ Y = ∑ (X ∩ Y) + b` are both `≡ c (mod m)`, so
`a ≡ b (mod m)`, and `a = b` since `a, b < m`.
Step 3.  But `a ∉ Y` and `b ∈ Y`.  ∎

**Theorem (`exists_le_card_gsFamily`).**  For `m > 0` and every `r` there is `c < m` with
`|gsFamily m r c| ≥ C(m, r)/m`.

*Proof.*  Step 1, the map `X ↦ (∑ X) mod m` sends the `C(m, r)` subsets of size `r` into
`{0, …, m-1}`, and its fibres are the families `gsFamily m r c`.  Step 2, since
`m · (C(m, r)/m) = C(m, r)`, Mathlib's pigeonhole principle
`Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to` (with a real bound) gives a fibre of
size at least `C(m, r)/m`.  ∎

### 1.3 The number of matroids (`cor:count`, Step 1)

**Lemma (`two_pow_le_succ_mul_choose_half`).**  `2^m ≤ (m+1) C(m, ⌊m/2⌋)`, that is,
`C(m, ⌊m/2⌋) ≥ 2^m/(m+1)`.

*Proof.*  Step 1, `2^m = ∑_{k=0}^{m} C(m, k)` (`Nat.sum_range_choose`).  Step 2, every term is
at most `C(m, ⌊m/2⌋)` (`Nat.choose_le_middle`).  ∎

**Lemma (`ncard_matroids_pos`).**  `N(m) > 0` (the free matroid on `Fin m`).

**Theorem (`two_pow_ceil_choose_le_ncard_matroids`).**  For `0 < r < m`,
`N(m) ≥ 2^{⌈C(m, r)/m⌉}`.

*Proof.*  Step 1, take `c` from `exists_le_card_gsFamily`; as `|gsFamily m r c|` is an integer
at least `C(m, r)/m`, it is at least `⌈C(m, r)/m⌉`.  Step 2, apply
`two_pow_card_le_ncard_matroids` with `isSparse_gsFamily`.  ∎

**Theorem (`two_pow_ceil_le_ncard_matroids`).**  For every `m`,
`N(m) ≥ 2^{⌈C(m, ⌊m/2⌋)/m⌉}`.

*Proof.*
Step 1, `m = 0`.  The bound is `2^{⌈1/0⌉} = 1`, and `N(0) ≥ 1`.
Step 2, `m = 1`.  The bound is `2^1 = 2`; the free and the loopy matroid on `Fin 1` both have
ground set `univ` and are distinct, since `{0}` is independent in the first and not in the
second.
Step 3, `m ≥ 2`.  `r = ⌊m/2⌋` satisfies `0 < r < m`; apply the previous theorem.  ∎

This bound is a natural number, so it is a valid `N` for the hypothesis
`hN : N ≤ Set.ncard {M : Matroid (Fin m) | M.E = Set.univ}` of Phase 1's `corollaryD`.

**Theorem (`rpow_le_ncard_matroids`).**  For every `m`, `N(m) ≥ 2^{2^m/(m(m+1))}`, with a real
exponent.

*Proof.*  Step 1, `2^m/(m(m+1)) ≤ C(m, ⌊m/2⌋)/m` by the lemma (both sides are `0` at `m = 0`).
Step 2, `C(m, ⌊m/2⌋)/m ≤ ⌈C(m, ⌊m/2⌋)/m⌉` and `t ↦ 2^t` is monotone; conclude with the
previous theorem.  ∎

### 1.4 Corollary `cor:count`

**Lemma (`pow_eight_le_two_pow`).**  `m^8 ≤ 2^m` for `m ≥ 64`.

*Proof.*  Step 1, `64^8 = 2^48 ≤ 2^64`.  Step 2, for `n ≥ 64`, `64(n+1) ≤ 65n` and
`65^8 ≤ 2 · 64^8`, so `64^8 (n+1)^8 ≤ 65^8 n^8 ≤ 64^8 · 2n^8`, and
`(n+1)^8 ≤ 2n^8 ≤ 2 · 2^n`.  ∎

**Lemma (`floor_sq_mul_le`).**  `S = ⌊2^{m/2}/m²⌋` satisfies `S² m⁴ ≤ 2^m`.

*Proof.*  Step 1, at `m = 0` the left side is `0`.  Step 2, for `m > 0`, `S ≤ 2^{m/2}/m²`, so
`S² m⁴ = (S m²)² ≤ (2^{m/2})² = 2^m`.  ∎

**Lemma (`codeCount_le`).**  If `m ≥ 128` and `s m⁴ ≤ 55 · 2^m`, then for every `L`,
`codeCount m s L ≤ 2^{m + (2m+2)s + mL}`.

*Proof.*  Step 1, `m⁴ ≥ 110` gives `2s m⁴ ≤ 110 · 2^m ≤ m⁴ 2^m`, so `2s ≤ 2^m`; and
`2(m+1) ≤ m² ≤ m^8 ≤ 2^m`.  Hence `m + 1 + s ≤ 2^m`.  Step 2, `s + 1 ≤ 2^m`,
`3(m+1+s)² ≤ 4 · 2^{2m} = 2^{2m+2}` and `(m+1+s)^L ≤ 2^{mL}`; multiply.  ∎

**Lemma (`exponent_le`).**  If `m ≥ 128`, `2^m ≤ m(m+1)a`, `s m⁴ ≤ 55 · 2^m` and `L ≤ m`, then
`⌊2^m/m³⌋ + m + (2m+2)s + mL ≤ a`.

*Proof.*
Step 1.  `m^5 (m+1)² ≤ m^8 ≤ 2^m` and `m(m+1) + 1 + 110(m+1)² ≤ m³` (as `m ≥ 128`).
Step 2.  Let `E = ⌊2^m/m³⌋`, so `m³ E ≤ 2^m`.  Multiply the left side by `m⁴(m+1)`:
`m⁴(m+1)E ≤ m(m+1) 2^m`, `m⁴(m+1)(2m+2)s = 2(m+1)² · s m⁴ ≤ 110(m+1)² 2^m`, and
`m⁴(m+1)(m + mL) ≤ m^5 (m+1)² ≤ 2^m`.
Step 3.  The sum is at most `(m(m+1) + 1 + 110(m+1)²) 2^m ≤ m³ 2^m ≤ m⁴(m+1) a`; divide by
`m⁴(m+1)`.  ∎

**Lemma (`exists_two_pow_le_ncard_matroids`).**  For `m > 0` there is `a` with
`2^m ≤ m(m+1)a` and `2^a ≤ N(m)`.

*Proof.*  Step 1, `a = ⌈C(m, ⌊m/2⌋)/m⌉` satisfies `2^a ≤ N(m)`
(`two_pow_ceil_le_ncard_matroids`) and `m a ≥ C(m, ⌊m/2⌋)`.  Step 2,
`2^m ≤ (m+1) C(m, ⌊m/2⌋) ≤ m(m+1) a`.  ∎

**Theorem (`corollaryD_explicit`, `cor:count`, explicit form).**  For `m ≥ 128`,
`2^{⌊2^m/m³⌋} · A(m) ≤ N(m)`: at most a fraction `2^{-⌊2^m/m³⌋}` of the matroids on `Fin m`
with ground set `univ` have a signed tropical circuit of size less than `2^{m/2}/m²` that
computes `h_M` on `{0,1}^m`.

*Proof.*
Step 1, circuit sizes.  Let `S = ⌊2^{m/2}/m²⌋`.  A size below `2^{m/2}/m²` is at most `S`, so
the matroids counted by `A(m)` are among those counted in Phase 1's `corollaryD_count` with
bound `S`, and `A(m) ≤ codeCount m (15S² + 40S) ⌈log₂(m+1)⌉` (Theorem B and the counting of
Boolean circuits by codes, as in `Counting.lean`).
Step 2, the count of circuits.  `s = 15S² + 40S ≤ 55S²` (as `S ≤ S²`), so
`s m⁴ ≤ 55 S² m⁴ ≤ 55 · 2^m` by `floor_sq_mul_le`, and `L = ⌈log₂(m+1)⌉ ≤ m`.  By
`codeCount_le`, `A(m) ≤ 2^K` with `K = m + (2m+2)s + mL`.
Step 3, the count of matroids.  With `a` from `exists_two_pow_le_ncard_matroids`,
`exponent_le` gives `⌊2^m/m³⌋ + K ≤ a`, so
`2^{⌊2^m/m³⌋} A(m) ≤ 2^{⌊2^m/m³⌋ + K} ≤ 2^a ≤ N(m)`.  ∎

**Theorem (`corollaryD_tendsto`, `cor:count`).**  The fraction `A(m)/N(m)` of the matroids on
`Fin m` (ground set `univ`) for which some signed tropical circuit of size less than
`2^{m/2}/m²` computes `h_M` on `{0,1}^m` tends to `0` as `m → ∞`.

*Proof.*  Step 1, `A(m)/N(m) ≥ 0`.  Step 2, for `m ≥ 128`, `E = ⌊2^m/m³⌋ ≥ m` (as
`m⁴ ≤ m^8 ≤ 2^m`) and `2^E > E`, so `m A(m) ≤ 2^E A(m) ≤ N(m)` by the explicit form, that is,
`A(m)/N(m) ≤ 1/m` (with `N(m) > 0`).  Step 3, `1/m → 0`; squeeze.  ∎

**Theorem (`corollaryD_tendsto_of_forall`).**  The fraction of the matroids on `Fin m` (ground
set `univ`) for which some signed tropical circuit of size less than `2^{m/2}/m²` computes
`h_M` at every `w ∈ ℝ^m` tends to `0` as `m → ∞`.

*Proof.*  Step 1, such a circuit computes `h_M` on `{0,1}^m`, so the counted matroids are among
those counted by `A(m)`.  Step 2, squeeze between `0` and `A(m)/N(m)`.  ∎

**Theorem (`corollaryD_most`).**  The fraction of the matroids `M` on `Fin m` (ground set
`univ`) such that every signed tropical circuit computing `h_M` on `{0,1}^m` has size at least
`2^{m/2}/m²` tends to `1` as `m → ∞`.

*Proof.*  Step 1, these matroids are exactly the matroids with ground set `univ` not counted by
`A(m)`, since "every circuit computing `h_M` on `{0,1}^m` has size at least `2^{m/2}/m²`" is
the negation of "some circuit of size less than `2^{m/2}/m²` computes `h_M` on `{0,1}^m`".
Step 2, so their number is `N(m) - A(m)` and the fraction is `1 - A(m)/N(m)`, which tends to
`1 - 0 = 1` by `corollaryD_tendsto`.  ∎

**Theorem (`corollaryD_unconditional`).**  For all `m` and `S`, if
`codeCount m (15S² + 40S) ⌈log₂(m+1)⌉ < 2^{⌈C(m, ⌊m/2⌋)/m⌉}`, some matroid `M` on `Fin m`
with ground set `univ` has no signed tropical circuit of size at most `S` that computes `h_M`
on `{0,1}^m`.

*Proof.*  Step 1, Phase 1's `corollaryD` with `N = 2^{⌈C(m, ⌊m/2⌋)/m⌉}` and
`hN = two_pow_ceil_le_ncard_matroids m`.  ∎


## 2. Correspondence

| Paper label | Lean names | Module | Status |
|:--|:--|:--|:--|
| `cor:count` | `corollaryD_tendsto`, `corollaryD_most` | `Asymptotic.lean` | proved, for circuits on `{0,1}^E` (stronger) |
| `cor:count`, circuits on `ℝ^E` | `corollaryD_tendsto_of_forall` | `Asymptotic.lean` | proved |
| `cor:count`, explicit form for `m ≥ 128` | `corollaryD_explicit` | `Asymptotic.lean` | proved (new) |
| `cor:count`, Step 2 | `codeCount_le`, `exponent_le`, `floor_sq_mul_le`, `pow_eight_le_two_pow`, with Phase 1's `corollaryD_count` | `Asymptotic.lean` | proved, explicit constants |
| `cor:count`, Step 1 (number of matroids) | `two_pow_ceil_le_ncard_matroids`, `rpow_le_ncard_matroids`, `exists_two_pow_le_ncard_matroids` | `SparsePaving.lean`, `Asymptotic.lean` | proved, replaces Knuth's bound |
| sparse paving matroids | `IsSparse`, `exchangeProperty`, `matroid`, `isBase_matroid_iff`, `exists_card_eq_notMem`, `exists_matroid` | `SparsePaving.lean` | proved |
| distinct subfamilies, distinct matroids | `two_pow_card_le_ncard_matroids`, `two_pow_ceil_choose_le_ncard_matroids` | `SparsePaving.lean` | proved |
| Graham and Sloane | `gsFamily`, `isSparse_gsFamily`, `exists_le_card_gsFamily` | `SparsePaving.lean` | proved |
| `C(m, ⌊m/2⌋) ≥ 2^m/(m+1)` | `two_pow_le_succ_mul_choose_half` | `SparsePaving.lean` | proved |
| Phase 1 `corollaryD` with `hN` discharged | `corollaryD_unconditional` | `Asymptotic.lean` | proved |


## 3. Differences from the paper

1. **Step 1 of the proof of `cor:count`.**  The paper cites Knuth (1974) for at least
   `2^{2^{m - (3/2)log₂ m - O(1)}}` matroids.  The formalization proves the weaker bound
   `2^{⌈C(m,⌊m/2⌋)/m⌉} ≥ 2^{2^m/(m(m+1))}` from sparse paving matroids and the family of
   Graham and Sloane.  It suffices, since Step 2 bounds the number of rank functions with
   small circuits by `2^{O(2^m m^{-5/2})}` (in the formalization `2^{O(2^m/m³)}`), which is
   `o(2^m/m²)` in the exponent.  Proposed replacement for Step 1:

   ```latex
   \emph{Step 1.}  Let $m\ge2$, $r=\lfloor m/2\rfloor$ and $E=\{0,\ldots,m-1\}$.  For
   $c\in\{0,\ldots,m-1\}$, the $r$-subsets $X\subseteq E$ with
   $\sum_{x\in X}x\equiv c\pmod m$ pairwise share at most $r-2$ elements: if
   $|X\cap Y|=r-1$, then $X\setminus Y=\{a\}$ and $Y\setminus X=\{b\}$ with
   $a\equiv b\pmod m$, so $a=b$.  These $m$ families partition the $r$-subsets of $E$, so one
   of them, $\mathcal H$, has at least $\binom{m}{r}/m$ members~\cite{graham-sloane80}.  For
   every $H\subseteq\mathcal H$, the $r$-subsets of $E$ not in $H$ are the bases of a matroid
   on $E$.  Some $r$-subset is not in $H$: if $X\in H$, then $X-a+b$ with $a\in X$ and
   $b\notin X$ shares $r-1$ elements with $X$, so it is not in $H$.  For base exchange, let
   $B_1,B_2$ be bases and
   $e\in B_1\setminus B_2$.  If $B_2\setminus B_1=\{f\}$, then $B_1-e+f=B_2$.  Otherwise
   $B_2\setminus B_1$ contains $f_1\ne f_2$, and $B_1-e+f_1$, $B_1-e+f_2$ share the $r-1$
   elements of $B_1-e$, so one of them is not in $H$.  Distinct $H$ give distinct matroids,
   and $\binom{m}{r}\ge2^{m}/(m+1)$, since $\binom{m}{r}$ is the largest of the $m+1$
   binomial coefficients that sum to $2^m$.  So there are at least
   $2^{\lceil\binom{m}{r}/m\rceil}\ge2^{2^{m}/(m(m+1))}$ matroids on $m$ labeled elements,
   and distinct matroids have distinct rank functions.
   ```

   with the bibliography entry (pages to be checked against the journal)

   ```bibtex
   @article{graham-sloane80,
     author  = {Ronald L. Graham and Neil J. A. Sloane},
     title   = {Lower bounds for constant weight codes},
     journal = {IEEE Transactions on Information Theory},
     volume  = {26},
     number  = {1},
     pages   = {37--43},
     year    = {1980}
   }
   ```

   The reference `knuth74` is then no longer needed for this corollary.

2. **Step 2, optional explicit wording.**  The formalized Step 2 has explicit constants and
   gives an explicit form of the corollary.  Optional replacement for Step 2:

   ```latex
   \emph{Step 2.}  A signed circuit of size $S<2^{m/2}/m^{2}$ that computes $h_M$ on
   $\{0,1\}^E$ gives, by Theorem~\ref{thm:B}, a Boolean rank circuit of size
   $s'\le15S^{2}+40S\le55\cdot2^{m}/m^{4}$ with $\lceil\log_2(m+1)\rceil$ outputs.  Every
   function computed by such a circuit is computed by one whose operands are renumbered into
   $m+s'+1$ symbols, so these functions number at most
   $(s'+1)\bigl(3(m+s'+1)^{2}\bigr)^{s'}(m+s'+1)^{\lceil\log_2(m+1)\rceil}$, which for
   $m\ge128$ is at most $2^{m+(2m+2)s'+m^{2}}$ and at most
   $2^{-\lfloor2^{m}/m^{3}\rfloor}$ times the count of Step~1.
   ```

   and, if the explicit form is wanted in the statement, a replacement for the corollary:

   ```latex
   \begin{corollary}[Counting]
   \label{cor:count}
   For every $m\ge128$, all but a fraction $2^{-\lfloor2^{m}/m^{3}\rfloor}$ of the matroids
   $M$ on $m$ labeled elements have no signed tropical circuit of size less than
   $2^{m/2}/m^{2}$ that computes $h_M$, not even on $\{0,1\}^{E}$.
   \end{corollary}
   ```

3. **Stronger hypothesis set.**  The formal statements exclude circuits that compute `h_M`
   only on `{0,1}^E`, which is stronger than the paper's "circuit for `h_M`"; the version for
   circuits on all of `ℝ^E` is `corollaryD_tendsto_of_forall`.  No paper change is needed;
   the optional statement above records it.

4. **Verification section (`sec:checks`).**  The sentence "Its counting statement is the
   finite form of Step 2 of Corollary~\ref{cor:count}, with the number of matroids as a
   hypothesis." is out of date.  Proposed replacement:

   ```latex
   It also proves Corollary~\ref{cor:count}, with the lower bound of Step~1 on the number of
   matroids, for circuits that compute $h_M$ on $\{0,1\}^E$, and in the explicit form: for
   $m\ge128$ at most a fraction $2^{-\lfloor2^{m}/m^{3}\rfloor}$ of the matroids on $m$
   labeled elements have such a circuit of size less than $2^{m/2}/m^{2}$.
   ```

5. **Hypotheses of the sparse paving construction (task wording, not in the paper).**  The
   task stated the construction for `r ≤ m`.  It fails for `r = 0` with `H = {∅}` and for
   `r = m` with `H = {E}`: no `r`-subset is left, so there is no base.  The formal statement
   assumes `0 < r < m` (`exists_matroid`); the definition `matroid` assumes only that some
   `r`-subset lies outside `H`.  The family `H` need not consist of `r`-subsets for the
   construction; that hypothesis is used only for the injectivity in
   `two_pow_card_le_ncard_matroids`.  "Share at most `r - 2` elements" is read over the
   integers (`|X ∩ Y| + 2 ≤ r`); for `r = 1` it allows at most one member.  The replacement
   wording for Step 1 above takes `r = ⌊m/2⌋` with `m ≥ 2`, where `0 < r < m` holds.

6. **Range of `m` in the matroid count.**  The construction needs `m ≥ 2`; the formal bounds
   `two_pow_ceil_le_ncard_matroids` and `rpow_le_ncard_matroids` hold for every `m`, the
   cases `m = 0, 1` being checked directly (bounds `1` and `2`).


## 4. Module line counts

| Module | Lines |
|:--|:--|
| `SignedTropical/SparsePaving.lean` | 257 |
| `SignedTropical/Asymptotic.lean` | 227 |


## 5. Not done, and why

* Knuth's stronger lower bound on the number of matroids is not formalized; the corollary does
  not need it.
* The threshold `m ≥ 128` of the explicit form is not optimized.  It comes from the crude
  estimates `15S² + 40S ≤ 55S²` and `log₂(3(m+s+1)²) ≤ 2m + 2`; sharper estimates would lower
  it, at the cost of longer arithmetic.
* No explicit bound is stated for `m < 128`; the asymptotic statements do not need one.
* The root module `SignedTropical.lean` does not import the two new modules; the coordinator
  adds the imports.
