"""Independent referee implementation of the Phase 2a objects (exact arithmetic).

Matroids are given by a rank function, tabulated on all bitmasks (m <= 11).
Nothing here imports the authors' code, so agreement is an independent check.
"""
import itertools
import random
from fractions import Fraction

INF = float("inf")
F0 = Fraction(0)


def popcount(x):
    return bin(x).count("1")


def elems(mask):
    out, e = [], 0
    while mask:
        if mask & 1:
            out.append(e)
        mask >>= 1
        e += 1
    return out


class Mat:
    def __init__(self, m, rankfn, check=False):
        self.m = m
        full = (1 << m) - 1
        self.R = [rankfn(elems(S)) for S in range(1 << m)]
        self.full = full
        self.k = self.R[full]
        self.bases = [S for S in range(1 << m) if popcount(S) == self.k and self.R[S] == self.k]
        self.loops = [e for e in range(m) if self.R[1 << e] == 0]
        self.loopmask = sum(1 << e for e in self.loops)
        if check:
            self.check_axioms()
        self._comp()

    def check_axioms(self):
        R, m = self.R, self.m
        assert R[0] == 0
        for S in range(1 << m):
            for e in range(m):
                if not S >> e & 1:
                    d = R[S | 1 << e] - R[S]
                    assert d in (0, 1), "unit increase"
        # submodularity via local form: R[S+e]+R[S+f] >= R[S+e+f]+R[S]
        for S in range(1 << m):
            for e in range(m):
                if S >> e & 1:
                    continue
                for f in range(e + 1, m):
                    if S >> f & 1:
                        continue
                    assert R[S | 1 << e] + R[S | 1 << f] >= R[S | 1 << e | 1 << f] + R[S], "submodular"

    def rank(self, S):
        return self.R[S]

    def in_cl(self, S, e):
        return self.R[S | (1 << e)] == self.R[S]

    def fund_circuit(self, B, e):
        """C(B, e) for e notin B, as a mask (contains e)."""
        if self.R[1 << e] == 0:
            return 1 << e
        out = 1 << e
        for f in elems(B):
            C = (B & ~(1 << f)) | (1 << e)
            if self.R[C] == self.k:
                out |= 1 << f
        return out

    def _comp(self):
        parent = list(range(self.m))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for B in self.bases:
            for e in range(self.m):
                if B >> e & 1 or self.R[1 << e] == 0:
                    continue
                for f in elems(self.fund_circuit(B, e)):
                    parent[find(e)] = find(f)
        self.comp = [find(e) for e in range(self.m)]


# ------------------------------------------------------------ matroid makers
def uniform(k, m):
    return Mat(m, lambda S: min(len(S), k))


def graphic(n, edges):
    def r(S):
        parent = list(range(n))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        c = 0
        for e in S:
            u, x = edges[e]
            a, b = find(u), find(x)
            if a != b:
                parent[a] = b
                c += 1
        return c
    return Mat(len(edges), r)


def gf2(cols):
    def r(S):
        basis = []
        for e in S:
            x = cols[e]
            for b in basis:
                x = min(x, x ^ b)
            if x:
                basis.append(x)
        return len(basis)
    return Mat(len(cols), r)


def gfp(cols, p):
    """columns are tuples over GF(p)."""
    def r(S):
        rows = [list(cols[e]) for e in S]
        if not rows:
            return 0
        rk = 0
        ncol = len(rows[0])
        for c in range(ncol):
            piv = None
            for i in range(rk, len(rows)):
                if rows[i][c] % p:
                    piv = i
                    break
            if piv is None:
                continue
            rows[rk], rows[piv] = rows[piv], rows[rk]
            inv = pow(rows[rk][c], p - 2, p)
            rows[rk] = [(x * inv) % p for x in rows[rk]]
            for i in range(len(rows)):
                if i != rk and rows[i][c] % p:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
            rk += 1
        return rk
    return Mat(len(cols), r)


def partition_matroid(parts, caps):
    """parts: element -> part id; caps: part -> capacity."""
    def r(S):
        cnt = {}
        for e in S:
            cnt[parts[e]] = cnt.get(parts[e], 0) + 1
        return sum(min(c, caps[p]) for p, c in cnt.items())
    return Mat(len(parts), r)


def sparse_paving(k, m, rng, tries=40):
    """Random sparse paving matroid: U_{k,m} minus a family of k-sets pairwise
    meeting in <= k-2 elements (circuit-hyperplanes)."""
    hyp = []
    allk = list(itertools.combinations(range(m), k))
    rng.shuffle(allk)
    for H in allk[:tries]:
        Hs = set(H)
        if all(len(Hs & set(G)) <= k - 2 for G in hyp):
            hyp.append(H)
    hyps = [set(H) for H in hyp]

    def r(S):
        S = set(S)
        if len(S) < k:
            return len(S)
        if len(S) == k and S in hyps:
            return k - 1
        return k
    return Mat(m, r, check=True)


def direct_sum(M1, M2):
    m1, m2 = M1.m, M2.m

    def r(S):
        a = sum(1 << e for e in S if e < m1)
        b = sum(1 << (e - m1) for e in S if e >= m1)
        return M1.R[a] + M2.R[b]
    return Mat(m1 + m2, r)


def add_loops_coloops(M, nloops, ncoloops):
    m = M.m

    def r(S):
        a = sum(1 << e for e in S if e < m)
        return M.R[a] + sum(1 for e in S if e >= m + nloops)
    return Mat(m + nloops + ncoloops, r)


# ------------------------------------------------------------ weighted basics
def wt(u, B):
    s = F0
    for e in elems(B):
        s = s + u[e]
    return s


def opt_bases(M, u):
    vals = [(wt(u, B), B) for B in M.bases]
    b = min(x for x, _ in vals)
    return frozenset(B for x, B in vals if x == b), b


def beta(M, u):
    return min(wt(u, B) for B in M.bases)


def blocks_of(B, blk):
    return frozenset(blk[e] for e in elems(B))


def nu_of(bases, blk):
    return max(len(blocks_of(B, blk)) for B in bases)


def avoidable(bases, blk, k):
    """blocks missed by some base meeting exactly nu blocks (= some largest
    rainbow independent set misses them)."""
    nu = nu_of(bases, blk)
    A = set()
    for B in bases:
        bl = blocks_of(B, blk)
        if len(bl) == nu:
            A |= set(range(k)) - bl
    return frozenset(A), nu


def rank_from_bases(bases, X):
    return max(popcount(B & X) for B in bases)


def Emask(blk, Q, m):
    return sum(1 << e for e in range(m) if blk[e] in Q)


def theta_local(M, v, B):
    th = F0
    for e in range(M.m):
        if B >> e & 1 or M.R[1 << e] == 0:
            continue
        for f in elems(M.fund_circuit(B, e) & ~(1 << e)):
            th = max(th, v[f] - v[e])
    return th


# ------------------------------------------------------------ PO-SL family
def po_set(M, v, t):
    out = []
    for f in range(M.m):
        if M.R[1 << f] == 0:
            continue
        low = 0
        for g in range(M.m):
            if v[g] < v[f] - t:
                low |= 1 << g
        if not M.in_cl(low, f):
            out.append(f)
    return out


def u_posl(M, v, t):
    po = po_set(M, v, t)
    u = [INF] * M.m
    clus = {}
    for c in set(M.comp):
        el = sorted((e for e in po if M.comp[e] == c), key=lambda e: v[e])
        lab = 0
        for i, e in enumerate(el):
            if i > 0 and v[e] - v[el[i - 1]] > t:
                lab += 1
            u[e] = lab
            clus[e] = (c, lab)
    return u, clus


def N_posl(M, v, t):
    u, _ = u_posl(M, v, t)
    return opt_bases(M, u)[0]


def breakpoints(v, m):
    return sorted({F0} | {v[f] - v[e] for e in range(m) for f in range(m) if v[f] - v[e] > 0})


# ------------------------------------------------------------ relation-only version
def N_from_relation(M, G):
    """N_G computed from the relation G (set of (e,f) with v_f - v_e <= t) only."""
    m = M.m
    po = []
    for f in range(m):
        if M.R[1 << f] == 0:
            continue
        low = 0
        for g in range(m):
            if (g, f) not in G:
                low |= 1 << g
        if not M.in_cl(low, f):
            po.append(f)
    poset = set(po)
    # single linkage: link if both (e,f),(f,e) in G, same component
    parent = {e: e for e in po}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for e in po:
        for f in po:
            if e < f and M.comp[e] == M.comp[f] and (e, f) in G and (f, e) in G:
                parent[find(e)] = find(f)
    cl = {e: find(e) for e in po}
    u = [INF] * m
    for e in po:
        # number of clusters strictly below e's cluster in its component
        below = set()
        for f in po:
            if M.comp[f] == M.comp[e] and cl[f] != cl[e] and (f, e) not in G:
                below.add(cl[f])          # v_e - v_f > t: f's cluster below
        u[e] = len(below)
    return opt_bases(M, u)[0]


# ------------------------------------------------------------ the update
def posl_update(M, blk, k, v, r, family=N_posl):
    """Returns (tau, lam, a, levels->N) for stage r at state v with the given family.
    lam_b = least breakpoint t < tau with b avoidable in N(t) (nu = r), else INF."""
    T = breakpoints(v, M.m)
    Ns = {}
    tau = None
    lam = {b: INF for b in range(k)}
    for t in T:
        N = family(M, v, t)
        Ns[t] = N
        A, nu = avoidable(N, blk, k)
        if nu > r:
            tau = t
            break
        for b in A:
            if lam[b] == INF:
                lam[b] = t
    a = {}
    for b in range(k):
        a[b] = F0 if (tau is None or lam[b] == INF) else max(tau - lam[b], F0)
    return tau, lam, a, Ns


def psi(M, blk, k, w, p):
    v = [w[e] - p[blk[e]] for e in range(M.m)]
    return sum(p.values(), F0) + beta(M, v)


def opt_rainbow(M, blk, k, w):
    vals = [wt(w, B) for B in M.bases if len(blocks_of(B, blk)) == k]
    return min(vals) if vals else None


def has_rainbow(M, blk, k):
    return any(len(blocks_of(B, blk)) == k for B in M.bases)


# ------------------------------------------------------------ random instances
def rand_blocks(M, k, rng, tries=200):
    for _ in range(tries):
        blk = [rng.randrange(k) for _ in range(M.m)]
        if has_rainbow(M, blk, k):
            return blk
    return None


def rand_values(m, rng, style):
    if style == "ties":
        return [Fraction(rng.randint(0, 3)) for _ in range(m)]
    if style == "ties5":
        return [Fraction(rng.randint(0, 5)) for _ in range(m)]
    if style == "spaced":
        return [Fraction(rng.randint(0, 4 * m), 4) for _ in range(m)]
    if style == "mixed":
        pool = [Fraction(rng.randint(-3, 3)) for _ in range(3)]
        return [rng.choice(pool) if rng.random() < 0.4 else Fraction(rng.randint(-6, 6), rng.randint(1, 3))
                for _ in range(m)]
    return [Fraction(rng.randint(-20, 20), rng.randint(1, 4)) for _ in range(m)]


def random_matroid(rng):
    kind = rng.choice(["uniform", "graphic", "gf2", "gf3", "paving", "sum", "partition", "loopy"])
    if kind == "uniform":
        k = rng.randint(2, 4)
        m = rng.randint(k + 1, min(9, k + 5))
        return kind, uniform(k, m)
    if kind == "graphic":
        n = rng.randint(3, 5)
        edges = []
        for _ in range(rng.randint(n, 9)):
            if rng.random() < 0.07:
                x = rng.randrange(n)
                edges.append((x, x))           # loop
            else:
                edges.append(tuple(rng.sample(range(n), 2)))
        M = graphic(n, edges)
        return kind, M
    if kind == "gf2":
        k = rng.randint(2, 4)
        m = rng.randint(k + 1, 9)
        cols = [rng.randrange(0 if rng.random() < 0.1 else 1, 1 << k) for _ in range(m)]
        return kind, gf2(cols)
    if kind == "gf3":
        k = rng.randint(2, 3)
        m = rng.randint(k + 1, 8)
        cols = [tuple(rng.randrange(3) for _ in range(k)) for _ in range(m)]
        return kind, gfp(cols, 3)
    if kind == "paving":
        k = rng.randint(2, 4)
        m = rng.randint(k + 2, 8)
        return kind, sparse_paving(k, m, rng)
    if kind == "sum":
        A = uniform(rng.randint(1, 2), rng.randint(2, 4))
        n = 3
        B = graphic(n, [tuple(rng.sample(range(n), 2)) for _ in range(rng.randint(2, 4))])
        return kind, direct_sum(A, B)
    if kind == "partition":
        cols = rng.randint(2, 4)
        m = rng.randint(cols + 1, 9)
        parts = [i % cols for i in range(m)]
        rng.shuffle(parts)
        return kind, partition_matroid(parts, {c: 1 for c in range(cols)})
    # loopy
    base = uniform(rng.randint(1, 3), rng.randint(3, 6))
    return kind, add_loops_coloops(base, rng.randint(0, 2), rng.randint(0, 2))
