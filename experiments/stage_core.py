"""Phase 2b core: the rainbow schedule with pluggable families, exact arithmetic.

Sets are bitmasks (Python ints).  A matroid is a rank oracle on masks, cached.
Weights are ints or Fractions; with integer w every PO-SL update is integral
(tau and lambda_b are levels |v_e - v_f|), so runs are exact.

Objects (greedy_intersection.tex, Section 4):
  M^u              MinBase(M, u): direct sum over the values of u of
                   (M | {u <= l}) / {u < l}, rank by eq. (rank-mu).
  nu(N), Av(N)     rainbow_av(N, blk, k): augmenting paths, then the reachable
                   set of the exchange graph of Lemma lem:avoidable.
  PO-SL            posl_u(M, v, t): Definition def:posl.
  update           update(M, blk, k, v, r, family): Definition def:update.
  P_t (exact)      exact_update(...): base enumeration, theta(B), small m only.
"""
import itertools
import random
from fractions import Fraction

INF = float("inf")


def bits(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def popcount(x):
    return bin(x).count("1")


def mask_of(it):
    s = 0
    for e in it:
        s |= 1 << e
    return s


# ---------------------------------------------------------------- matroids
class Matroid:
    def __init__(self, m, rank_fn, name=""):
        self.m = m
        self._rank = rank_fn
        self._cache = {}
        self.full = (1 << m) - 1
        self.name = name
        self.k = self.rank(self.full)
        self._components()

    def rank(self, S):
        c = self._cache.get(S)
        if c is None:
            c = self._rank(S)
            if len(self._cache) > 4_000_000:
                self._cache.clear()
            self._cache[S] = c
        return c

    def indep(self, S):
        return self.rank(S) == popcount(S)

    def in_cl(self, S, e):
        return self.rank(S | (1 << e)) == self.rank(S)

    def greedy(self, order):
        B = 0
        for e in order:
            if self.rank(B | (1 << e)) > popcount(B):
                B |= 1 << e
        return B

    def fund_circuit(self, B, e):
        """C(B, e) for e not in B (mask, contains e); B a base."""
        if self.rank(1 << e) == 0:
            return 1 << e
        out = 1 << e
        for f in bits(B):
            if self.rank((B & ~(1 << f)) | (1 << e)) == self.k:
                out |= 1 << f
        return out

    def _components(self):
        parent = list(range(self.m))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        B = self.greedy(range(self.m))
        for e in range(self.m):
            if B >> e & 1 or self.rank(1 << e) == 0:
                continue
            for f in bits(self.fund_circuit(B, e)):
                parent[find(e)] = find(f)
        roots = {}
        self.comp = []
        for e in range(self.m):
            self.comp.append(roots.setdefault(find(e), len(roots)))
        self.ncomp = len(roots)
        self.comp_mask = [0] * self.ncomp
        for e in range(self.m):
            self.comp_mask[self.comp[e]] |= 1 << e


def uniform(k, m):
    return Matroid(m, lambda S: min(popcount(S), k), f"U{k},{m}")


def graphic(n, edges):
    edges = list(edges)

    def r(S):
        parent = list(range(n))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        c = 0
        for e in bits(S):
            a, b = find(edges[e][0]), find(edges[e][1])
            if a != b:
                parent[a] = b
                c += 1
        return c
    M = Matroid(len(edges), r, f"graphic{n}")
    M.edges = edges
    M.nv = n
    return M


def gf2(cols):
    cols = list(cols)

    def r(S):
        basis = []
        for e in bits(S):
            x = cols[e]
            for b in basis:
                x = min(x, x ^ b)
            if x:
                basis.append(x)
        return len(basis)
    M = Matroid(len(cols), r, "binary")
    M.cols = cols
    return M


def partition(parts, caps=None):
    parts = list(parts)

    def r(S):
        cnt = {}
        for e in bits(S):
            cnt[parts[e]] = cnt.get(parts[e], 0) + 1
        return sum(min(c, 1 if caps is None else caps[p]) for p, c in cnt.items())
    return Matroid(len(parts), r, "partition")


def from_rank_table(m, R):
    return Matroid(m, lambda S: R[S], "table")


def direct_sum(M1, M2):
    m1 = M1.m
    lo = (1 << m1) - 1
    return Matroid(m1 + M2.m, lambda S: M1.rank(S & lo) + M2.rank(S >> m1), "sum")


# ------------------------------------------------------------ min-base matroid
class MinBase:
    """The matroid M^u of the minimum bases of u (any comparable values)."""

    def __init__(self, M, u):
        self.M = M
        self.m = M.m
        vals = sorted(set(u))
        self.levels = []
        below = 0
        for ell in vals:
            L = mask_of(e for e in range(M.m) if u[e] == ell)
            self.levels.append((L, below, M.rank(below)))
            below |= L

    def rank(self, A):
        tot = 0
        for L, below, rb in self.levels:
            X = A & L
            if X:
                tot += self.M.rank(below | X) - rb
        return tot

    def indep(self, A):
        for L, below, rb in self.levels:
            X = A & L
            if X and self.M.rank(below | X) - rb != popcount(X):
                return False
        return True

    def bases_key(self):
        """A canonical description: the level masks with their ranks (for equality tests)."""
        return tuple((L, self.M.rank(below | L) - rb) for L, below, rb in self.levels)


# ------------------------------------------------------------ rainbow structure
def rainbow_av(N, blk, k, I=0):
    """Largest rainbow independent set of N and the avoidable blocks Av(N).
    N has .m and .indep(mask).  Returns (nu, Av as frozenset, I mask)."""
    m = N.m
    while True:
        met = {blk[x] for x in bits(I)}
        outs = [y for y in range(m) if not I >> y & 1]
        Iel = bits(I)
        sources = [y for y in outs if blk[y] not in met]
        # BFS, lazily evaluating arcs y -> x (I - x + y indep) and x -> y (same block)
        prev = {}
        seen = set(sources)
        queue = list(sources)
        sink = None
        sinkcache = {}

        def is_sink(y):
            if y not in sinkcache:
                sinkcache[y] = N.indep(I | (1 << y))
            return sinkcache[y]
        head = 0
        while head < len(queue):
            z = queue[head]
            head += 1
            if not I >> z & 1:
                if is_sink(z):
                    sink = z
                    break
                for x in Iel:
                    if x not in seen and N.indep((I & ~(1 << x)) | (1 << z)):
                        seen.add(x)
                        prev[x] = z
                        queue.append(x)
            else:
                for y in outs:
                    if y not in seen and blk[y] == blk[z]:
                        seen.add(y)
                        prev[y] = z
                        queue.append(y)
        if sink is None:
            reach = seen
            av = set(range(k)) - met
            av |= {blk[x] for x in Iel if x in reach}
            return popcount(I), frozenset(av), I
        z = sink
        while True:
            I ^= 1 << z
            if z not in prev:
                break
            z = prev[z]


# ------------------------------------------------------------ families
def po_set(M, v, t):
    out = []
    for f in range(M.m):
        if M.rank(1 << f) == 0:
            continue
        low = 0
        thr = v[f] - t
        for g in range(M.m):
            if v[g] < thr:
                low |= 1 << g
        if not M.in_cl(low, f):
            out.append(f)
    return out


def posl_u(M, v, t):
    po = po_set(M, v, t)
    big = M.m + 1
    u = [big] * M.m
    for c in range(M.ncomp):
        el = sorted((e for e in po if M.comp[e] == c), key=lambda e: v[e])
        lab = 0
        for i, e in enumerate(el):
            if i > 0 and v[e] - v[el[i - 1]] > t:
                lab += 1
            u[e] = lab
    return u


def posl(M, v, t):
    return MinBase(M, posl_u(M, v, t))


def levels_of(v):
    m = len(v)
    return sorted({0} | {abs(v[e] - v[f]) for e in range(m) for f in range(m)})


def update(M, blk, k, v, r, family=posl, scan=False, levels=None):
    """Definition def:update.  Returns (tau, lam dict, a list, info).
    With scan=False uses binary search (valid for families obeying (F2));
    with scan=True evaluates every level (for testing candidate families)."""
    if levels is None:
        levels = levels_of(v)
    cache = {}

    def obs(i):
        if i not in cache:
            N = family(M, v, levels[i])
            nu, av, _ = rainbow_av(N, blk, k)
            cache[i] = (nu, av)
        return cache[i]
    L = len(levels)
    if scan:
        tau_i = None
        for i in range(L):
            if obs(i)[0] >= r + 1:
                tau_i = i
                break
    else:
        if obs(L - 1)[0] < r + 1:
            tau_i = None
        else:
            lo, hi = 0, L - 1          # obs(hi) >= r+1
            if obs(0)[0] >= r + 1:
                hi = 0
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if obs(mid)[0] >= r + 1:
                    hi = mid
                else:
                    lo = mid
            tau_i = hi
    if tau_i is None:
        raise RuntimeError("family never reaches nu >= r+1 (F4 fails)")
    tau = levels[tau_i]
    lam = {b: INF for b in range(k)}
    if tau_i > 0:
        if scan:
            for i in range(tau_i):
                for b in obs(i)[1]:
                    if lam[b] == INF:
                        lam[b] = levels[i]
        else:
            # Av(N(t)) is monotone on levels < tau: find change points by bisection
            def fill(lo, hi):
                # obs(lo), obs(hi) known, lo < hi
                if obs(lo)[1] == obs(hi)[1]:
                    return
                if hi - lo == 1:
                    for b in obs(hi)[1] - obs(lo)[1]:
                        lam[b] = min(lam[b], levels[hi])
                    return
                mid = (lo + hi) // 2
                fill(lo, mid)
                fill(mid, hi)
            for b in obs(0)[1]:
                lam[b] = levels[0]
            fill(0, tau_i - 1)
    a = [0] * k
    for b in range(k):
        if lam[b] != INF and lam[b] < tau:
            a[b] = tau - lam[b]
    return tau, lam, a, {"tau_i": tau_i, "levels": levels, "obs": cache}


def state(M, blk, k, v):
    """nu0 and S0 at v."""
    N = MinBase(M, v)
    nu, av, I = rainbow_av(N, blk, k)
    return nu, av


def shift(v, blk, a):
    return [v[e] - a[blk[e]] for e in range(len(v))]


def run_stage(M, blk, k, v, r, family=posl, cap=10_000, trace=None):
    """Apply the stage-r update until nu0 > r.  Returns (count, v)."""
    count = 0
    while True:
        nu0, S0 = state(M, blk, k, v)
        if nu0 > r:
            return count, v
        assert nu0 == r, (nu0, r)
        tau, lam, a, info = update(M, blk, k, v, r, family)
        if trace is not None:
            trace.append({"v": list(v), "S0": S0, "tau": tau, "lam": dict(lam), "a": list(a)})
        v = shift(v, blk, a)
        count += 1
        if count > cap:
            raise RuntimeError("stage cap exceeded")


def run_schedule(M, blk, k, w, family=posl, cap=10_000):
    v = list(w)
    p = [0] * k
    lens = []
    nu0, _ = state(M, blk, k, v)
    for r in range(1, k):
        if nu0 > r:
            lens.append(0)
            continue
        c, v2 = run_stage(M, blk, k, v, r, family, cap)
        for e in range(M.m):
            pass
        lens.append(c)
        v = v2
        nu0, _ = state(M, blk, k, v)
    p = None
    return lens, v


def beta(M, u):
    order = sorted(range(M.m), key=lambda e: u[e])
    B = M.greedy(order)
    return sum(u[e] for e in bits(B))


def psi_from_v(M, blk, k, w, v):
    """p is recovered from w - v on any element of each block (blocks nonempty)."""
    p = {}
    for e in range(M.m):
        p.setdefault(blk[e], w[e] - v[e])
    return sum(p.values()) + beta(M, v)


# ------------------------------------------------------------ brute force (small m)
def all_bases(M):
    return [mask_of(c) for c in itertools.combinations(range(M.m), M.k) if M.rank(mask_of(c)) == M.k]


def opt_rainbow(M, blk, k, w, bases=None):
    bases = all_bases(M) if bases is None else bases
    vals = [sum(w[e] for e in bits(B)) for B in bases if len({blk[e] for e in bits(B)}) == k]
    return min(vals) if vals else None


def theta(M, v, B):
    th = 0
    for e in range(M.m):
        if B >> e & 1 or M.rank(1 << e) == 0:
            continue
        for f in bits(M.fund_circuit(B, e) & ~(1 << e)):
            th = max(th, v[f] - v[e])
    return th


def exact_update(M, blk, k, v, r, bases=None):
    """The P_t update: tau = min theta over bases meeting >= r+1 blocks,
    lam_b = min theta over bases meeting >= r blocks other than b."""
    bases = all_bases(M) if bases is None else bases
    tau = INF
    lam = {b: INF for b in range(k)}
    for B in bases:
        th = theta(M, v, B)
        bl = {blk[e] for e in bits(B)}
        if len(bl) >= r + 1:
            tau = min(tau, th)
        for b in range(k):
            if len(bl - {b}) >= r:
                lam[b] = min(lam[b], th)
    a = [0] * k
    for b in range(k):
        if lam[b] < tau:
            a[b] = tau - lam[b]
    return tau, lam, a


def run_stage_exact(M, blk, k, v, r, cap=1000):
    bases = all_bases(M)
    count = 0
    while True:
        nu0, S0 = state(M, blk, k, v)
        if nu0 > r:
            return count, v
        tau, lam, a = exact_update(M, blk, k, v, r, bases)
        v = shift(v, blk, a)
        count += 1
        if count > cap:
            raise RuntimeError("cap")
