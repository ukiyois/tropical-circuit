"""Phase 2a prototype: partition matroid + general matroid (rainbow bases).

E is split into blocks R_0..R_{k-1}; M is a matroid of rank k on E.
  Opt(w) = min { w(B) : B a base of M meeting every block once }.
Bipartite matching: M = column partition.  Arborescences: M = graphic.

State: block potentials p only.  v = w - p[blk].
  Psi(p) = sum p + beta(v),  beta(v) = min v-weight of a base of M.
Psi(p) <= Opt(w) for every p, with equality at a maximizer (Edmonds).

Reduced structure at v:
  lam_e = least c with e in cl{ f != e : v_f <= c }   (closure level)
  rho_e = (v_e - lam_e)_+                             (reduced cost)
  vhat  = v - rho
  N(t)  = M^vhat | { rho <= t }
N(0) is the optimal-base matroid of v, N(t) grows with t, and N(t) is the
optimal-base matroid of v - min(t, rho).  All three facts are asserted below.

Candidate update U_r (threshold integral, generalizing the q-free bipartite
schedule of lagrangian_bipartite.py):
  tau   = least t with a rainbow independent (r+1)-set in N(t)
  lam_b = least t with a rainbow independent r-set in N(t) avoiding block b
  a_b   = (tau - lam_b)_+ ,  p <- p + a
Reference: exact steepest ascent of Psi along 1_S, S the minimal maximizer of
  |S| - r_{N(0)}(union of blocks S), with exact line search.
"""
import itertools
import math
import random
import sys
from fractions import Fraction

INF = math.inf
ZERO = Fraction(0)


# ---------------------------------------------------------------- matroids
class Matroid:
    def __init__(self, m, rank_fn):
        self.m = m
        self._rank = rank_fn
        self._cache = {}
        self.k = self.rank(range(m))
        self.bases = [frozenset(B) for B in itertools.combinations(range(m), self.k)
                      if self.rank(B) == self.k]

    def rank(self, S):
        key = frozenset(S)
        if key not in self._cache:
            self._cache[key] = self._rank(key)
        return self._cache[key]


def gf2_rank_fn(cols):
    def r(S):
        basis = []
        for e in S:
            x = cols[e]
            for b in basis:
                x = min(x, x ^ b)
            if x:
                basis.append(x)
        return len(basis)
    return r


def graphic_rank_fn(n, arcs):
    def r(S):
        parent = list(range(n))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        cnt = 0
        for e in S:
            u, x = arcs[e]
            ru, rx = find(u), find(x)
            if ru != rx:
                parent[ru] = rx
                cnt += 1
        return cnt
    return r


# ------------------------------------------------------- weighted structure
def weight(u, B):
    return sum(u[e] for e in B)


def beta(M, u):
    return min(weight(u, B) for B in M.bases)


def optimal_bases(M, u):
    b = beta(M, u)
    return [B for B in M.bases if weight(u, B) == b]


def closure_levels(M, v):
    lam = {}
    for e in range(M.m):
        if M.rank([e]) == 0:
            lam[e] = None                      # loop, in no base
            continue
        lam[e] = INF                           # coloop
        S = []
        for f in sorted((f for f in range(M.m) if f != e), key=lambda f: v[f]):
            S.append(f)
            if M.rank(S + [e]) == M.rank(S):
                lam[e] = v[f]
                break
    return lam


def reduced(M, blk, v):
    """rho and the entries (threshold, block set) of the bases of N(infinity)."""
    lam = closure_levels(M, v)
    rho = {e: (ZERO if lam[e] is None or lam[e] == INF else max(v[e] - lam[e], ZERO))
           for e in range(M.m)}
    vhat = {e: v[e] - rho[e] for e in range(M.m)}
    assert beta(M, vhat) == beta(M, v)
    nbases = optimal_bases(M, vhat)
    entries = [(max(rho[e] for e in B), frozenset(blk[e] for e in B), B) for B in nbases]
    assert {B for thr, S, B in entries if thr == 0} == set(optimal_bases(M, v))
    return rho, entries


def check_threshold_matroid(M, v, rho, entries):
    """N(t) equals the optimal-base matroid of v - min(t, rho), at every breakpoint."""
    for t in sorted({ZERO} | set(rho.values())):
        vt = {e: v[e] - min(t, rho[e]) for e in range(M.m)}
        assert {B for thr, S, B in entries if thr <= t} == set(optimal_bases(M, vt))


# ----------------------------------------------------------------- objective
def psi(M, blk, w, p):
    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
    return sum(p.values()) + beta(M, v)


def opt(M, blk, k, w):
    vals = [weight(w, B) for B in M.bases if sorted(blk[e] for e in B) == list(range(k))]
    return min(vals) if vals else None


# --------------------------------------------------------- candidate update
def candidate(entries, k, r):
    nu0 = max(len(S) for thr, S, B in entries if thr == 0)
    if nu0 != r:
        return None
    big = [thr for thr, S, B in entries if len(S) >= r + 1]
    if not big:
        return None
    tau = min(big)
    a = {}
    for b in range(k):
        c = [thr for thr, S, B in entries if len(S - {b}) >= r]
        a[b] = max(tau - min(c), ZERO) if c else ZERO
    return a, tau


def run_candidate(M, blk, k, w, cap=40, check=False):
    p = {b: ZERO for b in range(k)}
    last = psi(M, blk, w, p)
    stats = {"apps": [], "gain_eq": 0, "gain_gt": 0, "gain_lt": 0, "stall": False}
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            rho, entries = reduced(M, blk, v)
            if check:
                check_threshold_matroid(M, v, rho, entries)
            res = candidate(entries, k, r)
            if res is None:
                break
            a, tau = res
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            cur = psi(M, blk, w, p)
            gain, target = cur - last, (k - r) * tau
            stats["gain_eq" if gain == target else ("gain_gt" if gain > target else "gain_lt")] += 1
            last = cur
        if used == cap:
            stats["stall"] = True
        stats["apps"].append(used)
    return last, stats


# ---------------------------------------------------------------- reference
def run_steepest(M, blk, k, w, cap=400):
    p = {b: ZERO for b in range(k)}
    for it in range(cap):
        v = {e: w[e] - p[blk[e]] for e in range(M.m)}
        b0 = beta(M, v)
        ob = [B for B in M.bases if weight(v, B) == b0]

        def g(S):
            return len(S) - max(sum(1 for e in B if blk[e] in S) for B in ob)
        subsets = [frozenset(c) for s in range(k + 1) for c in itertools.combinations(range(k), s)]
        best = max(g(S) for S in subsets)
        if best <= 0:
            return psi(M, blk, w, p), it
        S = frozenset.intersection(*[S for S in subsets if g(S) == best])
        cnt = {B: sum(1 for e in B if blk[e] in S) for B in M.bases}
        mstar = max(cnt[B] for B in ob)
        steps = [(weight(v, B) - b0) / (cnt[B] - mstar) for B in M.bases if cnt[B] > mstar]
        if not steps:
            return None, it                    # Psi unbounded: no rainbow base
        s = min(steps)
        p = {b: p[b] + (s if b in S else ZERO) for b in range(k)}
    return psi(M, blk, w, p), cap


# ----------------------------------------------------------------- families
def bipartite(rng):
    n = rng.randint(2, 4)
    perm = list(range(n)); rng.shuffle(perm)
    E = sorted({(i, perm[i]) for i in range(n)} |
               {(i, j) for i in range(n) for j in range(n) if rng.random() < 0.5})
    blk = {e: E[e][0] for e in range(len(E))}
    col = {e: E[e][1] for e in range(len(E))}
    return Matroid(len(E), lambda S: len({col[e] for e in S})), blk, n


def arborescence(rng):
    n = rng.randint(3, 5)
    arcs = []
    order = list(range(1, n)); rng.shuffle(order)
    seen = [0]
    for x in order:                          # a spanning arborescence exists
        arcs.append((rng.choice(seen), x))
        seen.append(x)
    extra = [(u, x) for u in range(n) for x in range(1, n)
             if u != x and (u, x) not in arcs and rng.random() < 0.35]
    arcs += rng.sample(extra, min(len(extra), 10 - len(arcs)))
    blk = {e: arcs[e][1] - 1 for e in range(len(arcs))}
    return Matroid(len(arcs), graphic_rank_fn(n, arcs)), blk, n - 1


def rainbow_tree(rng):
    while True:
        n = rng.randint(3, 5)
        k = n - 1
        edges = [(u, x) for u in range(n) for x in range(u + 1, n)]
        edges = rng.sample(edges, min(len(edges), rng.randint(k + 1, 10)))
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(len(edges))}
        M = Matroid(len(edges), graphic_rank_fn(n, edges))
        if M.k == k and opt(M, blk, k, {e: 0 for e in range(len(edges))}) is not None:
            return M, blk, k


def binary_rainbow(rng):
    while True:
        k = rng.randint(2, 4)
        m = rng.randint(k + 1, min(10, 2 * k + 2))
        cols = [rng.randrange(1, 1 << k) for _ in range(m)]
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(m)}
        M = Matroid(m, gf2_rank_fn(cols))
        if M.k == k and opt(M, blk, k, {e: 0 for e in range(m)}) is not None:
            return M, blk, k


def random_weights(rng, m):
    pool = [Fraction(rng.randint(-3, 3)) for _ in range(3)]
    return {e: (rng.choice(pool) if rng.random() < 0.4
                else Fraction(rng.randint(-6, 6), rng.randint(1, 3))) for e in range(m)}


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    for name, family in [("bipartite (calibration)", bipartite),
                         ("arborescence", arborescence),
                         ("rainbow spanning tree", rainbow_tree),
                         ("binary rainbow base", binary_rainbow)]:
        ok = ref_ok = stalls = 0
        gains = {"gain_eq": 0, "gain_gt": 0, "gain_lt": 0}
        worst, ref_worst = 0, 0
        fails = []
        for t in range(trials):
            M, blk, k = family(rng)
            w = random_weights(rng, M.m)
            target = opt(M, blk, k, w)
            val, st = run_candidate(M, blk, k, w, check=(t < 40))
            ref, its = run_steepest(M, blk, k, w)
            ref_ok += (ref == target)
            ref_worst = max(ref_worst, its)
            stalls += st["stall"]
            worst = max(worst, max(st["apps"]))
            for key in gains:
                gains[key] += st[key]
            if val == target:
                ok += 1
            elif len(fails) < 2:
                fails.append((k, dict(blk), {e: str(x) for e, x in w.items()}, str(val), str(target), st["apps"]))
        print(f"{name:24s} candidate optimal {ok}/{trials}  stalls {stalls}  max apps/stage {worst}  "
              f"gain =,>,< (k-r)tau: {gains['gain_eq']},{gains['gain_gt']},{gains['gain_lt']}  |  "
              f"steepest optimal {ref_ok}/{trials}  max iters {ref_worst}")
        for f in fails:
            print("   fail:", f)


if __name__ == "__main__":
    main()
