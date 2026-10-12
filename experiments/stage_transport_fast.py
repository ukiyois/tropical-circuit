"""Type-compressed PO-SL for the capacitated transportation problem (B1 prototype).

The rainbow instance of stage_transport.py has its slots of one source
interchangeable, so the PO-SL potentials stay equal on them and the whole update
can be computed on edge types:
  - v_e = w_e - P_i for e = (i, j);
  - e in PO_t  iff  sum of min(c_f, a_i(f)) over edges f into j with v_f < v_e - t
    is < b_j  (sink j not filled by elements cheaper by more than t);
  - clusters: single linkage at scale t on the PO edges of each sink (a sink whose
    capacity does not bind splits into per-edge components, which gives the same
    matroid);
  - N(t) = M^{u_t}: at sink j, level piece l has capacity b_j - C_j(<l), with
    C_j(<l) = min(b_j, sum of min(c_f, a_i(f)) over lower levels), and edge caps;
  - nu(N(t)) is a max flow S -> i (a_i) -> e (c_e) -> (j, level) -> T;
  - source i is avoidable iff it is reachable from S in the residual network of
    a maximum flow (Lemma lem:avoidable in flow form).
The update is a_i = (tau - lambda_i)_+ per source.  Exact integer arithmetic.
"""
import random
import sys
from collections import deque

INF = float("inf")


class Flow:
    def __init__(self, n):
        self.n = n
        self.g = [[] for _ in range(n)]

    def add(self, u, v, c):
        self.g[u].append([v, c, len(self.g[v])])
        self.g[v].append([u, 0, len(self.g[u]) - 1])

    def maxflow(self, s, t):
        total = 0
        while True:
            prev = [None] * self.n
            prev[s] = (-1, -1)
            q = deque([s])
            while q and prev[t] is None:
                u = q.popleft()
                for idx, (v, c, rev) in enumerate(self.g[u]):
                    if c > 0 and prev[v] is None:
                        prev[v] = (u, idx)
                        q.append(v)
            if prev[t] is None:
                return total
            push, v = INF, t
            while v != s:
                u, idx = prev[v]
                push = min(push, self.g[u][idx][1])
                v = u
            v = t
            while v != s:
                u, idx = prev[v]
                self.g[u][idx][1] -= push
                vv, _, rev = self.g[u][idx]
                self.g[vv][rev][1] += push
                v = u
            total += push

    def reach(self, s):
        seen = {s}
        q = deque([s])
        while q:
            u = q.popleft()
            for v, c, _ in self.g[u]:
                if c > 0 and v not in seen:
                    seen.add(v)
                    q.append(v)
        return seen


class Transport:
    def __init__(self, a, b, cap, w):
        self.a, self.b = list(a), list(b)
        self.p, self.q = len(a), len(b)
        self.edges = sorted(e for e, c in cap.items() if c > 0)
        self.cap = {e: cap[e] for e in self.edges}
        self.w = {e: w[e] for e in self.edges}
        self.F = sum(a)
        self.unit = {e: min(self.cap[e], self.a[e[0]]) for e in self.edges}

    def values(self, P):
        return {e: self.w[e] - P[e[0]] for e in self.edges}

    def structure(self, v, t, levels_from_value=False):
        """Returns the network data of N(t) (or of M^v when levels_from_value)."""
        u = {}
        for j in range(self.q):
            ej = [e for e in self.edges if e[1] == j]
            po = []
            for e in ej:
                cheaper = sum(self.unit[f] for f in ej if v[f] < v[e] - t)
                if cheaper < self.b[j]:
                    po.append(e)
            po.sort(key=lambda e: v[e])
            lab = 0
            for idx, e in enumerate(po):
                if idx > 0 and v[e] - v[po[idx - 1]] > t:
                    lab += 1
                u[e] = lab
        return u

    def nu_av(self, u):
        """Max flow in N = M^u and the avoidable sources."""
        p, q = self.p, self.q
        E = self.edges
        # nodes: S, sources 0..p-1, edges, (j, level) nodes, T
        S = 0
        src = lambda i: 1 + i
        enode = {e: 1 + p + k for k, e in enumerate(E)}
        lvl_nodes = {}
        base = 1 + p + len(E)
        for e in E:
            if e in u:
                key = (e[1], u[e])
                if key not in lvl_nodes:
                    lvl_nodes[key] = base + len(lvl_nodes)
        T = base + len(lvl_nodes)
        fl = Flow(T + 1)
        for i in range(p):
            fl.add(S, src(i), self.a[i])
        for e in E:
            if e not in u:
                continue
            fl.add(src(e[0]), enode[e], self.cap[e])
            fl.add(enode[e], lvl_nodes[(e[1], u[e])], self.cap[e])
        for (j, l), node in lvl_nodes.items():
            below = sum(self.unit[f] for f in E if f[1] == j and f in u and u[f] < l)
            capl = self.b[j] - min(self.b[j], below)
            fl.add(node, T, capl)
        nu = fl.maxflow(S, T)
        R = fl.reach(S)
        av = frozenset(i for i in range(p) if src(i) in R)
        return nu, av

    def state(self, P):
        v = self.values(P)
        # M^v: PO_0 and levels = value classes (single linkage at scale 0)
        return self.nu_av(self.structure(v, 0))

    def update(self, P, r):
        v = self.values(P)
        levels = sorted({0} | {abs(v[e] - v[f]) for e in self.edges for f in self.edges})
        obs = {}

        def ob(i):
            if i not in obs:
                obs[i] = self.nu_av(self.structure(v, levels[i]))
            return obs[i]
        lo, hi = 0, len(levels) - 1
        if ob(hi)[0] < r + 1:
            raise RuntimeError("no rainbow base at the top level")
        if ob(0)[0] >= r + 1:
            return [0] * self.p, 0
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ob(mid)[0] >= r + 1:
                hi = mid
            else:
                lo = mid
        tau = levels[hi]
        lam = [INF] * self.p
        for i in range(hi):
            for s in ob(i)[1]:
                if lam[s] == INF:
                    lam[s] = levels[i]
        a = [max(tau - lam[i], 0) if lam[i] != INF else 0 for i in range(self.p)]
        return a, tau

    def psi(self, P):
        """sum_i a_i P_i + beta(v), beta by the greedy fill of each sink."""
        v = self.values(P)
        tot = sum(self.a[i] * P[i] for i in range(self.p))
        for j in range(self.q):
            ej = sorted((e for e in self.edges if e[1] == j), key=lambda e: v[e])
            need = self.b[j]
            for e in ej:
                take = min(need, self.unit[e])
                tot += take * v[e]
                need -= take
        return tot

    def schedule(self, P=None, rmin=1):
        P = [0] * self.p if P is None else list(P)
        lens = {}
        nu0, _ = self.state(P)
        for r in range(rmin, self.F):
            if nu0 > r:
                continue
            c = 0
            while True:
                nu0, _ = self.state(P)
                if nu0 > r:
                    break
                a, tau = self.update(P, r)
                P = [P[i] + a[i] for i in range(self.p)]
                c += 1
                if c > 10_000:
                    raise RuntimeError("stage cap")
            lens[r] = c
        return P, lens


def min_cost_flow(a, b, cap, w):
    from stage_transport import min_cost_flow as mcf
    return mcf(a, b, cap, w)


def random_instance(rng, p, q, U, wbits=20, density=1.0):
    while True:
        cap = {}
        for i in range(p):
            for j in range(q):
                if rng.random() < density:
                    cap[(i, j)] = rng.randint(1, U)
        a = [rng.randint(1, U) for _ in range(p)]
        F = sum(a)
        b = [0] * q
        for _ in range(F):
            b[rng.randrange(q)] += 1
        w = {e: rng.randrange(0, 1 << wbits) for e in cap}
        if min_cost_flow(a, b, cap, w) is not None:
            return a, b, cap, w


if __name__ == "__main__":
    import stage_core as sc
    from stage_transport import build, schedule
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    bad = 0
    for trial in range(40):
        a, b, cap, w = random_instance(rng, 3, 3, 2, wbits=5)
        T = Transport(a, b, cap, w)
        P, lens = T.schedule()
        M, blk, k, ww, elems = build(a, b, cap, w)
        lens2, v, start = schedule(M, blk, k, ww)
        same = [lens.get(r, 0) for r in range(1, T.F)] == lens2
        opt = min_cost_flow(a, b, cap, w)
        ok = T.psi(P) == opt == sc.psi_from_v(M, blk, k, ww, v)
        bad += (not same) or (not ok)
        if not same or not ok:
            print("MISMATCH", a, b, cap, w, lens, lens2, T.psi(P), opt)
    print("compressed vs uncompressed: 40 instances, mismatches", bad)
