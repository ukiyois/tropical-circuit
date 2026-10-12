"""B1 warm start: shared helpers (exact integer arithmetic).

Reuses stage_transport_fast.Transport (type-compressed PO-SL, max-flow nu0 and
Av) and stage_transport.min_cost_flow.  Adds:
  chain_floor(x0, cap)     the chain of the phase 2b note: x' = floor(x / 2),
                           I' = (row sums, column sums, ceil(c / 2));
  chain_balanced(x0, cap)  the balanced chain: odd entries rounded up or down
                           along an orientation of the odd edges with
                           |in - out| <= 1 at every node;
  rank_v(I, v, A)          r_{M^v}(E_A) from eq. (rank-mu) on edge types
                           (independent of the max-flow code);
  deficit_rado(I, v)       max_A [a(A) - r_{M^v}(E_A)] by enumeration of A;
  g_sink(...)              the units of A at one sink, from (rank-mu);
  g_minmax(...)            the same from the min-max formula of Lemma 3.2;
  comparison_terms(...)    alpha(A), L_A(j), G_{bar A}(j), beta_j of Theorem 3.4;
  run_scaled(...)          the scaling schedule with restart deficits.
An instance is (a, b, cap, w) with cap, w dicts on edges (i, j); INF_CAP marks an
uncapacitated edge.
"""
import itertools
from fractions import Fraction

from stage_transport_fast import Transport, Flow
from stage_transport import min_cost_flow

INF_CAP = 10 ** 15


def unit(a, cap):
    """hat c_e = min(c_e, a_{i(e)})."""
    return {e: min(c, a[e[0]]) for e, c in cap.items()}


def values(w, P):
    return {e: w[e] - P[e[0]] for e in w}


# ------------------------------------------------------------------ chains
def feasible_flow(a, b, cap):
    p, q = len(a), len(b)
    S, T = p + q, p + q + 1
    fl = Flow(p + q + 2)
    eidx = {}
    for i in range(p):
        fl.add(S, i, a[i])
    for j in range(q):
        fl.add(p + j, T, b[j])
    for (i, j), c in cap.items():
        eidx[(i, j)] = (i, len(fl.g[i]))
        fl.add(i, p + j, c)
    if fl.maxflow(S, T) != sum(a):
        return None
    return {e: cap[e] - fl.g[u][k][1] for e, (u, k) in eidx.items()}


def sums(x, p, q):
    a = [0] * p
    b = [0] * q
    for (i, j), xe in x.items():
        a[i] += xe
        b[j] += xe
    return a, b


def half_cap(c):
    return c if c >= INF_CAP else (c + 1) // 2


def chain_floor(x0, cap, p, q):
    """List of (a, b, cap, x), finest first, down to the first x with max <= 1."""
    a, b = sums(x0, p, q)
    out = [(a, b, dict(cap), dict(x0))]
    x = dict(x0)
    while max(x.values(), default=0) > 1:
        x = {e: xe // 2 for e, xe in x.items()}
        c2 = {e: half_cap(c) for e, c in out[-1][2].items()}
        a2, b2 = sums(x, p, q)
        out.append((a2, b2, c2, dict(x)))
    return out


def balanced_orientation(odd_edges):
    """Orient the edges (i, j) (bipartite, source i, sink j) so that every node
    has |in - out| <= 1.  Returns the set of edges oriented i -> j.
    Trail peeling: start maximal trails at odd-degree nodes first."""
    adj = {}
    for e in odd_edges:
        i, j = e
        adj.setdefault(("s", i), []).append(e)
        adj.setdefault(("t", j), []).append(e)
    used = set()
    out_edges = set()

    def deg(u):
        return sum(1 for e in adj.get(u, []) if e not in used)

    def walk(u):
        while True:
            nxt = None
            for e in adj.get(u, []):
                if e not in used:
                    nxt = e
                    break
            if nxt is None:
                return
            used.add(nxt)
            i, j = nxt
            if u == ("s", i):
                out_edges.add(nxt)          # oriented i -> j
                u = ("t", j)
            else:
                u = ("s", i)                # oriented j -> i
    while len(used) < len(odd_edges):
        odd = [u for u in adj if deg(u) % 2 == 1]
        start = odd[0] if odd else next(u for u in adj if deg(u) > 0)
        walk(start)
    return out_edges


def chain_balanced(x0, cap, p, q):
    a, b = sums(x0, p, q)
    out = [(a, b, dict(cap), dict(x0))]
    x = dict(x0)
    while max(x.values(), default=0) > 1:
        odd = [e for e, xe in x.items() if xe % 2 == 1]
        up = balanced_orientation(odd)
        x = {e: xe // 2 + (1 if e in up else 0) for e, xe in x.items()}
        c2 = {e: half_cap(c) for e, c in out[-1][2].items()}
        a2, b2 = sums(x, p, q)
        assert all(x[e] <= c2[e] for e in x)
        out.append((a2, b2, c2, dict(x)))
    return out


# ------------------------------------------------------------------ ranks
def sink_edges(cap, j):
    return [e for e in cap if e[1] == j]


def g_sink(kap, bj, v, edges, inA):
    """Units of the edges with inA[e] in a min-v fill of the sink (ties to A),
    computed from eq. (rank-mu): sum over values l of
    min(b, U(<l) + kap(A, =l)) - min(b, U(<l))."""
    tot = 0
    for ell in sorted({v[e] for e in edges}):
        below = sum(kap[e] for e in edges if v[e] < ell)
        at_A = sum(kap[e] for e in edges if v[e] == ell and inA[e])
        tot += min(bj, below + at_A) - min(bj, below)
    return tot


def g_minmax(kap, bj, v, edges, inA):
    """min over t in {-inf} + values of max(kap(A, <= t), b - kap(not A, <= t))."""
    best = bj                                   # t = -inf
    for t in sorted({v[e] for e in edges}):
        xa = sum(kap[e] for e in edges if inA[e] and v[e] <= t)
        xb = sum(kap[e] for e in edges if not inA[e] and v[e] <= t)
        best = min(best, max(xa, bj - xb))
    return best


def rank_v(a, b, cap, v, A):
    kap = unit(a, cap)
    tot = 0
    for j in range(len(b)):
        ej = sink_edges(cap, j)
        if not ej:
            continue
        inA = {e: (e[0] in A) for e in ej}
        tot += g_sink(kap, b[j], v, ej, inA)
    return tot


def deficit_rado(a, b, cap, v):
    """max over source sets A of a(A) - r_{M^v}(E_A); returns (d, argmax A)."""
    p = len(a)
    best, arg = 0, frozenset()
    for rr in range(1, p + 1):
        for A in itertools.combinations(range(p), rr):
            A = frozenset(A)
            val = sum(a[i] for i in A) - rank_v(a, b, cap, v, A)
            if val > best:
                best, arg = val, A
    return best, arg


def comparison_terms(I, I2, v, A):
    """Terms of Theorem 3.4 for the pair I (fine) and I2 (coarse) at values v:
    returns (alpha(A), [(L_A(j), G_barA(j), beta_j)]_j)."""
    a, b, cap = I[0], I[1], I[2]
    a2, b2, cap2 = I2[0], I2[1], I2[2]
    kap, kap2 = unit(a, cap), unit(a2, cap2)
    alphaA = sum(a[i] - 2 * a2[i] for i in A)
    per = []
    for j in range(len(b)):
        L = G = 0
        for e in sink_edges(cap, j):
            dlt = kap[e] - 2 * kap2[e]
            if e[0] in A:
                L += max(-dlt, 0)
            else:
                G += max(dlt, 0)
        per.append((L, G, b[j] - 2 * b2[j]))
    return alphaA, per


def comparison_bound(I, I2, v, A):
    alphaA, per = comparison_terms(I, I2, v, A)
    return alphaA + sum(max(L, G - beta) for (L, G, beta) in per)


# ------------------------------------------------------------------ schedule
def run_scaled(a, b, cap, w, insts, X=None, check=True):
    """insts: list (finest first) of (a_f, b_f, cap_f, x_f).  Runs the coarsest
    from P = 0 with all stages, then each finer phase from the kept potentials
    with stages r >= F_f - X (all stages if X is None).  Returns a dict with
    the restart deficits, update counts, final P and correctness."""
    p = len(a)
    P = [0] * p
    deficits, updates, phases = [], 0, 0
    order = list(reversed(insts))               # coarsest first
    first = True
    for (af, bf, cf, xf) in order:
        if sum(af) == 0:
            continue
        T = Transport(af, bf, cf, w)
        nu0, _ = T.state(P)
        d = T.F - nu0
        if not first:
            deficits.append(d)
        rmin = 1 if (first or X is None) else max(1, T.F - X)
        if (not first) and X is not None and d > X:
            return {"ok": False, "deficits": deficits, "updates": updates, "P": P,
                    "fail_phase": (af, bf, cf), "d": d}
        P, lens = T.schedule(P, rmin=rmin)
        updates += sum(lens.values())
        phases += 1
        first = False
    out = {"ok": True, "deficits": deficits, "updates": updates, "P": P, "phases": phases}
    if check:
        Tf = Transport(a, b, cap, w)
        out["psi"] = Tf.psi(P)
        out["opt"] = min_cost_flow(a, b, cap, w)
        out["correct"] = out["psi"] == out["opt"]
    return out
