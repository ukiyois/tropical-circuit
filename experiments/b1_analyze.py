"""B1: dissect one restart (chain member I_0 against I_1), exact.
Prints the chain data, the potentials, the deficit, the maximizing source sets
A and the terms of Theorem 3.4 (alpha(A), L_A(j), G_notA(j), beta_j), the
thresholds of each sink in I_0 and I_1.
Usage: imported (analyze(x0, slack, w, chain, mode, Pstart)) or run on the
balanced-chain instance found by b1_search.py (default)."""
import itertools

from b1_core import (Transport, values, chain_floor, chain_balanced, INF_CAP, unit,
                     rank_v, comparison_terms, sink_edges)


def threshold(kap, bj, v, edges):
    if bj == 0:
        return None
    for ell in sorted({v[e] for e in edges}):
        if sum(kap[e] for e in edges if v[e] <= ell) >= bj:
            return ell
    return None


def analyze(x0, slack, w, chain, mode="sched", Pstart=None, verbose=True):
    E = sorted(x0)
    p = 1 + max(e[0] for e in E)
    q = 1 + max(e[1] for e in E)
    cap = {e: (INF_CAP if slack[e] == "inf" else x0[e] + slack[e]) for e in E}
    insts = chain(x0, cap, p, q)
    I0, I1 = insts[0], insts[1]
    if mode == "sched":
        P = [0] * p
        for I in reversed(insts[1:]):
            if sum(I[0]):
                P, _ = Transport(I[0], I[1], I[2], w).schedule(P)
    else:
        P, _ = Transport(I1[0], I1[1], I1[2], w).schedule(list(Pstart))
    v = values(w, P)
    T = Transport(I0[0], I0[1], I0[2], w)
    d = T.F - T.state(P)[0]
    kap0, kap1 = unit(I0[0], I0[2]), unit(I1[0], I1[2])
    out = {"d": d, "P": P, "insts": insts}
    if verbose:
        print("I0: a", I0[0], "b", I0[1], "x", I0[3])
        print("I1: a", I1[0], "b", I1[1], "x", I1[3])
        print("cap0", {e: (c if c < INF_CAP else "inf") for e, c in I0[2].items()})
        print("P", P, " v", v)
        print("alpha", [I0[0][i] - 2 * I1[0][i] for i in range(p)],
              "beta", [I0[1][j] - 2 * I1[1][j] for j in range(q)])
        print("Delta", {e: kap0[e] - 2 * kap1[e] for e in E})
        for j in range(q):
            ej = sink_edges(I0[2], j)
            print(f"  sink {j}: thr I0 {threshold(kap0, I0[1][j], v, ej)} thr I1 "
                  f"{threshold(kap1, I1[1][j], v, ej)}; edges (v, kap0, 2kap1):",
                  {e: (v[e], kap0[e], 2 * kap1[e]) for e in ej})
        print("deficit", d)
    rows = []
    for rr in range(0, p + 1):
        for A in itertools.combinations(range(p), rr):
            A = frozenset(A)
            dA = sum(I0[0][i] for i in A) - rank_v(I0[0], I0[1], I0[2], v, A)
            alphaA, per = comparison_terms(I0, I1, v, A)
            bound = alphaA + sum(max(L, G - beta) for (L, G, beta) in per)
            rows.append((dA, bound, sorted(A), alphaA, per))
    rows.sort(key=lambda r: -r[0])
    if verbose:
        for r in rows[:4]:
            print(f"  A={r[2]}: d(A)={r[0]} bound={r[1]} alpha(A)={r[3]} (L,G,beta) per sink={r[4]}")
    out["rows"] = rows
    return out


if __name__ == "__main__":
    x0 = {(0, 0): 4, (0, 1): 6, (0, 2): 3, (1, 0): 5, (1, 1): 3, (1, 2): 5, (2, 0): 3, (2, 1): 1, (2, 2): 3}
    slack = {(0, 0): 0, (0, 1): 0, (0, 2): 'inf', (1, 0): 0, (1, 1): 2, (1, 2): 2, (2, 0): 0, (2, 1): 0, (2, 2): 2}
    w = {(0, 0): 11, (0, 1): 11, (0, 2): 5, (1, 0): 3, (1, 1): 0, (1, 2): 3, (2, 0): 4, (2, 1): 4, (2, 2): 1}
    analyze(x0, slack, w, chain_balanced, "sched")
