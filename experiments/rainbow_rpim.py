"""The finest weak-order coarsening that contains the possibly-optimal bases.

At level t a pair (e,f) with 0 < v_f - v_e <= t is RELEVANT if it is an
exchange pair of some possibly optimal base (theta(B) <= t, f in B, e notin B,
f in C(B,e)).  Within each connected component of M, merge the value intervals
[v_e, v_f] of relevant pairs; the clusters give a weak order u_t coarsening v,
and N(t) = optimal-base matroid of u_t.  Then
  - N(t) is a matroid, N(0) = N0(v), N grows with t,
  - every possibly optimal base lies in N(t)   (validity proof applies),
  - for bipartite matching N(t) is the paper's threshold graph {D <= t}.
Relevance is decided by brute force here.  Reported: optimality, exact gain,
progress dichotomy, applications per stage, and whether N(t) equals the
paper's threshold graphs on bipartite instances.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update, fundamental_circuit
from rainbow_local_lemmas import theta_map, avoid_set

ZERO = Fraction(0)


def components(M):
    parent = list(range(M.m))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for B in M.bases:
        for e in range(M.m):
            if e in B or M.rank([e]) == 0:
                continue
            for f in fundamental_circuit(M, B, e):
                parent[find(e)] = find(f)
    return {e: find(e) for e in range(M.m)}


def exchange_pairs(M, B):
    out = []
    for e in range(M.m):
        if e in B or M.rank([e]) == 0:
            continue
        for f in fundamental_circuit(M, B, e):
            out.append((e, f))
    return out


def possibly_optimal(M, v, f, t):
    """f lies in some base optimal for some u with |u - v| <= t/2."""
    return M.rank([g for g in range(M.m) if g != f and v[g] < v[f] - t] + [f]) > \
        M.rank([g for g in range(M.m) if g != f and v[g] < v[f] - t])


def theta_rpim(M, v, comp, loc, pairs, mode="exact"):
    levels = sorted({ZERO} | set(loc.values()) | {abs(v[e] - v[f]) for e in v for f in v})
    out = {}
    for t in levels:
        rel = set()
        if mode == "exact":
            for B in M.bases:
                if loc[B] <= t:
                    for (e, f) in pairs[B]:
                        if v[f] > v[e]:
                            rel.add((e, f))
        else:
            for f in range(M.m):
                if M.rank([f]) == 0 or not possibly_optimal(M, v, f, t):
                    continue
                for e in range(M.m):
                    if e != f and comp[e] == comp[f] and M.rank([e]) == 1 and 0 < v[f] - v[e] <= t:
                        rel.add((e, f))
        u = {}
        for c in set(comp.values()):
            elems = [e for e in range(M.m) if comp[e] == c]
            ivs = sorted((v[e], v[f]) for (e, f) in rel if comp[e] == c)
            merged = []
            for lo, hi in ivs:
                if merged and lo <= merged[-1][1]:
                    merged[-1][1] = max(merged[-1][1], hi)
                else:
                    merged.append([lo, hi])
            for e in elems:
                x = v[e]
                for lo, hi in merged:
                    if lo <= x <= hi:
                        x = lo
                        break
                u[e] = x
        b = rp.beta(M, u)
        for B in M.bases:
            if B not in out and rp.weight(u, B) == b:
                out[B] = t
    for B in M.bases:
        out.setdefault(B, rp.INF)
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 47
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    mode = sys.argv[3] if len(sys.argv) > 3 else "exact"
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow), ("binary5", st.binary5),
            ("rainbow tree6", st.rainbow_tree6), ("arborescence6", st.arborescence6)]
    for name, fam in fams:
        S = {"opt": 0, "eq": 0, "neq": 0, "aug": 0, "grow": 0, "fail": 0, "over": 0, "paper": 0, "papern": 0,
             "sand": 0, "sandn": 0}
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            comp = components(M)
            pairs = {B: exchange_pairs(M, B) for B in M.bases}
            p = {b: ZERO for b in range(k)}
            last = rp.psi(M, blk, w, p)
            for r in range(k):
                used = 0
                while used < 3 * k + 3:
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    loc = theta_map(M, v)
                    th = theta_rpim(M, v, comp, loc, pairs, mode)
                    if mode != "exact":
                        S["sand"] += all(th[B] <= loc[B] for B in M.bases)
                        S["sandn"] += 1
                    if name == "bipartite":
                        S["paper"] += (th == loc)
                        S["papern"] += 1
                    res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                    if res is None or all(x == 0 for x in res[0].values()):
                        break
                    a, tau = res
                    opt0 = [B for B in M.bases if th[B] == 0]
                    S0 = avoid_set(M, blk, k, opt0, r)
                    p = {b: p[b] + a[b] for b in range(k)}
                    used += 1
                    cur = rp.psi(M, blk, w, p)
                    S["eq" if cur - last == (k - r) * tau else "neq"] += 1
                    last = cur
                    v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    opt2 = rp.optimal_bases(M, v2)
                    if max(len({blk[e] for e in B}) for B in opt2) > r:
                        S["aug"] += 1
                    elif avoid_set(M, blk, k, opt2, r) > S0:
                        S["grow"] += 1
                    else:
                        S["fail"] += 1
                S["over"] += (used > r + 1)
            S["opt"] += (last == rp.opt(M, blk, k, w))
        extra = f"  equals paper's G_t {S['paper']}/{S['papern']}" if name == "bipartite" else ""
        if mode != "exact":
            extra += f"  sandwich {S['sand']}/{S['sandn']}"
        print(f"{name:13s} opt {S['opt']}/{trials}  gain exact {S['eq']} other {S['neq']}  "
              f"progress aug {S['aug']} grow {S['grow']} fail {S['fail']}  stages over r+1: {S['over']}{extra}",
              flush=True)


if __name__ == "__main__":
    main()
