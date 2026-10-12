"""Matroidal, compiler-compatible filtrations: do they give a valid update?

A family read from the pair relation G_t = {(e,f): |v_e - v_f| <= t} only.
  single-linkage: clusters = classes of the chain closure of G_t (intervals of
      the sorted values); u_t = cluster index; N(t) = optimal-base matroid of u_t.
      Monotone in t, N(0) = M^v, N(inf) = M, matroidal, so its observables are
      matroid intersections.
theta_SL(B) = least t at which B is optimal for u_t.  Same update formula as
rainbow_filtrations.py; reported: optimality, gain vs (k-r) tau, Psi drops,
stalls.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update

ZERO = Fraction(0)


def clusters(v, t):
    order = sorted(v, key=lambda e: v[e])
    lab, c = {}, 0
    for i, e in enumerate(order):
        if i > 0 and v[e] - v[order[i - 1]] > t:
            c += 1
        lab[e] = c
    return lab


def theta_sl(M, v):
    levels = sorted({ZERO} | {abs(v[e] - v[f]) for e in v for f in v})
    out = {}
    for t in levels:
        u = clusters(v, t)
        b = rp.beta(M, u)
        for B in M.bases:
            if B not in out and rp.weight(u, B) == b:
                out[B] = t
    return out


def run(M, blk, k, w, cap=30):
    p = {b: ZERO for b in range(k)}
    last = rp.psi(M, blk, w, p)
    st_ = {"eq": 0, "gt": 0, "lt": 0, "drop": 0, "stall": False}
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_sl(M, v)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None:
                break
            a, tau = res
            if all(x == 0 for x in a.values()):
                break
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            cur = rp.psi(M, blk, w, p)
            g, target = cur - last, (k - r) * tau
            st_["eq" if g == target else ("gt" if g > target else "lt")] += 1
            st_["drop"] += (g < 0)
            last = cur
        st_["stall"] |= (used == cap)
    return last, st_


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 37
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    rng = random.Random(seed)
    for name, fam in [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
                      ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow)]:
        ok = 0
        agg = {"eq": 0, "gt": 0, "lt": 0, "drop": 0, "stall": 0}
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            val, s = run(M, blk, k, w)
            ok += (val == rp.opt(M, blk, k, w))
            for key in ("eq", "gt", "lt", "drop"):
                agg[key] += s[key]
            agg["stall"] += s["stall"]
        print(f"{name:13s} single-linkage optimal {ok}/{trials}  gain =,>,< {agg['eq']},{agg['gt']},{agg['lt']}"
              f"  Psi drops {agg['drop']}  stalls {agg['stall']}", flush=True)


if __name__ == "__main__":
    main()
