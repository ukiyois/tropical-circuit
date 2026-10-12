"""Single-linkage family: the lemmas a proof needs, checked along the schedule.

N(t) = optimal-base matroid of the single-linkage cluster weights at scale t.
  (S1) sandwich: every possibly optimal base (theta(B) <= t) lies in N(t).
  (S2) Rado/Koenig for the matroid N(t): the avoidable block set S of N(t)
       satisfies |S| - r_{N(t)}(E_S) = k - nu(N(t)).
  (S3) along the update path v(s), s < tau: every optimal base of v(s) lies
       in N(s), and the ascent rate |S_s| - r_{N0(v(s))}(E(S_s)) equals k - r.
  (S4) progress: after one application, nu0 rises or the level-0 avoidable
       set strictly grows; applications per stage <= r+1.
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map, avoid_set
from rainbow_matroidal_families import theta_sl

ZERO = Fraction(0)


def lam_tau(th, M, blk, k, r):
    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
    res = update(entries, k, r)
    if res is None:
        return None
    a, tau = res
    lam = {}
    for b in range(k):
        c = [x for x, S in entries if len(S - {b}) >= r]
        lam[b] = min(c) if c else rp.INF
    return a, tau, lam


def check(M, blk, k, v, r, S):
    th = theta_sl(M, v)
    out = lam_tau(th, M, blk, k, r)
    if out is None:
        return None
    a, tau, lam = out
    loc = theta_map(M, v)
    levels = sorted(set(th.values()) | set(loc.values()))
    for t in levels:
        fam = {B for B in M.bases if th[B] <= t}
        S["S1"] += all(B in fam for B in M.bases if loc[B] <= t)
        S["S1n"] += 1
        nu = max(len({blk[e] for e in B}) for B in fam)
        av = avoid_set(M, blk, k, fam, nu)
        ES = {e for e in range(M.m) if blk[e] in av}
        rk = max(len(B & ES) for B in fam)
        S["S2"] += (len(av) - rk == k - nu)
        S["S2n"] += 1
    cuts = sorted({ZERO, tau} | {x for x in lam.values() if x != rp.INF and x < tau})
    for s in [(cuts[i] + cuts[i + 1]) / 2 for i in range(len(cuts) - 1)]:
        vs = {e: v[e] - max(s - lam[blk[e]], ZERO) for e in range(M.m)}
        ob = rp.optimal_bases(M, vs)
        fam = {B for B in M.bases if th[B] <= s}
        S["S3a"] += all(B in fam for B in ob)
        Ss = {b for b in range(k) if lam[b] <= s}
        ESs = {e for e in range(M.m) if blk[e] in Ss}
        S["S3b"] += (len(Ss) - max(len(B & ESs) for B in ob) == k - r)
        S["S3n"] += 1
    opt0 = [B for B in M.bases if th[B] == 0]
    S0 = avoid_set(M, blk, k, opt0, r)
    v2 = {e: v[e] - a[blk[e]] for e in range(M.m)}
    opt2 = rp.optimal_bases(M, v2)
    nu2 = max(len({blk[e] for e in B}) for B in opt2)
    if nu2 > r:
        S["S4aug"] += 1
    elif avoid_set(M, blk, k, opt2, r) > S0:
        S["S4grow"] += 1
    else:
        S["S4fail"] += 1
    return a


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 41
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow), ("binary5", st.binary5),
            ("rainbow tree6", st.rainbow_tree6), ("arborescence6", st.arborescence6)]
    for name, fam in fams:
        S = {key: 0 for key in ["S1", "S1n", "S2", "S2n", "S3a", "S3b", "S3n",
                                "S4aug", "S4grow", "S4fail", "over", "opt"]}
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            p = {b: ZERO for b in range(k)}
            for r in range(k):
                used = 0
                while used < 3 * k + 3:
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    a = check(M, blk, k, v, r, S)
                    if a is None or all(x == 0 for x in a.values()):
                        break
                    p = {b: p[b] + a[b] for b in range(k)}
                    used += 1
                S["over"] += (used > r + 1)
            S["opt"] += (rp.psi(M, blk, w, p) == rp.opt(M, blk, k, w))
        print(f"{name:13s} opt {S['opt']}/{trials}  S1 {S['S1']}/{S['S1n']}  S2 {S['S2']}/{S['S2n']}  "
              f"S3 subset {S['S3a']}/{S['S3n']} rate {S['S3b']}/{S['S3n']}  "
              f"S4 aug {S['S4aug']} grow {S['S4grow']} fail {S['S4fail']}  stages over r+1: {S['over']}",
              flush=True)


if __name__ == "__main__":
    main()
