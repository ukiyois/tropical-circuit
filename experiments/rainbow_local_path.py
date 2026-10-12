"""Along the update path, is the local update a steepest-ascent path?

For the local update a_b = (tau - lam_b)_+ put a(s)_b = (s - lam_b)_+ for
s in [0, tau] and v(s) = v - a(s)[blk].  Hypothesis (H): for every s < tau,
  (H1) the optimal-base matroid N0(v(s)) has rainbow rank r, and
  (H2) its avoidable blocks are exactly S_s = { b : lam_b <= s }.
(H1)+(H2) make d/ds Psi = |S_s| - r_{N0(v(s))}(E(S_s)) = k - r, which is the
exact gain.  Every optimal base of v(s) lies in the level-s family, since
0 <= a(s) <= s; (H) asks for the converse at the level of avoidable blocks.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map, avoid_set

ZERO = Fraction(0)


def lam_of(entries, k, r):
    lam = {}
    for b in range(k):
        c = [th for th, S in entries if len(S - {b}) >= r]
        lam[b] = min(c) if c else rp.INF
    return lam


def check(M, blk, k, v, r, stats):
    th = theta_map(M, v)
    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
    res = update(entries, k, r)
    if res is None:
        return None
    a, tau = res
    lam = lam_of(entries, k, r)
    cuts = sorted({ZERO, tau} | {x for x in lam.values() if x != rp.INF and x < tau}
                  | {t for t in th.values() if t < tau})
    probes = [(cuts[i] + cuts[i + 1]) / 2 for i in range(len(cuts) - 1)] + cuts[:-1]
    for s in probes:
        vs = {e: v[e] - max(s - lam[blk[e]], ZERO) for e in range(M.m)}
        ob = rp.optimal_bases(M, vs)
        nu = max(len({blk[e] for e in B}) for B in ob)
        stats["n"] += 1
        stats["H1"] += (nu == r)
        Ss = {b for b in range(k) if lam[b] <= s}
        stats["H2"] += (avoid_set(M, blk, k, ob, r) == Ss)
        ES = {e for e in range(M.m) if blk[e] in Ss}
        rate = len(Ss) - max(len(B & ES) for B in ob)
        stats["rate"] += (rate == k - r)
    return a


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 17
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow), ("binary5", st.binary5),
            ("rainbow tree6", st.rainbow_tree6)]
    for name, fam in fams:
        stats = {"n": 0, "H1": 0, "H2": 0, "rate": 0}
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            p = {b: ZERO for b in range(k)}
            for r in range(k):
                for _ in range(r + 1):
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    a = check(M, blk, k, v, r, stats)
                    if a is None:
                        break
                    p = {b: p[b] + a[b] for b in range(k)}
        print(f"{name:13s} probes {stats['n']:5d}  H1 {stats['H1']}  H2 {stats['H2']}  "
              f"rate == k-r {stats['rate']}", flush=True)


if __name__ == "__main__":
    main()
