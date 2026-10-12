"""Is the update a continuous function of the state?

A signed tropical circuit computes a continuous function, so an update rule
that jumps under an arbitrarily small perturbation of v cannot be compiled.
For each family, compare the update at v (with ties) and at v + eps*xi for
eps = 1/100, 1/1000, 1/10000 and random xi in [-1, 1]^E; report the largest
change of a in sup norm.  For a continuous rule it shrinks with eps.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map
from rainbow_rpim import components, exchange_pairs, theta_rpim
from rainbow_family_stress import theta_compsl

ZERO = Fraction(0)


def upd(M, blk, k, v, kind, comp, pairs, r):
    """U_r with r fixed by the schedule: a_b = (tau - lam_b)_+ from the min formulas."""
    if kind == "local":
        th = theta_map(M, v)
    elif kind == "comp-SL":
        th = theta_compsl(M, v, comp)
    else:
        th = theta_rpim(M, v, comp, theta_map(M, v), pairs, kind)
    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
    big = [x for x, S in entries if len(S) >= r + 1]
    tau = min(big) if big else rp.INF
    a = {}
    for b in range(k):
        c = [x for x, S in entries if len(S - {b}) >= r]
        lam = min(c) if c else rp.INF
        a[b] = ZERO if tau == rp.INF or lam == rp.INF else max(tau - lam, ZERO)
    return a


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 59
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    kinds = ["local", "comp-SL", "element", "exact"]
    worst = {kd: {1: ZERO, 2: ZERO, 3: ZERO} for kd in kinds}
    for _ in range(trials):
        fam = rng.choice([rp.bipartite, st.uniform, rp.rainbow_tree, rp.binary_rainbow])
        M, blk, k = fam(rng)
        v = {e: Fraction(rng.randint(0, 3)) for e in range(M.m)}
        comp = components(M)
        pairs = {B: exchange_pairs(M, B) for B in M.bases}
        xi = {e: Fraction(rng.randint(-100, 100), 100) for e in range(M.m)}
        r = max(len({blk[e] for e in B}) for B in rp.optimal_bases(M, v))
        if r == k:
            continue
        base = {kd: upd(M, blk, k, v, kd, comp, pairs, r) for kd in kinds}
        for j in (1, 2, 3):
            eps = Fraction(1, 10 ** (j + 1))
            v2 = {e: v[e] + eps * xi[e] for e in range(M.m)}
            for kd in kinds:
                a2 = upd(M, blk, k, v2, kd, comp, pairs, r)
                d = max(abs(a2[b] - base[kd][b]) for b in range(k))
                worst[kd][j] = max(worst[kd][j], d)
    for kd in kinds:
        print(f"{kd:8s} max |a(v+eps xi) - a(v)| at eps=1e-2,1e-3,1e-4: "
              f"{float(worst[kd][1]):.4f}, {float(worst[kd][2]):.4f}, {float(worst[kd][3]):.4f}")


if __name__ == "__main__":
    main()
