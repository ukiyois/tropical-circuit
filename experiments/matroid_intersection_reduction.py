"""Weighted matroid intersection through Corollary 9.

Common bases of M1, M2 (rank r on E, |E| = m) correspond to rainbow bases of
N = M1 (+) M2* on E x {1, 2} with blocks {(e,1), (e,2)}: choosing copy 1 of
the elements of X is a base of N iff X is a base of M1 and E - X is a base of
M2*, i.e. iff X is a base of M1 and of M2.  Weight w_e on copy 1, 0 on copy 2.
N has m blocks and rank r + (m - r) = m, and its rank circuit is built from
those of M1 and M2 (r*(S) = |S| + r(E - S) - r(E)).

Check: min-weight common base by brute force against the PO-SL schedule run on
the rainbow instance, on random binary and graphic pairs with ties.
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_rpim import components
from rainbow_posl import theta_posl

ZERO = Fraction(0)


def random_matroid_rank_fn(rng, m, r):
    while True:
        if rng.random() < 0.5:
            cols = [rng.randrange(1, 1 << r) for _ in range(m)]
            fn = rp.gf2_rank_fn(cols)
        else:
            n = r + 1
            edges = [tuple(sorted(rng.sample(range(n), 2))) for _ in range(m)]
            fn = rp.graphic_rank_fn(n, edges)
        if fn(frozenset(range(m))) == r:
            return fn


def brute_common(m, r1, r2, w):
    best = None
    for X in itertools.combinations(range(m), r1(frozenset(range(m)))):
        X = frozenset(X)
        if r1(X) == len(X) and r2(X) == len(X):
            val = sum(w[e] for e in X)
            best = val if best is None or val < best else best
    return best


def via_rainbow(m, r1, r2, w):
    rE2 = r2(frozenset(range(m)))

    def rank_N(S):
        A = frozenset(e for e in S if e < m)
        Bc = frozenset(e - m for e in S if e >= m)
        return r1(A) + len(Bc) + r2(frozenset(range(m)) - Bc) - rE2
    N = rp.Matroid(2 * m, rank_N)
    blk = {e: e % m for e in range(2 * m)}
    wN = {e: (w[e] if e < m else ZERO) for e in range(2 * m)}
    k = m
    assert N.k == k
    comp = components(N)
    p = {b: ZERO for b in range(k)}
    for r in range(k):
        for _ in range(r * ((2 * m) ** 2 // 4 + 1)):
            v = {e: wN[e] - p[blk[e]] for e in range(N.m)}
            th = theta_posl(N, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in N.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
    return rp.psi(N, blk, wN, p), rp.opt(N, blk, k, wN)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 97
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    ok = skipped = bad = 0
    for _ in range(trials):
        m = rng.randint(3, 5)
        r = rng.randint(1, m - 1)
        r1 = random_matroid_rank_fn(rng, m, r)
        r2 = random_matroid_rank_fn(rng, m, r)
        w = {e: Fraction(rng.randint(-3, 3)) if rng.random() < 0.5 else Fraction(rng.randint(-6, 6), 2)
             for e in range(m)}
        target = brute_common(m, r1, r2, w)
        if target is None:
            skipped += 1
            continue
        psi, rainbow_opt = via_rainbow(m, r1, r2, w)
        assert rainbow_opt == target, ("reduction mismatch", rainbow_opt, target)
        if psi == target:
            ok += 1
        else:
            bad += 1
            print("FAIL", m, r, {e: str(x) for e, x in w.items()}, psi, target)
    print(f"common-base instances {ok + bad}: schedule optimal {ok}, wrong {bad}; "
          f"skipped (no common base) {skipped}")


if __name__ == "__main__":
    main()
