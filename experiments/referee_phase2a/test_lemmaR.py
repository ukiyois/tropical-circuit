"""Lemma R and Lemma R': for a matroid N and blocks R_1..R_k,
  max_Q |Q| - r_N(E_Q) = k - nu,  the avoidable set A attains it,
  and A is contained in every maximizer (so A is the minimal maximizer).
Exhaustive over Q, random matroids (any rank, loops allowed), random blocks
(empty blocks allowed)."""
import random
import sys
from core import *


def check(M, blk, k):
    bases = M.bases
    # rainbow independent sets of N: subsets of bases with distinct blocks; nu
    nu = nu_of(bases, blk)
    A, _ = avoidable(bases, blk, k)
    best = None
    vals = {}
    for q in range(1 << k):
        Q = {b for b in range(k) if q >> b & 1}
        d = len(Q) - M.R[Emask(blk, Q, M.m)]
        vals[frozenset(Q)] = d
        best = d if best is None else max(best, d)
    assert best == k - nu, ("max deficiency", best, k - nu)
    assert vals[A] == k - nu, ("A not maximizer", A, vals[A], k - nu)
    for Q, d in vals.items():
        if d == best:
            assert A <= Q, ("A not in maximizer", A, Q)
    # A equals the intersection of all maximizers
    inter = frozenset(range(k))
    for Q, d in vals.items():
        if d == best:
            inter &= Q
    assert inter == A
    return nu


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    rng = random.Random(seed)
    stats = {}
    for _ in range(trials):
        kind, M = random_matroid(rng)
        k = rng.randint(1, M.m)
        blk = [rng.randrange(k) for _ in range(M.m)]
        nu = check(M, blk, k)
        stats[kind] = stats.get(kind, 0) + 1
    print("Lemma R / R' ok on", trials, "instances", stats)


if __name__ == "__main__":
    main()
