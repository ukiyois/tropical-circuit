"""Print guarded Rado gaps of the possibly-optimal family in full.

A gap at a reachable state (stage r, level t <= tau): no base in Bt meets
nu(t)+1 blocks, yet no block set S certifies it, i.e.
  nu(t) < min_S ( rho_t(E_S) + k - |S| ).
Graphic instances are printed with their edges, colors and weights.
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map
from rainbow_rado_gap import gap_at

ZERO = Fraction(0)


def tree_instance(rng, n):
    while True:
        k = n - 1
        edges = [(u, x) for u in range(n) for x in range(u + 1, n)]
        edges = rng.sample(edges, rng.randint(k + 2, min(len(edges), 9)))
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(len(edges))}
        M = rp.Matroid(len(edges), rp.graphic_rank_fn(n, edges))
        if M.k == k and rp.opt(M, blk, k, {e: 0 for e in range(len(edges))}) is not None:
            return M, blk, k, edges


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 31
    want = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    rng = random.Random(seed)
    found = 0
    tries = 0
    while found < want and tries < 4000:
        tries += 1
        n = rng.choice([4, 5])
        M, blk, k, edges = tree_instance(rng, n)
        w = {e: Fraction(rng.randint(-4, 4)) for e in range(M.m)}
        p = {b: ZERO for b in range(k)}
        done = False
        for r in range(k):
            for _ in range(r + 1):
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                th = theta_map(M, v)
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                if res is None:
                    break
                a, tau = res
                for t in sorted(set(th.values())):
                    if t > tau:
                        break
                    nu, rado = gap_at(M, blk, k, th, t)
                    if nu < rado and not done:
                        done = True
                        found += 1
                        print("=" * 70)
                        print(f"n={n} k={k} stage r={r} level t={t} tau={tau} nu(t)={nu} rado={rado}")
                        for e, (x, y) in enumerate(edges):
                            print(f"  edge {e}: {x}-{y}  color {blk[e]}  v={v[e]}")
                        fam = [B for B in M.bases if th[B] <= t]
                        for B in sorted(fam, key=lambda B: (th[B], sorted(B))):
                            print(f"   B {sorted(B)} theta {th[B]} colors {sorted({blk[e] for e in B})}")
                        for s in range(k + 1):
                            for S in itertools.combinations(range(k), s):
                                ES = {e for e in range(M.m) if blk[e] in S}
                                val = max(len(B & ES) for B in fam) + k - s
                                if val == rado:
                                    print(f"   tight S={S}: rho={val - k + s}")
                p = {b: p[b] + a[b] for b in range(k)}
    print("found", found, "in", tries, "instances")


if __name__ == "__main__":
    main()
