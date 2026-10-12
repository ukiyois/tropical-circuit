"""Stress test of the 'local' filtration on larger instances.

theta(B) = max { v_f - v_e : e notin B, f in C(B,e) }_+ ; equivalently
B is optimal for v - theta * 1_B, and B is in the level-t family iff
B cap {v <= c + t} spans {v <= c} for every c.

Families: arborescences on 6 vertices, rainbow spanning trees on 6 vertices,
binary matroids of rank 5, uniform matroids U_{k,m} with random blocks.
Reports optimality, gain == (k-r)*tau, and applications per stage.
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import run


def arborescence6(rng):
    n = 6
    arcs = []
    order = list(range(1, n)); rng.shuffle(order)
    seen = [0]
    for x in order:
        arcs.append((rng.choice(seen), x))
        seen.append(x)
    extra = [(u, x) for u in range(n) for x in range(1, n) if u != x and (u, x) not in arcs]
    arcs += rng.sample(extra, rng.randint(3, 6))
    blk = {e: arcs[e][1] - 1 for e in range(len(arcs))}
    return rp.Matroid(len(arcs), rp.graphic_rank_fn(n, arcs)), blk, n - 1


def rainbow_tree6(rng):
    while True:
        n = 6
        k = n - 1
        edges = [(u, x) for u in range(n) for x in range(u + 1, n)]
        edges = rng.sample(edges, rng.randint(k + 2, 10))
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(len(edges))}
        M = rp.Matroid(len(edges), rp.graphic_rank_fn(n, edges))
        if M.k == k and rp.opt(M, blk, k, {e: 0 for e in range(len(edges))}) is not None:
            return M, blk, k


def binary5(rng):
    while True:
        k = 5
        m = rng.randint(7, 10)
        cols = [rng.randrange(1, 1 << k) for _ in range(m)]
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(m)}
        M = rp.Matroid(m, rp.gf2_rank_fn(cols))
        if M.k == k and rp.opt(M, blk, k, {e: 0 for e in range(m)}) is not None:
            return M, blk, k


def uniform(rng):
    k = rng.randint(2, 4)
    m = rng.randint(k + 2, 9)
    blk = {e: (e if e < k else rng.randrange(k)) for e in range(m)}
    return rp.Matroid(m, lambda S: min(len(S), k)), blk, k


def weights(rng, m, style):
    if style == "ties":
        return {e: Fraction(rng.randint(0, 3)) for e in range(m)}
    return rp.random_weights(rng, m)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    for name, fam in [("uniform", uniform), ("arborescence6", arborescence6),
                      ("rainbow tree6", rainbow_tree6), ("binary5", binary5)]:
        for style in ("generic", "ties"):
            ok = eq = lt = gt = 0
            hist = {}
            fail = None
            for _ in range(trials):
                M, blk, k = fam(rng)
                w = weights(rng, M.m, style)
                val, p, st = run(M, blk, k, w, "local")
                target = rp.opt(M, blk, k, w)
                ok += (val == target)
                eq += st["eq"]; lt += st["lt"]; gt += st["gt"]
                for u in st["apps"]:
                    hist[u] = hist.get(u, 0) + 1
                if val != target and fail is None:
                    fail = (k, st["apps"], str(val), str(target))
            print(f"{name:14s} {style:7s} optimal {ok}/{trials}  gain =,>,< {eq},{gt},{lt}  "
                  f"apps/stage histogram {dict(sorted(hist.items()))}  first fail {fail}", flush=True)


if __name__ == "__main__":
    main()
