"""Does the PO-SL stage length grow with m at fixed k = 3?  Hill-climb over
multigraphs on 4 vertices with exactly m edges (m fixed per worker), 3 colors,
integer weights in 0..W.  Score = longest stage (stages start at p = 0)."""
import random
import sys
import time
from multiprocessing import Pool
from core import *
from hill_long import stage_lengths


def score(edges, blk, w):
    M = graphic(4, edges)
    if M.k != 3 or len(set(blk)) != 3 or not has_rainbow(M, blk, 3):
        return None
    ex, lens, ok = stage_lengths(M, blk, 3, [Fraction(x) for x in w])
    if ex is None:
        return None
    if not ok:
        print("NON-OPTIMAL", edges, blk, w, flush=True)
    return max(lens)


def work(args):
    m, seed, budget, Wmax = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (0, None)
    while time.time() - t0 < budget:
        edges = [tuple(rng.sample(range(4), 2)) for _ in range(m)]
        blk = [i if i < 3 else rng.randrange(3) for i in range(m)]
        w = [rng.randrange(0, Wmax + 1) for _ in range(m)]
        sc = score(edges, blk, w)
        if sc is None:
            continue
        for _ in range(400):
            if time.time() - t0 > budget:
                break
            e2, b2, w2 = list(edges), list(blk), list(w)
            op = rng.random()
            i = rng.randrange(m)
            if op < 0.55:
                w2[i] = min(Wmax, max(0, w2[i] + rng.choice([-3, -1, 1, 3])))
            elif op < 0.8:
                b2[i] = rng.randrange(3)
            else:
                e2[i] = tuple(rng.sample(range(4), 2))
            s2 = score(e2, b2, w2)
            if s2 is not None and s2 >= sc:
                edges, blk, w, sc = e2, b2, w2, s2
        if sc > best[0]:
            best = (sc, (edges, blk, w))
    return m, best


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 150
    Wmax = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    ms = [6, 7, 8, 9, 10, 11]
    jobs = [(m, 100 * m + j, budget, Wmax) for m in ms for j in range(5)]
    with Pool(30) as pool:
        res = pool.map(work, jobs)
    for m in ms:
        bm = max((b for mm, b in res if mm == m), key=lambda x: x[0])
        print(f"m={m}: longest stage {bm[0]} (r+1 = 3)  instance {bm[1]}", flush=True)


if __name__ == "__main__":
    main()
