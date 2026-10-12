"""Hill climbing for long PO-SL epochs against a candidate bound.

Objective: max over the epochs of the schedule from p = 0 of (n - bound(epoch)),
ties broken by n.  Bounds: see ep_common.BOUNDS.
Instances: graphic (n vertices, k = n - 1) or binary (rank n), m elements,
exponential integer weights (midpoint and doubling moves, as in stage_search_exp).
Usage: python ep_search.py kind n m budget workers bound [bits] [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc, mutate
from ep_common import epochs, BOUNDS

BOUND = "m"


def score(desc):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return None
    try:
        eps, _ = epochs(M, blk, k, list(w), cap=600)
    except RuntimeError:
        return None
    f = BOUNDS[BOUND]
    best = None
    for e in eps:
        key = (e["n"] - f(e), e["n"])
        if best is None or key > best[0]:
            best = (key, (e["n"], e["r"], e["rho"], e["U"], e["R"]))
    return best


def mutate2(desc, rng, bits):
    kind, data, blk, w = desc
    if kind == "graphic" and rng.random() < 0.15:
        n, edges = data
        edges = list(edges)
        i, j = rng.randrange(len(edges)), rng.randrange(len(edges))
        edges[i] = edges[j]          # make i parallel to j
        return (kind, (n, edges), list(blk), list(w))
    if rng.random() < 0.1:
        w = list(w)
        i, j = rng.randrange(len(w)), rng.randrange(len(w))
        w[i] = w[j] + rng.choice([-1, 1]) * (1 << rng.randrange(bits))
        w[i] = max(0, w[i])
        return (kind, data, list(blk), w)
    return mutate(desc, rng, bits)


def _init(b):
    global BOUND
    BOUND = b


def hill(args):
    seed, kind, n, m, budget, bits = args
    rng = random.Random(seed)
    t0 = time.time()
    best = ((-999, 0), None, None)
    while time.time() - t0 < budget:
        cur = random_desc(rng, kind, n, m, bits)
        s = score(cur)
        if s is None:
            continue
        stall = 0
        while stall < 800 and time.time() - t0 < budget:
            cand = mutate2(cur, rng, bits)
            s2 = score(cand)
            stall += 1
            if s2 is None:
                continue
            if s2[0] >= s[0]:
                if s2[0] > s[0]:
                    stall = 0
                cur, s = cand, s2
        if s[0] > best[0]:
            best = (s[0], s[1], cur)
    return best


if __name__ == "__main__":
    kind, n, m, budget, workers, bound = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                          float(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
    bits = int(sys.argv[7]) if len(sys.argv) > 7 else 24
    seed0 = int(sys.argv[8]) if len(sys.argv) > 8 else 1000
    with Pool(workers, initializer=_init, initargs=(bound,)) as pool:
        res = pool.map(hill, [(s, kind, n, m, budget, bits) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"kind={kind} n={n} m={m} budget={budget} bound={bound} bits={bits}")
    for key, info, desc in res[:6]:
        print("score", key, "(n,r,rho,|U|,|R|)", info, "desc", desc)
    sys.stdout.flush()
