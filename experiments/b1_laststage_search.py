"""B1 (exploratory): hill climbing against the last-stage block on general matroids.

Objective: 10^6 if the iteration of the last-stage block (b1_laststage_general)
decreases nu0, gets stuck, or ends away from Opt; otherwise the number of
last-stage updates minus the number of updates of the regular PO-SL schedule.
Moves: midpoint and doubling moves on the weights (they build ladders), random
weights, block changes.  Graphic matroids on 5 and 6 vertices, m <= 10.
Usage: python b1_laststage_search.py budget_seconds workers"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from b1_laststage_general import last_block


def evaluate(n, edges, blk, w):
    M = sc.graphic(n, edges)
    k = M.k
    if k < 3 or len(set(blk)) < k or max(blk) >= k:
        return None
    bases = sc.all_bases(M)
    opt = sc.opt_rainbow(M, blk, k, w, bases)
    if opt is None:
        return None
    try:
        lens, _ = sc.run_schedule(M, blk, k, w, cap=500)
    except RuntimeError:
        return None
    v, p, upd = list(w), [0] * k, 0
    nu_prev = sc.state(M, blk, k, v)[0]
    while True:
        nu0 = sc.state(M, blk, k, v)[0]
        if nu0 < nu_prev:
            return (10 ** 6, "nonmono", sum(lens), upd)
        nu_prev = nu0
        if nu0 >= k:
            break
        eta = last_block(M, blk, k, v)
        if not any(eta) or upd > 300:
            return (10 ** 6, "stuck", sum(lens), upd)
        v = [v[e] - eta[blk[e]] for e in range(M.m)]
        p = [p[b] + eta[b] for b in range(k)]
        upd += 1
    psi = sum(p) + sc.beta(M, v)
    if psi != opt:
        return (10 ** 6, "wrong", sum(lens), upd)
    return (upd - sum(lens), "ok", sum(lens), upd)


def mutate(w, blk, rng, k):
    w, blk = list(w), list(blk)
    op = rng.random()
    e = rng.randrange(len(w))
    if op < 0.35:
        f, g = rng.randrange(len(w)), rng.randrange(len(w))
        w[e] = (w[f] + w[g]) // 2
    elif op < 0.55:
        w[e] = 2 * w[e] if rng.random() < 0.5 else w[e] // 2
    elif op < 0.8:
        w[e] = rng.randrange(1 << rng.randint(1, 20))
    else:
        blk[e] = rng.randrange(k)
    return w, blk


def hill(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None)
    while time.time() - t0 < budget:
        n = rng.choice([5, 6])
        m = rng.randint(n + 1, 10)
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        M = sc.graphic(n, edges)
        k = M.k
        blk = [rng.randrange(k) for _ in range(m)]
        w = [rng.randrange(1 << 16) for _ in range(m)]
        res = evaluate(n, edges, blk, w)
        if res is None:
            continue
        s = res[0]
        stall = 0
        while stall < 150 and time.time() - t0 < budget:
            w2, b2 = mutate(w, blk, rng, k)
            r2 = evaluate(n, edges, b2, w2)
            stall += 1
            if r2 is None:
                continue
            if r2[0] >= s:
                if r2[0] > s:
                    stall = 0
                w, blk, s, res = w2, b2, r2[0], r2
            if s >= 10 ** 6:
                return (s, (n, edges, blk, w, res))
        if s > best[0]:
            best = (s, (n, edges, blk, w, res))
    return best


if __name__ == "__main__":
    budget, workers = float(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(hill, [(1500 + s, budget) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    for s, inst in res:
        print(f"objective {s}: {inst[4] if inst else None}", flush=True)
    print("best:", res[0][1], flush=True)
