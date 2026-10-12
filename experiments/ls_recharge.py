"""Open question of Section 6: can decreases of nu0 recur and lengthen the LS iteration?

Base: Instance LS-1 (graphic, 6 vertices, 10 edges, k = 5) plus 0 to 3 random extra
edges (random blocks), weights LS-1's scaled by 2^s plus random low bits and random
extra weights.  Hill climbing on (number of decreases) * 100 + (T_LS - regular),
with midpoint, doubling, random and block moves.  Every run checked: Psi = Opt.
Usage: python ls_recharge.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base

EDGES = [(2, 3), (5, 1), (1, 0), (4, 2), (5, 1), (5, 3), (0, 4), (0, 5), (1, 0), (2, 4)]
BLK = [0, 1, 1, 0, 2, 0, 3, 4, 3, 1]
W = [0, 3, 3, 0, 4, 0, 2, 2, 0, 4]


def evaluate(edges, blk, w):
    M = sc.graphic(6, edges)
    k = M.k
    if k != 5 or len(set(blk)) != k or not has_rainbow_base(M, blk, k):
        return None
    lens, _ = lc.regular(M, blk, k, w, cap=3000)
    v = list(w)
    nu, _ = lc.nu_state(M, blk, k, v)
    T = drops = 0
    while nu < k:
        a, pcs, tau = lc.block(M, blk, k, v, k - 1)
        v = lc.shift(v, blk, a)
        T += 1
        nu2, _ = lc.nu_state(M, blk, k, v)
        drops += nu2 < nu
        nu = nu2
        if T > 300:
            return (10 ** 6, T, sum(lens), drops)
    return (drops * 100 + T - sum(lens), T, sum(lens), drops)


def hill(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None)
    while time.time() - t0 < budget:
        extra = [tuple(rng.sample(range(6), 2)) for _ in range(rng.randint(0, 3))]
        edges = EDGES + extra
        blk = BLK + [rng.randrange(5) for _ in extra]
        s = rng.randint(0, 10)
        w = [(x << s) + rng.randrange(1 << s) if s else x for x in W] + \
            [rng.randrange(5 << s) for _ in extra]
        res = evaluate(edges, blk, w)
        if res is None:
            continue
        sc_, stall = res[0], 0
        while stall < 150 and time.time() - t0 < budget:
            w2, b2 = list(w), list(blk)
            e = rng.randrange(len(w2))
            op = rng.random()
            if op < 0.3:
                f, g = rng.randrange(len(w2)), rng.randrange(len(w2))
                w2[e] = (w2[f] + w2[g]) // 2
            elif op < 0.55:
                w2[e] = 2 * w2[e] if rng.random() < 0.5 else w2[e] // 2
            elif op < 0.8:
                w2[e] = rng.randrange(max(2, max(w2) + 1))
            else:
                b2[e] = rng.randrange(5)
            r2 = evaluate(edges, b2, w2)
            stall += 1
            if r2 is None:
                continue
            if r2[0] >= sc_:
                if r2[0] > sc_:
                    stall = 0
                w, blk, sc_, res = w2, b2, r2[0], r2
        if sc_ > best[0]:
            M = sc.graphic(6, edges)
            c, vl, nus, mono = lc.ls_iterate(M, blk, 5, w, cap=400)
            ok = sc.psi_from_v(M, blk, 5, w, vl) == sc.opt_rainbow(M, blk, 5, w)
            best = (sc_, (edges, blk, w, res, ok, nus))
    return best


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(hill, [(61000 + s, budget) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    for s, inst in res:
        if inst:
            print(f"objective {s}: T_LS={inst[3][1]} regular={inst[3][2]} drops={inst[3][3]} "
                  f"Psi=Opt:{inst[4]} nu0 seq {inst[5]}", flush=True)
    print("best:", res[0][1], flush=True)
