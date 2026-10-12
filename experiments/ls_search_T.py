"""Goal 3: hill climbing for long LS iterations (and for nu0 drops).

Objective (mode 'diff'): T_LS - (active updates of the regular schedule); mode 'T':
T_LS - m; mode 'drops': number of nu0 decreases along the LS run (tie-break T_LS).
Graphic matroids on n vertices with m edges, integer weights below 2^bits; moves:
midpoint, doubling/halving, random weight, block change, scaling by 2 plus noise.
Every final state is checked: Psi = Opt (brute force) and nu0 = k.
Usage: python ls_search_T.py n m bits seconds workers mode [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base


def evaluate(n, edges, blk, w, mode, cap=400):
    M = sc.graphic(n, edges)
    k = M.k
    if k < 4 or len(set(blk)) != k or max(blk) >= k or not has_rainbow_base(M, blk, k):
        return None
    try:
        lens, _ = lc.regular(M, blk, k, w, cap=2000)
    except RuntimeError:
        return None
    v = list(w)
    nu, _ = lc.nu_state(M, blk, k, v)
    T = 0
    drops = 0
    low = 0
    while nu < k:
        low += nu <= k - 2
        a, pcs, tau = lc.block(M, blk, k, v, k - 1)
        v = lc.shift(v, blk, a)
        T += 1
        nu2, _ = lc.nu_state(M, blk, k, v)
        drops += nu2 < nu
        nu = nu2
        if T > cap:
            return (10 ** 6, T, sum(lens), drops, "cap")
    reg = sum(lens)
    if mode == "diff":
        obj = T - reg
    elif mode == "T":
        obj = T - M.m
    elif mode == "low":
        obj = low
    elif mode == "overmax":
        obj = T - max(lens)
    elif mode == "second":
        srt = sorted(lens, reverse=True)
        obj = (srt[1] if len(srt) > 1 else 0) * 100 + sum(lens)
    elif mode == "lowdiff":
        obj = low - sum(lens[:-1])
    else:
        obj = drops * 1000 + T
    return (obj, T, reg, drops, "ok", tuple(lens))


def mutate(w, blk, rng, k, bits):
    w, blk = list(w), list(blk)
    op = rng.random()
    e = rng.randrange(len(w))
    if op < 0.3:
        f, g = rng.randrange(len(w)), rng.randrange(len(w))
        w[e] = (w[f] + w[g]) // 2
    elif op < 0.5:
        w[e] = min(2 * w[e], (1 << bits) - 1) if rng.random() < 0.5 else w[e] // 2
    elif op < 0.7:
        w[e] = rng.randrange(1 << rng.randint(1, bits))
    elif op < 0.85:
        blk[e] = rng.randrange(k)
    else:
        w = [min((x << 1) | rng.randint(0, 1), (1 << bits) - 1) for x in w]
    return w, blk


def hill(args):
    n, m, bits, budget, mode, seed = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None)
    while time.time() - t0 < budget:
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        M = sc.graphic(n, edges)
        k = M.k
        blk = [rng.randrange(k) for _ in range(m)]
        w = [rng.randrange(1 << bits) for _ in range(m)]
        res = evaluate(n, edges, blk, w, mode)
        if res is None:
            continue
        s = res[0]
        stall = 0
        while stall < 200 and time.time() - t0 < budget:
            w2, b2 = mutate(w, blk, rng, k, bits)
            r2 = evaluate(n, edges, b2, w2, mode)
            stall += 1
            if r2 is None:
                continue
            if r2[0] >= s:
                if r2[0] > s:
                    stall = 0
                w, blk, s, res = w2, b2, r2[0], r2
        if s > best[0]:
            M = sc.graphic(n, edges)
            opt = sc.opt_rainbow(M, blk, M.k, w)
            c, vl, nus, mono = lc.ls_iterate(M, blk, M.k, w, cap=500)
            psi = sc.psi_from_v(M, blk, M.k, w, vl)
            best = (s, (edges, blk, w, res, psi == opt, nus))
    return best


if __name__ == "__main__":
    n, m, bits, budget, workers, mode = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                                         float(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
    seed0 = int(sys.argv[7]) if len(sys.argv) > 7 else 21000
    with Pool(workers) as pool:
        res = pool.map(hill, [(n, m, bits, budget, mode, seed0 + s) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    for s, inst in res:
        if inst:
            print(f"objective {s}: T_LS={inst[3][1]} regular={inst[3][2]} stages={inst[3][5] if len(inst[3]) > 5 else ''} drops={inst[3][3]} "
                  f"Psi=Opt:{inst[4]} nu0 seq {inst[5]}", flush=True)
    print("best:", res[0][1], flush=True)
