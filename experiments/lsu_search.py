"""Hill climbing for long LS runs, by objective, at a given bit length.

Objectives (computed on the LS run from p = 0):
  T      T_LS - m
  low    number of LS steps at states with nu0 <= k - 2
  mis    number of LS steps with a mismatch at a jump (nu(L(t_i)) < nu(N(t_i)))
  nonpure number of LS steps whose block has more than one nu-level below tau
  drops  1000 * (number of decreases of nu0) + T
Matroids: graphic on n vertices with m edges ('g'), or binary of rank n with m columns ('b').
Every best instance is re-run and checked: Psi = Opt (brute force), nu0 = k at the end.
Usage: python lsu_search.py kind n m bits seconds workers objective [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_trace as tr
from ls_mono_random import has_rainbow_base


def build(kind, n, data):
    return sc.graphic(n, data) if kind == "g" else sc.gf2(data)


def evaluate(M, blk, w, obj, cap=300):
    k = M.k
    if len(set(blk)) != k or max(blk) >= k or not has_rainbow_base(M, blk, k):
        return None
    v = list(w)
    nu, _ = lc.nu_state(M, blk, k, v)
    T = low = mis = nonpure = drops = 0
    nus = [nu]
    while nu < k:
        st = tr.step_info(M, blk, k, v)
        T += 1
        low += st["nu0"] <= k - 2
        mis += st["mismatch"]
        nonpure += len({nu_ for _, _, nu_, _ in st["pcs"]}) > 1
        drops += st["nu1"] < st["nu0"]
        v = st["v2"]
        nu = st["nu1"]
        nus.append(nu)
        if T > cap:
            return (10 ** 6, T, low, mis, nonpure, drops, nus)
    val = {"T": T - M.m, "low": low, "mis": mis, "nonpure": nonpure,
           "drops": 1000 * drops + T}[obj]
    return (val, T, low, mis, nonpure, drops, nus)


def mutate(w, blk, rng, k, bits):
    w, blk = list(w), list(blk)
    op = rng.random()
    e = rng.randrange(len(w))
    top = (1 << bits) - 1
    if op < 0.3:
        f, g = rng.randrange(len(w)), rng.randrange(len(w))
        w[e] = (w[f] + w[g]) // 2
    elif op < 0.5:
        w[e] = min(2 * w[e], top) if rng.random() < 0.5 else w[e] // 2
    elif op < 0.65:
        w[e] = rng.randrange(1 << rng.randint(1, bits))
    elif op < 0.8:
        blk[e] = rng.randrange(k)
    elif op < 0.9:
        f = rng.randrange(len(w))
        w[e] = max(0, min(top, w[f] + rng.choice([-1, 1]) * rng.randint(0, 3)))
    else:
        w = [min((x << 1) | rng.randint(0, 1), top) for x in w]
    return w, blk


def rand_data(kind, n, m, rng):
    if kind == "g":
        return [tuple(rng.sample(range(n), 2)) for _ in range(m)]
    return [rng.randint(1, (1 << n) - 1) for _ in range(m)]


def hill(args):
    kind, n, m, bits, budget, obj, seed = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None)
    while time.time() - t0 < budget:
        data = rand_data(kind, n, m, rng)
        M = build(kind, n, data)
        k = M.k
        if k < 3:
            continue
        blk = [rng.randrange(k) for _ in range(m)]
        w = [rng.randrange(1 << bits) for _ in range(m)]
        res = evaluate(M, blk, w, obj)
        if res is None:
            continue
        s = res[0]
        stall = 0
        while stall < 250 and time.time() - t0 < budget:
            w2, b2 = mutate(w, blk, rng, k, bits)
            r2 = evaluate(M, b2, w2, obj)
            stall += 1
            if r2 is None:
                continue
            if r2[0] >= s:
                if r2[0] > s:
                    stall = 0
                w, blk, s, res = w2, b2, r2[0], r2
        if s > best[0]:
            opt = sc.opt_rainbow(M, blk, k, w)
            c, vl, nus, mono = lc.ls_iterate(M, blk, k, w, cap=500)
            psi = sc.psi_from_v(M, blk, k, w, vl)
            best = (s, (data, blk, w, res, psi == opt))
    return best


if __name__ == "__main__":
    kind, n, m, bits, budget, workers, obj = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                              int(sys.argv[4]), float(sys.argv[5]),
                                              int(sys.argv[6]), sys.argv[7])
    seed0 = int(sys.argv[8]) if len(sys.argv) > 8 else 31000
    with Pool(workers) as pool:
        res = pool.map(hill, [(kind, n, m, bits, budget, obj, seed0 + s) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    print(f"# lsu_search {kind} n={n} m={m} bits={bits} obj={obj} budget={budget} workers={workers}")
    for s, inst in res:
        if inst:
            data, blk, w, r, ok = inst
            print(f"objective {s}: T={r[1]} low={r[2]} mis={r[3]} nonpure={r[4]} drops={r[5]} "
                  f"Psi=Opt:{ok} nu0 seq {r[6]}", flush=True)
            print(f"   data={data} blk={blk} w={w}", flush=True)
