"""LS iteration on block-constant weights w_e = x_{blk(e)}.

Every LS run has v_j = v* + (p* - p_j)_blk with v* = w - p*_blk the limit state, so near
its end an LS run is an LS run on M^{v*} with block-constant weights.  Here M itself
gets block-constant weights x (random, various bit lengths, with ties).  Records T_LS
against k, m and the bit length; checks Psi = Opt = sum_b x_b at the end.
Usage: python lsu_blockconst.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc
from ls_mono_random import has_rainbow_base


def rand_x(rng, k):
    st = rng.choice(["small", "bits8", "bits20", "exp", "ladder"])
    if st == "small":
        return [rng.randint(0, 4) for _ in range(k)]
    if st == "bits8":
        return [rng.randrange(256) for _ in range(k)]
    if st == "bits20":
        return [rng.randrange(1 << 20) for _ in range(k)]
    if st == "exp":
        return [rng.choice([0, 1 << rng.randint(0, 20)]) for _ in range(k)]
    return [rng.choice([0, 1, 2]) * (1 << rng.randint(0, 10)) + rng.randint(0, 1) for _ in range(k)]


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "maxT": 0, "maxT_minus_k": -99, "wrong": 0, "drops": 0}
    hist = {}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        x = rand_x(rng, k)
        w = [x[blk[e]] for e in range(M.m)]
        c, vl, nus, mono = lc.ls_iterate(M, blk, k, w, cap=400)
        st["runs"] += 1
        st["drops"] += not mono
        if sc.psi_from_v(M, blk, k, w, vl) != sum(x):
            st["wrong"] += 1
        hist[(k, c)] = hist.get((k, c), 0) + 1
        if c > st["maxT"]:
            st["maxT"] = c
            ex["maxT"] = (uc.describe(M), blk, x, c, nus)
        if c - k > st["maxT_minus_k"]:
            st["maxT_minus_k"] = c - k
            ex["maxT_minus_k"] = (uc.describe(M), blk, x, c, nus)
    return st, ex, hist


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs, hist = {}, {}, {}
    for st, ex, h in res:
        for key, val in st.items():
            tot[key] = max(tot.get(key, val), val) if key.startswith("max") else tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
        for key, val in h.items():
            hist[key] = hist.get(key, 0) + val
    print(tot, flush=True)
    for kk in sorted({a for a, _ in hist}):
        print("k", kk, "T histogram", sorted((c, n) for (a, c), n in hist.items() if a == kk))
    for key, val in exs.items():
        print(key, val, flush=True)
