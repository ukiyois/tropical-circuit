"""T_LS against the number V of distinct values of w (weights drawn from few values).

Random instances (lsu_core.rand_instance matroids and blocks, k = 3..7, m <= 12), weights
chosen from V0 random values (V0 = 2..6, of 3, 10 or 20 bits).  Records T_LS by V.
Observation tested: OBS  T_LS <= V + 1.   False variant: FALSE  T_LS <= V.
Also checks Psi = Opt at the end (brute force).
Usage: python lsu_fewvalues.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "OBS": 0, "FALSE": 0, "OPT": 0}
    hist = {}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        nv = rng.randint(2, 6)
        vals = [rng.randrange(1 << rng.choice([3, 10, 20])) for _ in range(nv)]
        w = [rng.choice(vals) for _ in range(M.m)]
        T, vl, nus, mono = lc.ls_iterate(M, blk, k, w, cap=400)
        V = len(set(w))
        st["runs"] += 1
        hist[(V, T)] = hist.get((V, T), 0) + 1
        if T > V + 1:
            st["OBS"] += 1
            ex.setdefault("OBS", (uc.describe(M), blk, w, T))
        if T > V:
            st["FALSE"] += 1
            ex.setdefault("FALSE", (uc.describe(M), blk, w, T, nus))
        if sc.psi_from_v(M, blk, k, w, vl) != sc.opt_rainbow(M, blk, k, w):
            st["OPT"] += 1
    return st, ex, hist


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 14000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs, hist = {}, {}, {}
    for st, ex, h in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
        for key, val in h.items():
            hist[key] = hist.get(key, 0) + val
    print(tot, flush=True)
    for V in sorted({a for a, _ in hist}):
        print("V", V, "T histogram", sorted((T, n) for (a, T), n in hist.items() if a == V), flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
