"""T_LS against the structure of the limit state v* (Section 4 picture).

For each LS run: v* = v_T; D* = sum over components K of (number of distinct values of v*
on the non-loops of K, minus 1) = the number of consecutive final gaps; V = number of
distinct values of w.  Records max(T - D*), max(T - V), and the histogram of T - D*.
Candidate: CAND  T_LS <= D* + 2.   False variant: FALSE  T_LS <= D*.
Usage: python lsu_finalgaps.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import lsu_core as uc


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "CAND": 0, "FALSE": 0, "max_T_minus_Dstar": -99, "max_T_minus_V": -99}
    hist = {}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        T = len(blocks)
        vstar = states[-1]["v"]
        D = 0
        for c in range(M.ncomp):
            vals = {vstar[e] for e in range(M.m) if M.comp[e] == c and M.rank(1 << e) > 0}
            D += max(len(vals) - 1, 0)
        V = len(set(w))
        st["runs"] += 1
        hist[T - D] = hist.get(T - D, 0) + 1
        if T - D > st["max_T_minus_Dstar"]:
            st["max_T_minus_Dstar"] = T - D
            ex["max_T_minus_Dstar"] = (uc.describe(M), blk, w, T, D)
        st["max_T_minus_V"] = max(st["max_T_minus_V"], T - V)
        if T > D + 2:
            st["CAND"] += 1
            ex.setdefault("CAND", (uc.describe(M), blk, w, T, D))
        if T > D:
            st["FALSE"] += 1
    return st, ex, hist


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 15000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs, hist = {}, {}, {}
    for st, ex, h in res:
        for key, val in st.items():
            tot[key] = max(tot.get(key, val), val) if key.startswith("max") else tot.get(key, 0) + val
        for key, val in ex.items():
            if key.startswith("max"):
                if key not in exs or val[3] - val[4] > exs[key][3] - exs[key][4]:
                    exs[key] = val
            else:
                exs.setdefault(key, val)
        for key, val in h.items():
            hist[key] = hist.get(key, 0) + val
    print(tot, flush=True)
    print("T - D* histogram:", sorted(hist.items()), flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
