"""Goal 3(b): T_LS against the regular schedule (active updates, longest stage) and R(k, m).

Random graphic / binary / uniform / paving / sum instances (k = 3..6, m <= 11), weights
small, spread, exponential and ladder-like.  Every LS run is checked to end at Opt.
Usage: python ls_stats.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_search_drop import rmat, rweights
from ls_mono_random import random_matroid, has_rainbow_base


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "lt": 0, "eq": 0, "gt": 0, "sumT": 0, "sumReg": 0, "maxT": 0, "maxReg": 0,
          "max_T_minus_reg": -99, "max_T_minus_maxstage": -99, "max_T_over_R": 0.0,
          "drops_runs": 0, "wrong": 0, "max_T_minus_m": -99}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = (rmat(rng) if rng.random() < 0.5 else random_matroid(rng))
        k = M.k
        if k < 3 or M.m > 11:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        w = rweights(rng, M.m)
        lens, vreg = lc.regular(M, blk, k, w)
        T, vls, nus, mono = lc.ls_iterate(M, blk, k, w)
        if sc.psi_from_v(M, blk, k, w, vls) != sc.psi_from_v(M, blk, k, w, vreg):
            st["wrong"] += 1
        reg = sum(lens)
        st["runs"] += 1
        st["lt"] += T < reg
        st["eq"] += T == reg
        st["gt"] += T > reg
        st["sumT"] += T
        st["sumReg"] += reg
        st["maxT"] = max(st["maxT"], T)
        st["maxReg"] = max(st["maxReg"], reg)
        st["drops_runs"] += not mono
        if T - reg > st["max_T_minus_reg"]:
            st["max_T_minus_reg"] = T - reg
            ex["T_minus_reg"] = (kind, M.m, k, blk, getattr(M, "edges", None), w, T, lens)
        st["max_T_minus_maxstage"] = max(st["max_T_minus_maxstage"], T - max(lens))
        st["max_T_minus_m"] = max(st["max_T_minus_m"], T - M.m)
        st["max_T_over_R"] = max(st["max_T_over_R"], T / lc.R_bound(k, M.m))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(51000 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            if key.startswith("max"):
                tot[key] = max(tot.get(key, val), val)
            else:
                tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
