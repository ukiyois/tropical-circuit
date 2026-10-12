"""Test: does the LS iteration stay below the least nonnegative dual optimum p0?

For random instances: run LS from p = 0, compute p0 (lsu_core.least_dual with an
optimal rainbow base), and check
  BELOW   p_j <= p0 componentwise at every state j       (candidate)
  LIMIT   p_T == p0 at the end                            (implied by BELOW)
  FALSE1  p_j <= p0 - (p0 - p_{j-1})/2 ... (a false strengthening: half-way rule)
Also records, per run, T, k, m.
Usage: python lsu_overshoot.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import lsu_core as uc


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "states": 0, "BELOW_fail": 0, "LIMIT_fail": 0, "FALSE1_fail": 0,
          "maxT": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w = uc.rand_instance(rng)
        bases = uc.all_bases(M)
        ob = uc.opt_rainbow_base(M, blk, k, w, bases)
        p0 = uc.least_dual(M, blk, k, w, ob[1])
        assert p0 is not None and min(p0) == 0
        states, blocks = uc.ls_run(M, blk, k, w)
        st["runs"] += 1
        st["maxT"] = max(st["maxT"], len(blocks))
        inst = (uc.describe(M), blk, w)
        bad = False
        for j, s in enumerate(states):
            st["states"] += 1
            if any(s["p"][b] > p0[b] for b in range(k)):
                bad = True
                ex.setdefault("BELOW", (inst, j, s["p"], p0))
            if j >= 1:
                prev = states[j - 1]["p"]
                # false: each step closes at least half of the remaining distance in every block
                if any(2 * s["p"][b] < p0[b] + prev[b] for b in range(k)):
                    st["FALSE1_fail"] += 1
        st["BELOW_fail"] += bad
        if states[-1]["p"] != p0:
            st["LIMIT_fail"] += 1
            ex.setdefault("LIMIT", (inst, states[-1]["p"], p0))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = max(tot.get(key, val), val) if key.startswith("max") else tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
