"""Block-constant LS: do ties x_b = x_c persist, and does every step merge value classes?

State x in R^k (v_e = x_{blk e}).  Along the LS run record the partition of the blocks
by equal x-value.  Checks:
  H1  ties never break: x_b = x_c at step j implies x_b = x_c at step j + 1
  H2  every step except the last strictly coarsens the partition (merges classes)
  H3  T_LS <= (number of distinct values of x at the start)
  F   false variant: every step (including the last) leaves at most (classes - 1) classes
      ... and the false variant H2' "every step merges exactly two classes".
Usage: python lsu_bc_ties.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc
from lsu_blockconst import rand_x


def classes(x):
    return len(set(x))


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "steps": 0, "H1": 0, "H2": 0, "H3": 0, "F_exact2": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        x = rand_x(rng, k)
        w = [x[blk[e]] for e in range(M.m)]
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        st["runs"] += 1
        T = len(blocks)
        xs = [[x[b] - s["p"][b] for b in range(k)] for s in states]
        inst = (uc.describe(M), blk, x)
        for j in range(T):
            st["steps"] += 1
            a, b2 = xs[j], xs[j + 1]
            broke = any(a[b] == a[c] and b2[b] != b2[c] for b in range(k) for c in range(k))
            if broke:
                st["H1"] += 1
                ex.setdefault("H1", (inst, j, a, b2))
            if j < T - 1 and classes(b2) >= classes(a):
                st["H2"] += 1
                ex.setdefault("H2", (inst, j, a, b2))
            if classes(b2) != classes(a) - 1:
                st["F_exact2"] += 1
        if T > classes(x):
            st["H3"] += 1
            ex.setdefault("H3", (inst, T))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 5000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
