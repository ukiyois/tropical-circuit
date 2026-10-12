"""Goal 2: how often does the dangerous configuration occur along a multi-stage block?

On every open interval (s0, s1) of the path of a stage-r block at a state with nu0 < r,
with L = M^{v(s)}, A = Av(N(s)) (the piece's raised blocks), f_L(Q) = |Q| - r_L(E_Q):
  MISMATCH   nu(L) < nu(N(s))
  C4FAIL     f_L(A) < k - nu(L)          (A does not maximize the deficiency of L;
                                          Lead 4's sufficient condition fails)
  AVL_IN_A   Av(L) subseteq A            (candidate invariant)
  DROP       nu(L(s+)) < nu(L(s))        (next open interval smaller)
Usage: python ls_lead4.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import random_matroid, random_v, has_rainbow_base


def Emask(blk, Q):
    return sc.mask_of(e for e in range(len(blk)) if blk[e] in Q)


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"multi": 0, "intervals": 0, "MISMATCH": 0, "C4FAIL": 0, "C4FAIL_noMISMATCH": 0,
          "AVL_NOT_IN_A": 0, "AVL_NOT_IN_A_mis": 0, "DROP": 0, "blocks_with_mismatch": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = random_matroid(rng)
        k = M.k
        if k < 4:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        v = random_v(rng, M.m)
        nu0, _ = lc.nu_state(M, blk, k, v)
        if nu0 >= k - 1:
            continue
        for r in range(nu0 + 1, k):
            st["multi"] += 1
            a, pcs, tau = lc.block(M, blk, k, v, r)
            prev = None
            had = False
            for item in lc.path_intervals(M, blk, k, v, pcs):
                if item[0] != "open":
                    continue
                _, s0, s1, vm, idx = item
                c0, c1, nuN, A = pcs[idx]
                L = sc.MinBase(M, vm)
                nuL, avL, _ = sc.rainbow_av(L, blk, k)
                st["intervals"] += 1
                fA = len(A) - L.rank(Emask(blk, A))
                inst = (kind, M.m, k, r, blk, v, getattr(M, "edges", None), getattr(M, "cols", None), s0, s1)
                if nuL < nuN:
                    st["MISMATCH"] += 1
                    had = True
                if fA < k - nuL:
                    st["C4FAIL"] += 1
                    ex.setdefault("C4FAIL", inst)
                    if nuL >= nuN:
                        st["C4FAIL_noMISMATCH"] += 1
                if not avL <= A:
                    st["AVL_NOT_IN_A"] += 1
                    if nuL < nuN:
                        st["AVL_NOT_IN_A_mis"] += 1
                        ex.setdefault("AVL_NOT_IN_A_mis", inst)
                if prev is not None and nuL < prev:
                    st["DROP"] += 1
                    ex.setdefault("DROP", inst)
                prev = nuL
            st["blocks_with_mismatch"] += had
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(9100 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
