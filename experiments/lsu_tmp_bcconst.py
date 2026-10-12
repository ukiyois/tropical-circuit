import random, sys, time
import lsu_core as uc
from lsu_blockconst import rand_x
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "const_final":0, "cf_steps":0, "cf_H2fail":0, "cf_T_gt_k1":0, "cf_maxT_minus_vals":-9}
    ex = {}
    while time.time() - t0 < 25:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        x = rand_x(rng, k); w = [x[blk[e]] for e in range(M.m)]
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        st["runs"] += 1
        xs = [[x[b]-s["p"][b] for b in range(k)] for s in states]
        if len(set(xs[-1])) == 1 and blocks:
            st["const_final"] += 1
            T = len(blocks)
            st["cf_maxT_minus_vals"] = max(st["cf_maxT_minus_vals"], T - (len(set(x)) - 1))
            for j in range(T - 1):
                st["cf_steps"] += 1
                if len(set(xs[j+1])) >= len(set(xs[j])):
                    st["cf_H2fail"] += 1; ex.setdefault("H2", (uc.describe(M), blk, x, xs))
    return st, ex

if __name__ == "__main__":
    with Pool(2) as pool: res = pool.map(work, range(2))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = max(tot.get(kk, vv), vv) if kk.startswith("cf_max") else tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
