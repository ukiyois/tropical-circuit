import random, sys, time
import lsu_core as uc, ls_core as lc, stage_core as sc, lsu_trace as tr
from lsu_blockconst import rand_x
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "pure_steps":0, "pure_noend":0, "reg_stages":0, "reg_stage_gt_r":0, "reg_epoch_gt1":0, "reg_updates":0}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        x = rand_x(rng, k)
        w = [x[blk[e]] for e in range(M.m)]
        t = tr.trace(M, blk, k, w)
        st["runs"] += 1
        for s in t:
            if len({nu for _, _, nu, _ in s["pcs"]}) == 1:
                st["pure_steps"] += 1
                if s["nu1"] == s["nu0"] and s["S1"] == s["S0"]:
                    st["pure_noend"] += 1; ex.setdefault("pure_noend", (uc.describe(M), blk, x))
        # regular schedule
        v = list(w)
        for r in range(1, k):
            tr_ = []
            nu0, S0 = sc.state(M, blk, k, v)
            if nu0 > r: continue
            c, v = sc.run_stage(M, blk, k, v, r, trace=tr_)
            st["reg_stages"] += 1; st["reg_updates"] += c
            if c > r: st["reg_stage_gt_r"] += 1; ex.setdefault("stage>r", (uc.describe(M), blk, x, r, c))
            for i in range(len(tr_) - 1):
                if tr_[i]["S0"] == tr_[i+1]["S0"]:
                    st["reg_epoch_gt1"] += 1; ex.setdefault("epoch>1", (uc.describe(M), blk, x, r)); break
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
