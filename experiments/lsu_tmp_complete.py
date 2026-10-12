import random, sys, time
import lsu_core as uc
from lsu_blockconst import rand_x
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"bc_runs":0, "bc_steps":0, "bc_nocomplete":0, "gen_runs":0, "gen_steps":0, "gen_nocomplete":0}
    ex = {}
    while time.time() - t0 < 25:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        for mode in ("bc", "gen"):
            if mode == "bc":
                x = rand_x(rng, k); w = [x[blk[e]] for e in range(M.m)]
            else:
                w = w0
            states, blocks = uc.ls_run(M, blk, k, w, cap=400)
            if not blocks: continue
            st[mode + "_runs"] += 1
            pT = states[-1]["p"]
            for j in range(len(blocks)):
                st[mode + "_steps"] += 1
                pj, pj1 = states[j]["p"], states[j+1]["p"]
                if not any(pj[b] < pT[b] and pj1[b] == pT[b] for b in range(k)):
                    st[mode + "_nocomplete"] += 1
                    ex.setdefault(mode, (uc.describe(M), blk, w, j, [s["p"] for s in states]))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
