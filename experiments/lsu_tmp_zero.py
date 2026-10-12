import random, sys, time
import lsu_core as uc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "steps":0, "run_no_zero_block":0, "step_all_raised":0, "runs_T>=2":0}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        st["runs"] += 1
        if not blocks: continue
        st["runs_T>=2"] += len(blocks) >= 2
        if min(states[-1]["p"]) > 0:
            st["run_no_zero_block"] += 1; ex.setdefault("noZero", (uc.describe(M), blk, w, [s["p"] for s in states]))
        for bl in blocks:
            st["steps"] += 1
            if min(bl["a"]) > 0:
                st["step_all_raised"] += 1; ex.setdefault("allraised", (uc.describe(M), blk, w, bl["a"]))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
