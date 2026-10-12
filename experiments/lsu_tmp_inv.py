import random, sys, time
from multiprocessing import Pool
import stage_core as sc, lsu_trace as tr
from lsu_rankone import instance

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs": 0, "states": 0, "INV": 0, "INV_F": 0, "Tk1": 0}
    ex = {}
    while time.time() - t0 < 100:
        k, parts, blk, w = instance(rng); M = sc.partition(parts)
        t = tr.trace(M, blk, k, w, cap=200)
        st["runs"] += 1
        if len(t) > k - 1: st["Tk1"] += 1
        for j, s in enumerate(t):
            st["states"] += 1
            if len(s["S0"]) < j + 1:
                st["INV"] += 1; ex.setdefault("INV", (parts, blk, w, j, [ (x["nu0"], sorted(x["S0"])) for x in t]))
            if len(s["S0"]) < j + 2:
                st["INV_F"] += 1
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(19100, 19104))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
