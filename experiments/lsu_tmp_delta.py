import random, sys, time
from multiprocessing import Pool
import stage_core as sc, lsu_trace as tr
from lsu_rankone import instance

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    cnt = {}; runs = 0; worst = {}
    while time.time() - t0 < 90:
        k, parts, blk, w = instance(rng); M = sc.partition(parts)
        trace = tr.trace(M, blk, k, w, cap=200)
        runs += 1
        for s in trace:
            if s["nu1"] == k: continue
            d = (s["nu1"] - s["nu0"], len(s["S1"]) - len(s["S0"]), s["nu0"], len(s["S0"]), k)
            cnt[d[:2]] = cnt.get(d[:2], 0) + 1
            worst.setdefault(d[:2], (parts, blk, w, d))
    return runs, cnt, worst

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(18000, 18004))
    tot = {}; runs = 0; wst = {}
    for r, c, wo in res:
        runs += r
        for kk, vv in c.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in wo.items(): wst.setdefault(kk, vv)
    print("runs", runs, "(dnu0, d|S0|) counts:", sorted(tot.items()))
    for kk in sorted(wst):
        if kk[0] <= 0 or kk[1] < 0: print(kk, wst[kk][3])
