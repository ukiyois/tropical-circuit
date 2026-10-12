import random, sys, time
from multiprocessing import Pool
import stage_core as sc, lsu_trace as tr, lsu_core as uc
from lsu_rankone import instance

def work(args):
    seed, budget, mode = args
    rng = random.Random(seed); t0 = time.time()
    st = {"runs": 0, "steps": 0, "phi_fail": 0, "phi_fail_pure": 0}
    ex = {}
    while time.time() - t0 < budget:
        if mode == "rank1":
            k, parts, blk, w = instance(rng); M = sc.partition(parts)
        else:
            kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=6, mmax=10)
        trace = tr.trace(M, blk, k, w, cap=200)
        st["runs"] += 1
        for s in trace:
            if s["nu1"] == k: continue
            st["steps"] += 1
            if s["nu1"] + len(s["S1"]) <= s["nu0"] + len(s["S0"]):
                st["phi_fail"] += 1
                st["phi_fail_pure"] += len({nu for _, _, nu, _ in s["pcs"]}) == 1
                ex.setdefault("fail", (uc.describe(M) if mode != "rank1" else parts, blk, w, s["nu0"], sorted(s["S0"]), s["nu1"], sorted(s["S1"])))
    return st, ex

if __name__ == "__main__":
    mode = sys.argv[1]
    with Pool(2) as pool: res = pool.map(work, [(17000 + s, 60, mode) for s in range(2)])
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(mode, tot)
    for kk, vv in exs.items(): print(kk, vv)
