import random, sys, time
import lsu_core as uc
import ls_core as lc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "T_gt_V":0, "T_gt_V_comp":0, "T_gt_V+1":0}
    hist = {}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        nv = rng.randint(2, 6)
        vals = [rng.randrange(1 << rng.choice([3, 10, 20])) for _ in range(nv)]
        w = [rng.choice(vals) for _ in range(M.m)]
        c, vl, nus, mono = lc.ls_iterate(M, blk, k, w, cap=400)
        V = len(set(w))
        st["runs"] += 1
        hist[(V, c)] = hist.get((V, c), 0) + 1
        if c > V:
            st["T_gt_V"] += 1; ex.setdefault("T>V", (uc.describe(M), blk, w, c, nus))
        if c > V + 1:
            st["T_gt_V+1"] += 1; ex.setdefault("T>V+1", (uc.describe(M), blk, w, c, nus))
    return st, ex, hist

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}; hist = {}
    for st, ex, h in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
        for kk, vv in h.items(): hist[kk] = hist.get(kk, 0) + vv
    print(tot)
    for V in sorted({a for a, _ in hist}): print("V", V, sorted((c, n) for (a, c), n in hist.items() if a == V))
    for kk, vv in exs.items(): print(kk, vv)
