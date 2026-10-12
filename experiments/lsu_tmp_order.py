import random, sys, time
import lsu_core as uc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "steps":0, "order_flip":0, "strict_to_tie_ok":0, "tie_break":0, "diff_grow":0}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        if not blocks: continue
        st["runs"] += 1
        pT = states[-1]["p"]
        xs = [[pT[b] - s["p"][b] for b in range(k)] for s in states]
        for j in range(len(blocks)):
            st["steps"] += 1
            a, c = xs[j], xs[j+1]
            fl = any(a[b] > a[d] and c[b] < c[d] for b in range(k) for d in range(k))
            tb = any(a[b] == a[d] and c[b] != c[d] for b in range(k) for d in range(k))
            gr = any(a[b] > a[d] and c[b] - c[d] > a[b] - a[d] for b in range(k) for d in range(k))
            if fl: st["order_flip"] += 1; ex.setdefault("flip", (uc.describe(M), blk, w, j, a, c))
            if tb: st["tie_break"] += 1; ex.setdefault("tiebreak", (uc.describe(M), blk, w, j, a, c))
            if gr: st["diff_grow"] += 1
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
