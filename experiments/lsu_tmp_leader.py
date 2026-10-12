import random, sys, time
import lsu_core as uc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "steps":0, "step_no_full":0, "run_no_persistent":0, "runs_T>=2":0}
    ex = {}
    while time.time() - t0 < 30:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        if not blocks: continue
        st["runs"] += 1
        full = [set(b for b in range(k) if bl["a"][b] == bl["tau"]) for bl in blocks]
        for j, f in enumerate(full):
            st["steps"] += 1
            if not f:
                st["step_no_full"] += 1; ex.setdefault("nofull", (uc.describe(M), blk, w, j, blocks[j]["a"], blocks[j]["tau"]))
        if len(blocks) >= 2:
            st["runs_T>=2"] += 1
            if not set.intersection(*full):
                st["run_no_persistent"] += 1; ex.setdefault("nopers", (uc.describe(M), blk, w, [bl["a"] for bl in blocks]))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
