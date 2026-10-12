import random, sys, time
import lsu_core as uc
from lsu_blockconst import rand_x
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "steps":0, "H4_newval":0, "H4b_sub":0, "Gen_diff":0, "gen_steps":0, "Gen_diff_cur":0}
    ex = {}
    while time.time() - t0 < 30:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        x = rand_x(rng, k)
        w = [x[blk[e]] for e in range(M.m)]
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        st["runs"] += 1
        V0 = set(x)
        for j in range(len(blocks)):
            st["steps"] += 1
            xj = [x[b]-states[j]["p"][b] for b in range(k)]
            xj1 = [x[b]-states[j+1]["p"][b] for b in range(k)]
            if not set(xj1) <= set(xj):
                st["H4b_sub"] += 1; ex.setdefault("H4b", (uc.describe(M), blk, x, j, xj, xj1))
            if not set(xj1) <= V0:
                st["H4_newval"] += 1
        # general weights: is each a_b a difference v_e - v_f with e in block b (current values)?
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        for j, bl in enumerate(blocks):
            v = states[j]["v"]
            st["gen_steps"] += 1
            for b in range(k):
                ab = bl["a"][b]
                if ab == 0: continue
                diffs = {v[e]-v[f] for e in range(M.m) if blk[e]==b for f in range(M.m)}
                if ab not in diffs:
                    st["Gen_diff"] += 1; ex.setdefault("Gen", (uc.describe(M), blk, w, j, b, ab)); break
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
