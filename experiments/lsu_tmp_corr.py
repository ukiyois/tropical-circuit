import random, sys, time
import lsu_core as uc, stage_core as sc
from multiprocessing import Pool

def sgn(x): return (x > 0) - (x < 0)

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"runs":0, "pairs":0, "uncorrect":0, "uncorrect_to_tie":0, "steps":0, "step_no_correction":0, "step_no_corr_not_last":0}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        if not blocks: continue
        st["runs"] += 1
        vs = [s["v"] for s in states]; vstar = vs[-1]; m = M.m; T = len(blocks)
        pairs = [(e, f) for e in range(m) for f in range(m) if e < f and M.comp[e] == M.comp[f] and blk[e] != blk[f] and vstar[e] != vstar[f]]
        st["pairs"] += len(pairs)
        corrected_at = {}
        for (e, f) in pairs:
            d = sgn(vstar[e] - vstar[f])
            good = [sgn(v[e] - v[f]) == d for v in vs]
            # once good, stays good?
            seen = False
            for j, g in enumerate(good):
                if g: seen = True
                elif seen:
                    st["uncorrect"] += 1
                    if vs[j][e] == vs[j][f]: st["uncorrect_to_tie"] += 1
                    ex.setdefault("uncorrect", (uc.describe(M), blk, w, (e, f), [ (v[e], v[f]) for v in vs]))
                    break
        for j in range(T):
            st["steps"] += 1
            # does step j correct some pair with nonzero final gap, or create a tie of a final-tie pair?
            corr = any(sgn(vs[j][e]-vs[j][f]) != sgn(vstar[e]-vstar[f]) and sgn(vs[j+1][e]-vs[j+1][f]) == sgn(vstar[e]-vstar[f]) for (e, f) in pairs)
            if not corr:
                st["step_no_correction"] += 1
                if j < T - 1: st["step_no_corr_not_last"] += 1; ex.setdefault("nocorr", (uc.describe(M), blk, w, j))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
