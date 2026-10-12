import random, sys, time
import lsu_core as uc, ls_core as lc, stage_core as sc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    st = {"steps":0, "minblock_raised":0, "minblock_raised_comp":0, "cocirc_fail":0, "runs":0, "Zfinal_has_minblock0":0}
    ex = {}
    while time.time() - t0 < 40:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        if not blocks: continue
        st["runs"] += 1
        nonloop = [e for e in range(M.m) if M.rank(1 << e) > 0]
        mn = min(w[e] for e in nonloop)
        b0s = {blk[e] for e in nonloop if w[e] == mn}
        if any(states[-1]["p"][b] == 0 for b in b0s): st["Zfinal_has_minblock0"] += 1
        for j, bl in enumerate(blocks):
            st["steps"] += 1
            v = states[j]["v"]
            mnv = min(v[e] for e in nonloop)
            bm = {blk[e] for e in nonloop if v[e] == mnv}
            if all(bl["a"][b] > 0 for b in bm):
                st["minblock_raised"] += 1; ex.setdefault("minraised", (uc.describe(M), blk, w, j, v, bl["a"]))
            # per component: blocks of the minimum elements of each component
            ok = False
            for c in range(M.ncomp):
                el = [e for e in nonloop if M.comp[e] == c]
                if not el: continue
                mc = min(v[e] for e in el)
                if any(bl["a"][blk[e]] == 0 for e in el if v[e] == mc): ok = True
            if not ok: st["minblock_raised_comp"] += 1
            # cocircuit criterion at the last piece: some b with every base of N(tau^-) meeting R_b
            c0, c1, nu, A = bl["pcs"][-1]
            N = sc.posl(M, v, c0)
            zero = [b for b in range(k) if bl["a"][b] == 0]
            if not any(N.rank(sum(1 << e for e in range(M.m) if blk[e] != b)) < k for b in zero):
                st["cocirc_fail"] += 1; ex.setdefault("cocirc", (uc.describe(M), blk, w, j))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; exs = {}
    for st, ex in res:
        for kk, vv in st.items(): tot[kk] = tot.get(kk, 0) + vv
        for kk, vv in ex.items(): exs.setdefault(kk, vv)
    print(tot)
    for kk, vv in exs.items(): print(kk, vv)
