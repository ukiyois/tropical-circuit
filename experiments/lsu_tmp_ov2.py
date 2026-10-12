import random, sys, time
sys.path.insert(0, '.')
import lsu_core as uc
from multiprocessing import Pool

def work(seed):
    rng = random.Random(seed)
    t0 = time.time()
    st = {}
    ex = []
    while time.time() - t0 < 30:
        kind, M, blk, k, w = uc.rand_instance(rng)
        bases = uc.all_bases(M)
        ob = uc.opt_rainbow_base(M, blk, k, w, bases)
        p0 = uc.least_dual(M, blk, k, w, ob[1])
        states, blocks = uc.ls_run(M, blk, k, w)
        conn = M.ncomp - sum(1 for e in range(M.m) if M.rank(1 << e) == 0)
        # count non-loop components
        comps = {M.comp[e] for e in range(M.m) if M.rank(1 << e) > 0}
        key = (kind, len(comps) > 1)
        bad = any(s["p"][b] > p0[b] for s in states for b in range(k))
        c = st.setdefault(key, [0, 0])
        c[0] += 1
        c[1] += bad
        if bad and len(comps) == 1 and len(ex) < 2:
            ex.append((uc.describe(M), blk, w, [s["p"] for s in states], p0))
    return st, ex

if __name__ == "__main__":
    with Pool(4) as pool:
        res = pool.map(work, range(4))
    tot = {}
    exs = []
    for st, ex in res:
        for kk, (a, b) in st.items():
            t = tot.setdefault(kk, [0, 0]); t[0] += a; t[1] += b
        exs += ex
    for kk in sorted(tot): print(kk, tot[kk])
    for e in exs[:3]: print(e)
