import random, sys, time
import lsu_core as uc, ls_core as lc, stage_core as sc
from multiprocessing import Pool

def sgn(x): return (x > 0) - (x < 0)

def flips(M, blk, k, w):
    states, blocks = uc.ls_run(M, blk, k, w, cap=400)
    m = M.m
    maxf = 0; cnt = {}
    for e in range(m):
        for f in range(e+1, m):
            if M.comp[e] != M.comp[f] or blk[e] == blk[f]: continue
            seq = [sgn(s["v"][e]-s["v"][f]) for s in states]
            # count reversals of strict order: +..-.. or -..+..
            strict = [x for x in seq if x != 0]
            rev = sum(1 for a, b in zip(strict, strict[1:]) if a != b)
            cnt[rev] = cnt.get(rev, 0) + 1
            maxf = max(maxf, rev)
    return len(blocks), maxf, cnt

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    tot = {}; mx = 0; ex = None; runs = 0
    while time.time() - t0 < 40:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=4, kmax=7, mmax=12)
        T, maxf, cnt = flips(M, blk, k, w)
        runs += 1
        for kk, vv in cnt.items(): tot[kk] = tot.get(kk, 0) + vv
        if maxf > mx: mx = maxf; ex = (uc.describe(M), blk, w, T)
    return runs, tot, mx, ex

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(4))
    tot = {}; mx = 0; ex = None; runs = 0
    for r_, t, m_, e in res:
        runs += r_
        for kk, vv in t.items(): tot[kk] = tot.get(kk, 0) + vv
        if m_ > mx: mx = m_; ex = e
    print("runs", runs, "reversal histogram", sorted(tot.items()), "max", mx, ex)
    # logged long runs
    edges=[(2, 6), (0, 2), (6, 2), (3, 5), (3, 4), (4, 6), (6, 3), (5, 1), (2, 5), (1, 0), (1, 2), (4, 1)]
    blk=[2, 4, 4, 3, 4, 2, 0, 5, 1, 4, 0, 0]
    w=[999, 27669, 254, 65535, 9, 392, 5231, 65535, 32767, 16829, 605, 2332]
    M = sc.graphic(7, edges)
    print("logged k=6 run:", flips(M, blk, M.k, w))
