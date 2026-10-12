"""Hill climbing against the epoch conjectures: maximise max over epochs of
(length - base), base = |U| (mode U), max(|U|, |R|) (mode maxUR) or m (mode m),
U = E - E_{S0} of the epoch (exponential weights).
Usage: python stage_search_epoch.py kind n m budget workers [mode]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc, mutate


MODE = "U"


def score(desc):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return None
    v = list(w)
    best = (-999, None)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        trace = []
        try:
            c, v = sc.run_stage(M, blk, k, v, r, cap=400, trace=trace)
        except RuntimeError:
            return None
        cur, n = None, 0
        for st in trace + [None]:
            if st is None or st["S0"] != cur:
                if cur is not None:
                    U = sum(1 for e in range(M.m) if blk[e] not in cur)
                    rho = len(cur) - (k - r)
                    base = U if MODE == "U" else (max(U, M.m - U) if MODE == "maxUR" else M.m)
                    best = max(best, (n - base, (n, U, rho, r)))
                if st is None:
                    break
                cur, n = st["S0"], 0
            n += 1
    return best


def _set_mode(mode):
    global MODE
    MODE = mode


def hill(args):
    seed, kind, n, m, budget, bits = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-999, None, None)
    while time.time() - t0 < budget:
        cur = random_desc(rng, kind, n, m, bits)
        s = score(cur)
        if s is None:
            continue
        stall = 0
        while stall < 500 and time.time() - t0 < budget:
            cand = mutate(cur, rng, bits)
            s2 = score(cand)
            stall += 1
            if s2 is None:
                continue
            if s2[0] >= s[0]:
                if s2[0] > s[0]:
                    stall = 0
                cur, s = cand, s2
        if s[0] > best[0]:
            best = (s[0], s[1], cur)
    return best


if __name__ == "__main__":
    kind, n, m, budget, workers = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    MODE = sys.argv[6] if len(sys.argv) > 6 else "U"
    with Pool(workers, initializer=_set_mode, initargs=(MODE,)) as pool:
        res = pool.map(hill, [(s, kind, n, m, budget, 20) for s in range(300, 300 + workers)])
    res.sort(key=lambda x: -x[0])
    print(f"kind={kind} n={n} m={m} budget={budget} mode={MODE}")
    for sc_, info, desc in res[:5]:
        print("max(len-|U|)", sc_, "(len,|U|,rho,r)", info, "desc", desc)
