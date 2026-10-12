"""Worst-case PO-SL stage length.  Every state v with nu0(v) = r is the start of
stage r for the input w = v (earlier stages are identities), so the worst stage
length is a max over states.  Exhaustive over small matroids, canonical blocks,
v in {0..L}^m with min 0.  Records max(apps - (r+1)), the number of item-3
applications, and checks the Theorem 8 bound and the potential at each step."""
import itertools
import sys
import time
from multiprocessing import Pool
from core import *
from exhaustive import matroid_zoo, rgs


def cross(blk, v, S, m):
    ES = [e for e in range(m) if blk[e] in S]
    rest = [e for e in range(m) if blk[e] not in S]
    return {(y, g) for y in ES for g in rest if v[y] <= v[g]}


def stage(M, blk, k, v, r, out):
    used = 0
    item3 = 0
    while True:
        N0, _ = opt_bases(M, v)
        nu = nu_of(N0, blk)
        if nu > r:
            return used, item3
        S, _ = avoidable(N0, blk, k)
        C0 = cross(blk, v, S, M.m)
        tau, lam, a, _ = posl_update(M, blk, k, v, r)
        v2 = [v[e] - a[blk[e]] for e in range(M.m)]
        if not C0 < cross(blk, v2, S, M.m):
            out["potential_fail"] += 1
        N0b, _ = opt_bases(M, v2)
        if nu_of(N0b, blk) == r:
            S2, _ = avoidable(N0b, blk, k)
            if S2 == S:
                item3 += 1
            elif not S <= S2:
                out["S_shrink"] += 1
        elif nu_of(N0b, blk) < r:
            out["nu_drop"] += 1
        v = v2
        used += 1
        if used > (r + 1) * (M.m * M.m // 4 + 1):
            out["over_bound"] += 1
            return used, item3


def work(args):
    name, L, blks, part, nparts = args
    M = matroid_zoo()[name][0]()
    k = M.k
    out = {"states": 0, "potential_fail": 0, "S_shrink": 0, "nu_drop": 0, "over_bound": 0}
    worst = (-99, None)
    hist = {}
    idx = 0
    for blk in blks:
        for v in itertools.product(range(L + 1), repeat=M.m):
            if min(v) != 0:
                continue
            idx += 1
            if idx % nparts != part:
                continue
            v = [Fraction(x) for x in v]
            N0, _ = opt_bases(M, v)
            r = nu_of(N0, blk)
            if r >= k:
                continue
            out["states"] += 1
            used, item3 = stage(M, blk, k, v, r, out)
            ex = used - (r + 1)
            hist[(r, used)] = hist.get((r, used), 0) + 1
            if ex > worst[0]:
                worst = (ex, (blk, [str(x) for x in v], r, used, item3))
    return out, worst, hist


def main():
    names = sys.argv[1].split(",")
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    zoo = matroid_zoo()
    for name in names:
        t0 = time.time()
        M = zoo[name][0]()
        blks = [b for b in rgs(M.m, M.k) if has_rainbow(M, b, M.k)]
        nparts = procs * 4
        with Pool(procs) as pool:
            res = pool.map(work, [(name, L, blks, p, nparts) for p in range(nparts)])
        tot = {}
        hist = {}
        for o, _, h in res:
            for key, c in o.items():
                tot[key] = tot.get(key, 0) + c
            for key, c in h.items():
                hist[key] = hist.get(key, 0) + c
        worst = max((w for _, w, _ in res), key=lambda x: x[0])
        print(f"{name}: m={M.m} k={M.k} L={L} {tot} worst excess over r+1: {worst[0]}  example {worst[1]}  "
              f"time {time.time() - t0:.0f}s", flush=True)
        print("    (r, stage length) histogram:", dict(sorted(hist.items())), flush=True)


if __name__ == "__main__":
    main()
