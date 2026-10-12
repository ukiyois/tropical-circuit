"""Targeted search: schedules on larger single-component matroids with finely
spaced or tied values (m up to 10).  Full Theorem 6/8 checks at every
application; collects item-3 cases (nu0 stays r and S unchanged) and the
longest stages.  Parallel over seeds."""
import random
import sys
import time
from multiprocessing import Pool
from core import *
import test_main as TM


def gen(rng):
    while True:
        kind = rng.choice(["ufine", "bdense", "gmulti", "paving", "gf3"])
        if kind == "ufine":
            k = rng.randint(2, 4)
            m = rng.randint(k + 3, 9)
            M = uniform(k, m)
        elif kind == "bdense":
            k = rng.randint(3, 4)
            m = rng.randint(k + 3, 9)
            M = gf2([rng.randrange(1, 1 << k) for _ in range(m)])
        elif kind == "gmulti":
            n = rng.randint(4, 5)
            M = graphic(n, [tuple(rng.sample(range(n), 2)) for _ in range(rng.randint(n + 2, 9))])
        elif kind == "paving":
            k = rng.randint(3, 4)
            M = sparse_paving(k, rng.randint(k + 3, 8), rng)
        else:
            k = 3
            M = gfp([tuple(rng.randrange(3) for _ in range(k)) for _ in range(rng.randint(6, 8))], 3)
        if M.k < 2:
            continue
        blk = rand_blocks(M, M.k, rng)
        if blk is None:
            continue
        style = rng.choice(["spaced", "ties", "ties5", "generic"])
        return kind, M, blk, M.k, rand_values(M.m, rng, style)


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    stats = {key: 0 for key in ["F1", "F2", "F3", "F4", "rel", "T6", "T8", "T8-item3-cases", "S-grow",
                                "aug", "C-not-strict-anyway", "step3-choices", "compile"]}
    longest = []
    item3 = []
    t0 = time.time()
    runs = 0
    while time.time() - t0 < budget:
        kind, M, blk, k, w = gen(rng)
        runs += 1
        p = {b: F0 for b in range(k)}
        for r in range(k):
            used = 0
            while True:
                v = [w[e] - p[blk[e]] for e in range(M.m)]
                N0, _ = opt_bases(M, v)
                if nu_of(N0, blk) > r:
                    break
                before = stats["T8-item3-cases"]
                TM.check_thm6_thm8(M, blk, k, v, r, stats)
                if stats["T8-item3-cases"] > before and len(item3) < 3:
                    item3.append((kind, M.m, k, blk, [str(x) for x in v], r))
                tau, lam, a, _ = posl_update(M, blk, k, v, r)
                p = {b: p[b] + a[b] for b in range(k)}
                used += 1
                if used > 60:
                    TM.fail("runaway", (kind, blk, w, r))
                    break
            if used > r + 1:
                longest.append((used - (r + 1), kind, M.m, k, r, used, blk, [str(x) for x in w]))
        if psi(M, blk, k, w, p) != opt_rainbow(M, blk, k, w):
            TM.fail("final", (kind, blk, w))
    return runs, stats, TM.FAIL[:5], len(TM.FAIL), item3, sorted(longest, reverse=True)[:3]


def main():
    nseeds = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    with Pool(min(nseeds, 30)) as pool:
        budget = float(sys.argv[2]) if len(sys.argv) > 2 else 60
        res = pool.map(work, [(s_, budget) for s_ in range(1000, 1000 + nseeds)])
    tot = {}
    for x in res:
        for key, c in x[1].items():
            tot[key] = tot.get(key, 0) + c
    print("runs", sum(x[0] for x in res), "failures", sum(x[3] for x in res))
    print(tot)
    for x in res:
        for f in x[2]:
            print("FAIL", f)
    longest = sorted([y for x in res for y in x[5]], reverse=True)[:5]
    print("stages longer than r+1 (excess, kind, m, k, r, apps, blk, w):")
    for y in longest:
        print("  ", y)
    print("sample item-3 cases:")
    for x in res:
        for y in x[4][:1]:
            print("  ", y)


if __name__ == "__main__":
    main()
