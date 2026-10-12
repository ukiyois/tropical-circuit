"""Epoch length against |U| on random and searched instances with long stages.
Usage: python stage_epoch_U_random.py seed trials"""
import ast
import glob
import random
import sys
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc


def epochs_of(M, blk, k, w):
    out = []
    v = list(w)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        trace = []
        c, v = sc.run_stage(M, blk, k, v, r, trace=trace)
        cur, n = None, 0
        for st in trace:
            if st["S0"] != cur:
                if cur is not None:
                    out.append((n, sum(1 for e in range(M.m) if blk[e] not in cur)))
                cur, n = st["S0"], 0
            n += 1
        if cur is not None:
            out.append((n, sum(1 for e in range(M.m) if blk[e] not in cur)))
    return out


def work(seed):
    rng = random.Random(seed)
    res = []
    for _ in range(25):
        kind = rng.choice(["graphic", "binary"])
        if kind == "graphic":
            n = rng.randint(4, 6)
            d = random_desc(rng, kind, n, rng.randint(n + 2, 11), rng.choice([8, 16, 22]))
        else:
            kk = rng.randint(3, 5)
            d = random_desc(rng, kind, kk, rng.randint(kk + 3, 11), rng.choice([8, 16, 22]))
        M = build(d)
        _, _, blk, w = d
        if not has_rainbow(M, blk, M.k):
            continue
        res += epochs_of(M, blk, M.k, w)
    return res


if __name__ == "__main__":
    seed, nw = int(sys.argv[1]), int(sys.argv[2])
    with Pool(28) as pool:
        res = sum(pool.map(work, range(seed, seed + nw)), [])
    print("random epochs", len(res), "fails (len > |U|)", sum(1 for n, u in res if n > u),
          "max len", max(n for n, u in res), "len == |U|", sum(1 for n, u in res if n == u and n > 1))
    # searched instances
    found = []
    for f in glob.glob("stage_logs/exp_*.txt") + glob.glob("stage_logs/hill_*.txt"):
        for line in open(f):
            if line.startswith("score"):
                desc = ast.literal_eval(line[line.index("desc ") + 5:].strip())
                found.append(desc)
    bad = 0
    tot = 0
    for d in found:
        M = build(d)
        _, _, blk, w = d
        for n, u in epochs_of(M, blk, M.k, w):
            tot += 1
            if n > u:
                bad += 1
                print("FAIL", d, n, u)
    print("searched instances", len(found), "epochs", tot, "fails", bad)
