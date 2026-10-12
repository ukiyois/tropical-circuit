"""Random scan for states with tau_P < D, and with t1 < D where t1 = least theta(B) over bases B with
more than rho raised elements (see stage_forced.py), on larger matroids
(uniform U_{k,m}, graphic, binary), m <= 10.  Usage: python stage_forced_random.py seed trials"""
import random
import sys
from fractions import Fraction
from multiprocessing import Pool

import stage_core as sc
from stage_forced import analyse


def rand_inst(rng):
    kind = rng.choice(["uniform", "graphic", "binary"])
    if kind == "uniform":
        k = rng.randint(3, 5)
        m = rng.randint(k + 3, 10)
        M = sc.uniform(k, m)
    elif kind == "graphic":
        n = rng.randint(4, 6)
        while True:
            M = sc.graphic(n, [tuple(rng.sample(range(n), 2)) for _ in range(rng.randint(n + 2, 10))])
            if M.k == n - 1:
                break
    else:
        k = rng.randint(3, 5)
        while True:
            M = sc.gf2([rng.randrange(1, 1 << k) for _ in range(rng.randint(k + 3, 10))])
            if M.k == k:
                break
    return kind, M


def work(seed):
    rng = random.Random(seed)
    out = {"states": 0, "forced": 0, "ex": [], "ex1": []}
    for _ in range(60):
        kind, M = rand_inst(rng)
        k = M.k
        bases = sc.all_bases(M)
        for _ in range(20):
            blk = [i if i < k else rng.randrange(k) for i in range(M.m)]
            rng.shuffle(blk)
            if not any(len({blk[e] for e in sc.bits(B)}) == k for B in bases):
                continue
            style = rng.random()
            if style < 0.5:
                v = [rng.randint(0, 4) for _ in range(M.m)]
            else:
                v = [rng.randint(0, 40) for _ in range(M.m)]
            res = analyse(M, bases, blk, k, v)
            if res is None:
                continue
            r, S0, D, tauP = res
            out["states"] += 1
            Rm = sum(1 << e for e in range(M.m) if blk[e] in S0)
            rho = len(S0) - (k - r)
            t1 = min((sc.theta(M, v, B) for B in bases if sc.popcount(B & Rm) > rho), default=None)
            if t1 is not None and t1 < D:
                out["t1<D"] = out.get("t1<D", 0) + 1
                if len(out["ex1"]) < 2:
                    out["ex1"].append((kind, M.name, getattr(M, "edges", getattr(M, "cols", None)), blk, v, r,
                                       sorted(S0), D, tauP, t1))
            if tauP < D:
                out["forced"] += 1
                if len(out["ex"]) < 3:
                    out["ex"].append((kind, M.name, getattr(M, "edges", getattr(M, "cols", None)), blk, v, r, sorted(S0), D, tauP))
    return out


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    nw = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    with Pool(nw) as pool:
        res = pool.map(work, range(seed, seed + nw))
    print("states", sum(r["states"] for r in res), "forced(tau_P<D)", sum(r["forced"] for r in res),
          "t1<D", sum(r.get("t1<D", 0) for r in res))
    for r in res:
        for ex in r["ex1"][:1]:
            print("t1<D example", ex)
    for r in res:
        for ex in r["ex"]:
            print(ex)
