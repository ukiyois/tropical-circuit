"""Exhaustive search: small matroids x all canonical block assignments (all
blocks used, a rainbow base exists) x all integer weight vectors v in
{0..L}^m with min v = 0.  At every state with nu0 = r < k: Proposition 7
(F1-F4, piecewise constancy, relation-determined), Theorem 6, Theorem 8
(items 1-3, strong form, Steps 1-5), and optionally the compilation identity."""
import itertools
import sys
import time
from multiprocessing import Pool
from core import *
import test_main as TM


def matroid_zoo():
    zoo = {}
    zoo["U24"] = (lambda: uniform(2, 4), 3)
    zoo["U25"] = (lambda: uniform(2, 5), 3)
    zoo["U35"] = (lambda: uniform(3, 5), 3)
    zoo["U36"] = (lambda: uniform(3, 6), 3)
    zoo["MK4"] = (lambda: graphic(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]), 3)
    # whirl W^3: rank 3, 6 elements (K4 graphic with one circuit-hyperplane relaxed)
    def whirl():
        G = graphic(4, [(0, 1), (1, 2), (2, 0), (0, 3), (1, 3), (2, 3)])
        # rim = {0,1,2}? In M(K4) labelled as wheel W3 with rim 0,1,2 (triangle 012) spokes 3,4,5
        def r(S):
            S = set(S)
            if S == {0, 1, 2}:
                return 3
            return G.R[sum(1 << e for e in S)]
        return Mat(6, r, check=True)
    zoo["W3"] = (whirl, 3)
    zoo["F7"] = (lambda: gf2([1, 2, 4, 3, 5, 6, 7]), 2)
    zoo["P6dbl"] = (lambda: graphic(3, [(0, 1), (0, 1), (1, 2), (1, 2), (0, 2), (0, 2)]), 3)
    zoo["U23+loop+coloop"] = (lambda: add_loops_coloops(uniform(2, 3), 1, 1), 3)
    zoo["sumU12U12"] = (lambda: direct_sum(uniform(1, 2), direct_sum(uniform(1, 2), uniform(1, 2))), 3)
    zoo["sumU12U23"] = (lambda: direct_sum(uniform(1, 2), uniform(2, 3)), 3)
    zoo["K4minus+par"] = (lambda: graphic(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)]), 3)
    zoo["C4+chord par"] = (lambda: graphic(4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (0, 2)]), 3)
    zoo["gf3_U24"] = (lambda: gfp([(1, 0), (0, 1), (1, 1), (1, 2)], 3), 4)
    zoo["U26"] = (lambda: uniform(2, 6), 2)
    zoo["U37"] = (lambda: uniform(3, 7), 2)
    zoo["bip33"] = (lambda: partition_matroid([j for i in range(3) for j in range(3)], {0: 1, 1: 1, 2: 1}), 2)
    return zoo


def rgs(m, k):
    """restricted growth strings of length m using exactly k symbols."""
    def rec(i, mx, cur):
        if i == m:
            if mx + 1 == k:
                yield list(cur)
            return
        for s in range(min(mx + 2, k)):
            cur.append(s)
            yield from rec(i + 1, max(mx, s), cur)
            cur.pop()
    yield from rec(0, -1, [])


def work(args):
    name, L, blk_list, part, nparts, do_compile = args
    M = matroid_zoo()[name][0]()
    k = M.k
    stats = {key: 0 for key in ["F1", "F2", "F3", "F4", "rel", "T6", "T8", "T8-item3-cases", "S-grow",
                                "aug", "C-not-strict-anyway", "step3-choices", "compile"]}
    states = 0
    idx = 0
    for blk in blk_list:
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
            states += 1
            TM.check_prop7(M, blk, k, v, stats)
            if do_compile:
                TM.check_thm6_thm8(M, blk, k, v, r, stats)
            else:
                check_6_8_nocompile(M, blk, k, v, r, stats)
    return states, stats, TM.FAIL[:5], len(TM.FAIL)


def check_6_8_nocompile(M, blk, k, v, r, stats):
    # same as TM.check_thm6_thm8 but skipping the (expensive) compile part:
    # temporarily monkeypatch by calling and catching nothing -- simpler to just call
    TM.check_thm6_thm8(M, blk, k, v, r, stats)


def main():
    names = sys.argv[1].split(",")
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    zoo = matroid_zoo()
    for name in names:
        t0 = time.time()
        M = zoo[name][0]()
        Lm = min(L, zoo[name][1]) if L < 0 else L
        k = M.k
        blks = [b for b in rgs(M.m, k) if has_rainbow(M, b, k)]
        nparts = procs * 4
        jobs = [(name, Lm, blks, p, nparts, True) for p in range(nparts)]
        with Pool(procs) as pool:
            res = pool.map(work, jobs)
        states = sum(x[0] for x in res)
        tot = {}
        for x in res:
            for key, c in x[1].items():
                tot[key] = tot.get(key, 0) + c
        nfail = sum(x[3] for x in res)
        print(f"{name}: m={M.m} k={k} blocks={len(blks)} L={Lm} states(nu0<k)={states} "
              f"failures={nfail} time={time.time() - t0:.0f}s", flush=True)
        print("   ", tot, flush=True)
        for x in res:
            for f in x[2]:
                print("    FAIL", f, flush=True)


if __name__ == "__main__":
    main()
