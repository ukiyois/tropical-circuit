"""Forced extra updates for EVERY admissible family.

Any admissible family has N(t) containing P_t, so nu(N(t)) >= nu(P_t) and its
tau is at most tau_P = min{ theta(B) : B meets >= r+1 blocks }.  At an epoch
state with tau_P < D (D of Theorem 2.2), Theorem 2.2(2) gives D' >= D - tau > 0
for every admissible family: the epoch cannot end in one update.

This script scans states (exhaustive on a small matroid list, or random) and
reports the states with tau_P < D, and the largest ratio D / tau_P.
Usage: python stage_forced.py exhaustive L   |   python stage_forced.py random seed trials
"""
import itertools
import os
import random
import sys
from fractions import Fraction
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402
from stage_verify_epoch import D_of  # noqa: E402


def analyse(M, bases, blk, k, v):
    vals = {B: sum(v[e] for e in sc.bits(B)) for B in bases}
    b0 = min(vals.values())
    minb = [B for B in bases if vals[B] == b0]
    nblk = {B: len({blk[e] for e in sc.bits(B)}) for B in minb}
    r = max(nblk.values())
    if r >= k:
        return None
    S0 = frozenset(b for B in minb if nblk[B] == r for b in range(k) if b not in {blk[e] for e in sc.bits(B)})
    Rset = {e for e in range(M.m) if blk[e] in S0}
    Bs = next(B for B in minb if nblk[B] == r)
    D = D_of(M, Bs, Rset, v)
    tauP = min(sc.theta(M, v, B) for B in bases if len({blk[e] for e in sc.bits(B)}) >= r + 1)
    return r, S0, D, tauP


def work(args):
    name, L, part, nparts = args
    Mr = EX.matroid_zoo()[name][0]()
    M = sc.from_rank_table(Mr.m, Mr.R)
    k = M.k
    bases = sc.all_bases(M)
    out = {"states": 0, "forced": 0, "maxratio": Fraction(0), "ex": None}
    idx = 0
    for blk in EX.rgs(M.m, k):
        if not any(len({blk[e] for e in sc.bits(B)}) == k for B in bases):
            continue
        for v in itertools.product(range(L + 1), repeat=M.m):
            if min(v) != 0:
                continue
            idx += 1
            if idx % nparts != part:
                continue
            res = analyse(M, bases, blk, k, list(v))
            if res is None:
                continue
            r, S0, D, tauP = res
            out["states"] += 1
            if tauP < D:
                out["forced"] += 1
                ratio = Fraction(D, tauP) if tauP > 0 else Fraction(10 ** 9)
                if ratio > out["maxratio"]:
                    out["maxratio"] = ratio
                    out["ex"] = (blk, list(v), r, sorted(S0), D, tauP)
    return out


def main():
    mode = sys.argv[1]
    if mode == "exhaustive":
        L = int(sys.argv[2])
        names = sys.argv[3:] or ["U24", "U25", "U35", "U36", "MK4", "W3", "P6dbl", "K4minus+par",
                                 "C4+chord par", "sumU12U23", "sumU12U12", "U23+loop+coloop"]
        for name in names:
            with Pool(30) as pool:
                res = pool.map(work, [(name, L, p, 30) for p in range(30)])
            st = sum(r["states"] for r in res)
            fo = sum(r["forced"] for r in res)
            best = max(res, key=lambda r: r["maxratio"])
            print(f"{name}: states {st} forced(tau_P < D) {fo} max D/tau_P {best['maxratio']} ex {best['ex']}",
                  flush=True)


if __name__ == "__main__":
    main()
