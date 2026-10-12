"""Test of the conjecture: an epoch of PO-SL has at most |U| updates, U = E - E_{S0}.

Every state with nu0 = r < k is taken as the first state of an epoch (exhaustive
on the zoo for v in {0..L}^E, all block assignments); the epoch is run to its end
(S0 changes or nu0 rises) and its length compared with |U|, |U - B*|, and the
number of distinct values of U.  Usage: python stage_epoch_U.py L [names...]
"""
import itertools
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402


def epoch_length(M, blk, k, v, r, S0, cap=500):
    c = 0
    while True:
        tau, lam, a, _ = sc.update(M, blk, k, v, r)
        v = sc.shift(v, blk, a)
        c += 1
        nu, S = sc.state(M, blk, k, v)
        if nu > r or S != S0:
            return c
        if c > cap:
            raise RuntimeError("cap")


def work(args):
    name, L, part, nparts = args
    Mr = EX.matroid_zoo()[name][0]()
    M = sc.from_rank_table(Mr.m, Mr.R)
    k = M.k
    bases = sc.all_bases(M)
    st = {"epochs": 0, "fail_U": 0, "max_len": 0, "max_ratio_U": 0.0, "fail_Unon": 0}
    ex = None
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
            v = list(v)
            nu, S0 = sc.state(M, blk, k, v)
            if nu >= k:
                continue
            n = epoch_length(M, blk, k, v, nu, S0)
            U = [e for e in range(M.m) if blk[e] not in S0]
            st["epochs"] += 1
            st["max_len"] = max(st["max_len"], n)
            st["max_ratio_U"] = max(st["max_ratio_U"], n / max(1, len(U)))
            if n > len(U):
                st["fail_U"] += 1
                ex = ex or (blk, v, nu, sorted(S0), n, len(U))
    return st, ex


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    names = sys.argv[2:] or ["U24", "U25", "U35", "U36", "MK4", "W3", "P6dbl", "K4minus+par",
                             "C4+chord par", "sumU12U23", "sumU12U12", "gf3_U24", "U23+loop+coloop"]
    for name in names:
        t0 = time.time()
        with Pool(30) as pool:
            res = pool.map(work, [(name, L, p, 30) for p in range(30)])
        tot = {"epochs": 0, "fail_U": 0, "max_len": 0, "max_ratio_U": 0.0}
        ex = None
        for s, e in res:
            tot["epochs"] += s["epochs"]
            tot["fail_U"] += s["fail_U"]
            tot["max_len"] = max(tot["max_len"], s["max_len"])
            tot["max_ratio_U"] = max(tot["max_ratio_U"], s["max_ratio_U"])
            ex = ex or e
        print(f"{name}: L={L} {tot} example={ex} {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
