"""Rank-one components with T_LS >= k: search (seeds of lsu_tmp_inv.py) and verification.
Prints the instance, the nu0 / S0 sequence, and the regular schedule's stage lengths;
re-checks nu0 at every state and Psi = Opt with the referee implementation.
Usage: python lsu_rankone_ce.py"""
import random, sys, time
from fractions import Fraction
from multiprocessing import Pool
import stage_core as sc, lsu_trace as tr, ls_core as lc
from lsu_rankone import instance

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    while time.time() - t0 < 100:
        k, parts, blk, w = instance(rng); M = sc.partition(parts)
        t = tr.trace(M, blk, k, w, cap=200)
        if len(t) > k - 1:
            return (k, parts, blk, w)
    return None

if __name__ == "__main__":
    with Pool(4) as pool: res = pool.map(work, range(19100, 19104))
    found = [r for r in res if r]
    k, parts, blk, w = min(found, key=lambda r: len(r[1]))
    M = sc.partition(parts)
    t = tr.trace(M, blk, k, w, cap=200)
    print("k", k, "m", len(parts), "columns", parts, "rows (blocks)", blk, "w", w)
    print("T_LS", len(t), "nu0/S0:", [(s["nu0"], sorted(s["S0"])) for s in t], "->", t[-1]["nu1"])
    for j, s in enumerate(t):
        print("  step", j, "a", s["a"], "tau", s["tau"], "mismatch", s["mismatch"], "levels", sorted({nu for _, _, nu, _ in s["pcs"]}))
    lens, vreg = lc.regular(M, blk, k, w)
    print("regular stage lengths", lens)
    vl = t[-1]["v2"]
    print("Psi=Opt:", sc.psi_from_v(M, blk, k, w, vl) == sc.opt_rainbow(M, blk, k, w))
    sys.path.insert(0, "referee_phase2a")
    import core as ref
    Mr = ref.partition_matroid(parts, [1] * k)
    for j, s in enumerate(t + [{"v": vl, "nu0": t[-1]["nu1"]}]):
        A, nu = ref.avoidable(ref.opt_bases(Mr, [Fraction(x) for x in s["v"]])[0], blk, k)
        print("  referee nu0 at state", j, "=", nu, "ours", s["nu0"])
