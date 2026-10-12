"""Exhaustive check of the rho = 1 lemma (phase 2d note, Theorem A) on the referee zoo.

For every matroid of the zoo, every block assignment with a rainbow base, every
v in {0..L}^m with min v = 0 and nu0 = r < k, every minimum base B* of v meeting
r blocks, one PO-SL update v -> v' is checked.  With R = E_{S0}, U = E - R,
rho = |S0| - (k - r), D, D' as in B0:
  T1  (rho = 1, D' > 0)  some z in U, in the component of h (B* cap R = {h}),
       has v_z < v_h and v'_z >= v'_h                     [Theorem A, per update]
  T2  (any rho, D' > 0)  D > delta                         [Lemma A.1]
  T3  (any rho, D' > 0)  every y in R - B* with y in PO_delta has an anchor
       b in C(B*, y) - y with v_y - delta <= v_b, and all such b lie in R
                                                         [Lemma A.2]
False variants (expected to fail, to show the harness discriminates):
  F1  (rho = 1, D' > 0)  some z in U - B* passes h (a non-anchor)
  F2  (rho = 1, D' = 0)  some z in U passes h  (T1 at the last update)
  F3  (rho = 2, D' > 0)  some z in U passes an anchor of B* cap R
       (the rho = 1 statement for rho = 2; Section 4 shows it fails)
Usage: python ep_verify_rho1.py L [names...]
"""
import itertools
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402
from stage_verify_epoch import zoo_sc, first_event, D_of  # noqa: E402


def check(M, bases, blk, k, v, stats, bad):
    m = M.m
    vals = {B: sum(v[e] for e in sc.bits(B)) for B in bases}
    b0 = min(vals.values())
    minb = [B for B in bases if vals[B] == b0]
    nblk = {B: len({blk[e] for e in sc.bits(B)}) for B in minb}
    r = max(nblk.values())
    if r >= k:
        return
    S0 = frozenset(b for B in minb if nblk[B] == r for b in range(k) if b not in {blk[e] for e in sc.bits(B)})
    Rset = {e for e in range(m) if blk[e] in S0}
    rho = len(S0) - (k - r)
    if rho == 0:
        return
    delta = first_event(M, blk, k, v, r, S0)
    tau, lam, a, _ = sc.update(M, blk, k, v, r)
    v2 = sc.shift(v, blk, a)
    po = set(sc.po_set(M, v, delta))
    stats["states"] += 1
    for Bs in minb:
        if nblk[Bs] != r:
            continue
        stats["Bstar"] += 1
        D = D_of(M, Bs, Rset, v)
        D2 = D_of(M, Bs, Rset, v2)
        RA = [h for h in Rset if Bs >> h & 1]
        res = {}

        def passes(h, nonanchor=False):
            for z in range(m):
                if z in Rset or M.comp[z] != M.comp[h]:
                    continue
                if nonanchor and Bs >> z & 1:
                    continue
                if v[z] < v[h] and v2[z] >= v2[h]:
                    return True
            return False
        if D2 > 0:
            res["T2"] = D > delta
            ok3 = True
            for y in Rset:
                if Bs >> y & 1 or y not in po:
                    continue
                win = [b for b in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)) if v[b] >= v[y] - delta]
                if not win or any(b not in Rset for b in win):
                    ok3 = False
            res["T3"] = ok3
            if rho == 1:
                h = RA[0]
                res["T1"] = passes(h)
                res["F1"] = passes(h, nonanchor=True)
            if rho == 2:
                res["F3"] = any(passes(h) for h in RA)
        elif rho == 1:
            res["F2"] = passes(RA[0])
        for key, val in res.items():
            stats["n_" + key] = stats.get("n_" + key, 0) + 1
            if not val:
                stats["fail_" + key] = stats.get("fail_" + key, 0) + 1
                if key.startswith("T") and len(bad) < 3:
                    bad.append((key, blk, list(v), r, Bs))


def work(args):
    name, L, part, nparts = args
    M = zoo_sc(name)
    k = M.k
    bases = sc.all_bases(M)
    stats = {"states": 0, "Bstar": 0}
    bad = []
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
            check(M, bases, blk, k, list(v), stats, bad)
    return stats, bad


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    names = sys.argv[2:] or ["U24", "U25", "U35", "U36", "MK4", "W3", "P6dbl", "K4minus+par",
                             "C4+chord par", "sumU12U23", "sumU12U12", "gf3_U24", "U23+loop+coloop"]
    nparts = 6
    for name in names:
        t0 = time.time()
        with Pool(nparts) as pool:
            res = pool.map(work, [(name, L, p, nparts) for p in range(nparts)])
        tot, bad = {}, []
        for s, b in res:
            for key, val in s.items():
                tot[key] = tot.get(key, 0) + val
            bad += b
        print(f"{name}: L={L} {dict(sorted(tot.items()))} bad={bad[:2]} time {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
