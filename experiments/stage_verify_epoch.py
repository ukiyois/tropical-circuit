"""Exhaustive check of Theorems 2.1, 2.2, 2.4 (phase2b note) on the referee zoo.

For every matroid of the zoo, every block assignment with a rainbow base (all
blocks used), every v in {0..L}^m with min v = 0 and nu0 = r < k, and EVERY
minimum base B* of v meeting r blocks, one PO-SL update v -> v' is checked:
  G1  D(v) > 0                          G2  D(v') >= D(v) - tau
  G3  D(v') <= D(v) - delta             G4  (2q - 1) delta >= D(v)
  E   D(v') = 0  iff  (nu0(v') > r or S0(v') != S0(v))
  A   some pair x in R, z in U, x or z in B*, one component, passes
  Z   rho = 0  implies  D(v') = 0
Usage: python stage_verify_epoch.py L [names...]
"""
import itertools
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402


def zoo_sc(name):
    Mr = EX.matroid_zoo()[name][0]()
    return sc.from_rank_table(Mr.m, Mr.R)


def first_event(M, blk, k, v, r, S0):
    for t in sc.levels_of(v):
        nu, av, _ = sc.rainbow_av(sc.posl(M, v, t), blk, k)
        if nu > r or av != S0:
            return t
    raise RuntimeError("no event")


def D_of(M, Bs, Rset, v):
    best = None
    for y in Rset:
        if Bs >> y & 1:
            continue
        for g in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
            if g not in Rset:
                d = v[y] - v[g]
                best = d if best is None or d < best else best
    return best


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
    delta = first_event(M, blk, k, v, r, S0)
    tau, lam, a, _ = sc.update(M, blk, k, v, r)
    v2 = sc.shift(v, blk, a)
    vals2 = {B: sum(v2[e] for e in sc.bits(B)) for B in bases}
    b2 = min(vals2.values())
    minb2 = [B for B in bases if vals2[B] == b2]
    nb2 = {B: len({blk[e] for e in sc.bits(B)}) for B in minb2}
    r2 = max(nb2.values())
    S2 = frozenset(b for B in minb2 if nb2[B] == r2 for b in range(k) if b not in {blk[e] for e in sc.bits(B)})
    ended = r2 > r or S2 != S0
    stats["states"] += 1
    for Bs in minb:
        if nblk[Bs] != r:
            continue
        stats["Bstar"] += 1
        D = D_of(M, Bs, Rset, v)
        D2 = D_of(M, Bs, Rset, v2)
        q = max(len({v[e] for e in sc.bits(Bs) if M.comp[e] == c}) for c in range(M.ncomp))
        ok = {"G1": D is not None and D > 0,
              "G2": D2 >= D - tau,
              "G3": D2 <= D - delta,
              "G4": (2 * q - 1) * delta >= D,
              "E": (D2 == 0) == ended,
              "Z": rho > 0 or D2 == 0}
        cross = False
        for x in Rset:
            for z in range(m):
                if z in Rset or M.comp[x] != M.comp[z]:
                    continue
                if (Bs >> x & 1 or Bs >> z & 1) and v[x] > v[z] and v2[x] <= v2[z]:
                    cross = True
                    break
            if cross:
                break
        ok["A"] = cross
        for key, val in ok.items():
            if not val:
                stats["fail_" + key] = stats.get("fail_" + key, 0) + 1
                if len(bad) < 3:
                    bad.append((key, blk, list(v), r))


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
    nparts = 30
    for name in names:
        t0 = time.time()
        with Pool(nparts) as pool:
            res = pool.map(work, [(name, L, p, nparts) for p in range(nparts)])
        tot, bad = {}, []
        for s, b in res:
            for key, val in s.items():
                tot[key] = tot.get(key, 0) + val
            bad += b
        print(f"{name}: L={L} {tot} bad={bad[:2]} time {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
