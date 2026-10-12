"""Random admissibility check ((F1)-(F4)) of the families of stage_families.py on
larger matroids (graphic up to 6 vertices, binary rank 3-4, uniform), m <= 9,
values in {0..6}.  Usage: python stage_admissible_random.py family seed"""
import random
import sys
from multiprocessing import Pool

import stage_core as sc
import stage_families as SF
from stage_forced_random import rand_inst


def work(args):
    fam, seed = args
    rng = random.Random(seed)
    fn = SF.FAMILIES[fam]
    st = {"states": 0, "levels": 0, "F1": 0, "F2": 0, "F3": 0, "F4": 0}
    ex = None
    for _ in range(12):
        kind, M = rand_inst(rng)
        if M.m > 9:
            continue
        bases = sc.all_bases(M)
        for _ in range(15):
            v = [rng.randint(0, 6) for _ in range(M.m)]
            st["states"] += 1
            th = {B: sc.theta(M, v, B) for B in bases}
            prev = None
            levels = sc.levels_of(v)
            for i, t in enumerate(levels):
                N = sc.MinBase(M, fn(M, SF.relation(v, t)))
                NB = {B for B in bases if N.rank(B) == M.k}
                st["levels"] += 1
                bad = []
                if i == 0:
                    vb = sc.beta(M, v)
                    if NB != {B for B in bases if sum(v[e] for e in sc.bits(B)) == vb}:
                        bad.append("F1")
                if prev is not None and not prev <= NB:
                    bad.append("F2")
                if any(th[B] <= t and B not in NB for B in bases):
                    bad.append("F3")
                if i == len(levels) - 1 and NB != set(bases):
                    bad.append("F4")
                for b in bad:
                    st[b] += 1
                    ex = ex or (b, kind, getattr(M, "edges", getattr(M, "cols", M.name)), v, t)
                prev = NB
    return st, ex


if __name__ == "__main__":
    fam, seed = sys.argv[1], int(sys.argv[2])
    with Pool(24) as pool:
        res = pool.map(work, [(fam, seed + s) for s in range(24)])
    tot, ex = {}, None
    for s, e in res:
        for key, val in s.items():
            tot[key] = tot.get(key, 0) + val
        ex = ex or e
    print(fam, tot, "example", ex)
