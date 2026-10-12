"""Exhaustive admissibility check of candidate families (stage_families.py).

For each zoo matroid and every v in {0..L}^m with min v = 0 (blocks do not enter
(F1)-(F3)), at every level t in {0} u {|v_e - v_f|}:
  F1  N(0) has exactly the minimum bases of v;
  F2  bases of N(t) are bases of N(t') for consecutive levels t < t';
  F3  every base with theta(B) <= t is a base of N(t);
  F4  N(t) = M at the top level (so it has a rainbow base when M does).
(F5) holds by construction: N(t) is computed from G_t, which is constant between
consecutive levels.  Usage: python stage_admissible.py L family [names...]
"""
import itertools
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402
import stage_families as SF  # noqa: E402


def work(args):
    name, L, fam, part, nparts = args
    Mr = EX.matroid_zoo()[name][0]()
    M = sc.from_rank_table(Mr.m, Mr.R)
    bases = sc.all_bases(M)
    fn = SF.FAMILIES[fam]
    st = {"states": 0, "levels": 0, "F1": 0, "F2": 0, "F3": 0, "F4": 0}
    ex = {}
    idx = 0
    for v in itertools.product(range(L + 1), repeat=M.m):
        if min(v) != 0:
            continue
        idx += 1
        if idx % nparts != part:
            continue
        v = list(v)
        st["states"] += 1
        th = {B: sc.theta(M, v, B) for B in bases}
        prev = None
        levels = sc.levels_of(v)
        for i, t in enumerate(levels):
            N = sc.MinBase(M, fn(M, SF.relation(v, t)))
            NB = {B for B in bases if N.rank(B) == M.k}
            st["levels"] += 1
            if i == 0:
                vb = sc.beta(M, v)
                if NB != {B for B in bases if sum(v[e] for e in sc.bits(B)) == vb}:
                    st["F1"] += 1
                    ex.setdefault("F1", (list(v), t))
            if prev is not None and not prev <= NB:
                st["F2"] += 1
                ex.setdefault("F2", (list(v), t))
            if any(th[B] <= t and B not in NB for B in bases):
                st["F3"] += 1
                ex.setdefault("F3", (list(v), t))
            if i == len(levels) - 1 and NB != set(bases):
                st["F4"] += 1
                ex.setdefault("F4", (list(v), t))
            prev = NB
    return st, ex


def main():
    L = int(sys.argv[1])
    fam = sys.argv[2]
    names = sys.argv[3:] or ["U24", "U25", "U35", "U36", "MK4", "W3", "P6dbl", "K4minus+par",
                             "C4+chord par", "sumU12U23", "sumU12U12", "gf3_U24", "U23+loop+coloop", "F7"]
    for name in names:
        t0 = time.time()
        with Pool(30) as pool:
            res = pool.map(work, [(name, L, fam, p, 30) for p in range(30)])
        tot, ex = {}, {}
        for s, e in res:
            for key, val in s.items():
                tot[key] = tot.get(key, 0) + val
            for key, val in e.items():
                ex.setdefault(key, val)
        print(f"{fam} {name}: L={L} {tot} examples={ex} {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
