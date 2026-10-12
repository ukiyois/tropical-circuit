"""Cross-check of the key instances of the phase 2d note with the independent
referee implementation (referee_phase2a/core.py: rank tables, base enumeration,
posl_update by a scan of all breakpoints).  For each instance, the epoch lengths
(stage r, S0, number of updates) and stage lengths are computed by both
implementations and compared.
Usage: python ep_referee.py
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import core as ref  # noqa: E402
import stage_core as sc  # noqa: E402
from stage_search import build  # noqa: E402
from ep_common import epochs  # noqa: E402


def ref_matroid(desc):
    kind, data, blk, w = desc
    if kind == "graphic":
        n, edges = data
        return ref.graphic(n, edges)
    if kind == "binary":
        return ref.gf2(data)
    raise ValueError(kind)


def ref_epochs(Mr, blk, k, w, cap=200):
    v = [Fraction(x) for x in w]
    out = []
    for r in range(1, k):
        cur, n = None, 0
        steps = 0
        while True:
            N0, _ = ref.opt_bases(Mr, v)
            A, nu = ref.avoidable(N0, blk, k)
            if nu > r or A != cur:
                if cur is not None:
                    out.append((r, sorted(cur), n))
                if nu > r:
                    break
                cur, n = A, 0
            tau, lam, a, _ = ref.posl_update(Mr, blk, k, v, r)
            v = [v[e] - a[blk[e]] for e in range(Mr.m)]
            n += 1
            steps += 1
            if steps > cap:
                raise RuntimeError("cap")
    return out


INSTANCES = {
    "R1 (rho=1 ladder, n = m - 2 = 7)":
        ('graphic', (5, [(1, 3), (1, 3), (3, 4), (2, 0), (2, 1), (1, 3), (4, 2), (0, 1), (2, 1)]),
         [0, 1, 1, 2, 1, 0, 0, 3, 1],
         [140624, 49368, 34576, 579690, 32980, 37332, 34568, 579690, 295920]),
    "R2 (rho=2, n = 8)":
        ('graphic', (6, [(4, 3), (2, 4), (4, 5), (0, 5), (2, 1), (0, 4), (1, 2), (2, 1), (4, 5), (0, 3), (1, 5)]),
         [4, 2, 4, 3, 1, 4, 2, 0, 4, 3, 0], [18, 10530, 2, 23, 15770, 64, 8583, 4308, 7, 880, 6446]),
    "A.3 tight, binary m=9 (stage 2 = 8)":
        ('binary', [4, 3, 3, 7, 7, 7, 1, 4, 2], [1, 1, 1, 1, 1, 1, 2, 1, 0],
         [7878, 418, 737, 2066, 3449, 65057, 526012, 3715, 1048576]),
    "A.3 tight, graphic m=8 (stage 2 = 7)":
        ('graphic', (4, [(2, 1), (2, 3), (1, 2), (1, 0), (3, 1), (2, 0), (0, 2), (2, 1)]),
         [1, 0, 1, 1, 2, 1, 1, 1], [6143, 188686, 3799, 94734, 421930, 1120, 1457, 54]),
    "A.3 tight, graphic m=11 (stage 2 = 10)":
        ('graphic', (4, [(2, 3), (0, 1), (3, 0), (3, 0), (0, 1), (0, 2), (0, 3), (3, 1), (0, 3), (1, 0), (1, 3)]),
         [0, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2],
         [242944, 652, 16002, 2, 121, 151842, 65, 38028, 75922, 8135, 356]),
    "Section 5 reuse example (rho=2, n = 8, m = 11)":
        ('graphic', (6, [(0, 1), (4, 0), (2, 4), (0, 2), (4, 1), (0, 3), (4, 5), (3, 0), (0, 3), (0, 1), (3, 5)]),
         [0, 1, 1, 0, 1, 4, 3, 3, 3, 0, 2], [2172, 15, 3437, 1011, 54, 40002, 24996, 14221, 20361, 606, 41723]),
    "P1 failure example (rho=2, n = 7, m = 10)":
        ('graphic', (5, [(1, 3), (3, 1), (2, 0), (2, 0), (0, 3), (1, 3), (4, 2), (2, 1), (4, 2), (0, 4)]),
         [0, 1, 2, 2, 1, 1, 2, 3, 2, 2], [335362, 233742, 26, 3789, 313619, 273680, 811, 1048576, 83842, 120224]),
    "k = 7 stage of m + 6 = 20 (m = 14)":
        ('graphic', (8, [(7, 5), (2, 4), (6, 4), (3, 6), (5, 3), (1, 4), (6, 4), (4, 6), (6, 5), (1, 3), (2, 1),
                         (4, 7), (7, 0), (0, 4)]), [6, 5, 0, 3, 1, 4, 1, 4, 1, 4, 2, 1, 6, 3],
         [430261, 4251475, 2240075, 19124, 153712, 3840, 2342092, 1171454, 102834, 307393, 16777218, 46321,
          200643, 256338]),
    "Conjecture P tight (rho=2, n = 9 = P1 + 1, m = 12)":
        ('graphic', (6, [(5, 4), (5, 3), (0, 4), (2, 5), (0, 1), (1, 2), (1, 2), (2, 5), (5, 3), (4, 3), (2, 5), (0, 5)]),
         [0, 0, 0, 3, 4, 4, 3, 3, 1, 2, 3, 3],
         [8693495, 5005395, 8715723, 647534, 12, 27734, 396381, 58070, 33554431, 17386996, 3050667, 1]),
}


def main():
    bad = 0
    for name, d in INSTANCES.items():
        M = build(d)
        _, _, blk, w = d
        k = M.k
        mine, _ = epochs(M, blk, k, list(w))
        mine = [(e["r"], e["S"], e["n"]) for e in mine]
        Mr = ref_matroid(d)
        theirs = ref_epochs(Mr, blk, k, w)
        theirs = [(r, S, n) for (r, S, n) in theirs]
        ok = mine == theirs
        bad += not ok
        print(("OK  " if ok else "DIFF"), name, "| stage_core:", mine, "| referee:", theirs, flush=True)
    print("mismatches:", bad)


if __name__ == "__main__":
    main()
