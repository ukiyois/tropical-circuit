"""Lemma 4.3 / Corollary 4.4 exhaustively at k = 4 (and the k = 5 zoo for comparison).

For each matroid of the zoo, every block assignment up to renaming of blocks that has a
rainbow base, and every v in {0..L}^E with min v = 0: apply the last-stage block
(r = k - 1).  Record states by nu0, END drops (nu(M^{v'}) < nu0), path drops below 2
(Lemma 4.3: nu(L(s)) >= 2 once it is >= 2), and, at nu0 = 1, whether nu(M^{v'}) >= 2
(Corollary 4.4).  Discriminating variant: "nu never drops below 3 once >= 3" (false at
k = 5 by Instance LS-1), counted on the k = 5 matroids.
Usage: python ls_k4_exhaustive.py L workers"""
import itertools
import sys
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base

ZOO = {
    "U45": lambda: sc.uniform(4, 5),
    "U46": lambda: sc.uniform(4, 6),
    "C5+chord": lambda: sc.graphic(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 2)]),
    "C5+2chords": lambda: sc.graphic(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 2), (0, 3)]),
    "K4+pendant": lambda: sc.graphic(5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4)]),
    "U23+U23": lambda: sc.direct_sum(sc.uniform(2, 3), sc.uniform(2, 3)),
    "bin4_7": lambda: sc.gf2([1, 2, 4, 8, 3, 12, 15]),
    "C4par+tail": lambda: sc.graphic(5, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 1), (2, 4), (2, 4)]),
}


def canon_blocks(m, k):
    """Block assignments with all k blocks used, blocks named by first occurrence."""
    out = []

    def rec(i, cur, used):
        if i == m:
            if used == k:
                out.append(list(cur))
            return
        for b in range(min(used + 1, k)):
            cur.append(b)
            rec(i + 1, cur, max(used, b + 1))
            cur.pop()
    rec(0, [], 0)
    return out


def work(args):
    name, L, part, nparts = args
    M = ZOO[name]()
    k = M.k
    st = {"name": name, "assign": 0, "states": 0, "nu0_1": 0, "nu0_2": 0, "nu0_3": 0,
          "END": 0, "PATH_below2": 0, "nu1_to_ge2": 0, "nu1_fail": 0}
    blks = canon_blocks(M.m, k)
    for idx, blk in enumerate(blks):
        if idx % nparts != part:
            continue
        if not has_rainbow_base(M, blk, k):
            continue
        st["assign"] += 1
        for v in itertools.product(range(L + 1), repeat=M.m):
            if min(v) != 0:
                continue
            v = list(v)
            nu0, _ = lc.nu_state(M, blk, k, v)
            if nu0 >= k - 1:
                continue
            st["states"] += 1
            st["nu0_%d" % nu0] += 1
            pr = lc.path_profile(M, blk, k, v, k - 1)
            if pr["nu_end"] < nu0:
                st["END"] += 1
            sq = pr["nu_seq"]
            seen2 = nu0 >= 2
            for x in sq:
                if seen2 and x < 2:
                    st["PATH_below2"] += 1
                    break
                if x >= 2:
                    seen2 = True
            if nu0 == 1:
                if pr["nu_end"] >= 2:
                    st["nu1_to_ge2"] += 1
                else:
                    st["nu1_fail"] += 1
    return st


if __name__ == "__main__":
    L, workers = int(sys.argv[1]), int(sys.argv[2])
    tasks = []
    for name in ZOO:
        for part in range(3):
            tasks.append((name, L, part, 3))
    with Pool(workers) as pool:
        res = pool.map(work, tasks)
    agg = {}
    for st in res:
        d = agg.setdefault(st["name"], {})
        for key, val in st.items():
            if key != "name":
                d[key] = d.get(key, 0) + val
    for name, d in agg.items():
        print(name, d, flush=True)
