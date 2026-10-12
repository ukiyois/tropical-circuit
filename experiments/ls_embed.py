"""Goal 2: try to realize the abstract counterexample to Claim R inside a real block path.

Base: the graphic matroid G on 6 vertices of the Claim R counterexample
(ls_logs/refine_claim.txt), blocks [4,1,2,1,4,3,4,4,0,0], which has nu = 4 < 5.  Add
1 to 3 random edges with random blocks so that the sum has a rainbow base; random
small-integer states v (and v = u + a_blk with u the counterexample's weights); check
every multi-stage block (nu0 < r <= k-1) for a decrease of nu(L(s)) along the path
(PATH) and at the end (END).
Usage: python ls_embed.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base
from ls_search_drop import check_state

EDGES = [(2, 3), (5, 1), (1, 0), (1, 0), (4, 2), (5, 1), (0, 3), (5, 3), (0, 4), (3, 0)]
BLK = [4, 1, 2, 1, 4, 3, 4, 4, 0, 0]
U = [0, 1, 4, 2, 0, 3, 2, 1, 2, 4]


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"inst": 0, "blocks": 0, "intervals": 0, "PATH": 0, "END": 0, "ASCENT": 0}
    ex = {}
    while time.time() - t0 < budget:
        extra = [tuple(rng.sample(range(6), 2)) for _ in range(rng.randint(1, 3))]
        edges = EDGES + extra
        blk = BLK + [rng.randrange(5) for _ in extra]
        M = sc.graphic(6, edges)
        k = M.k
        if k != 5 or not has_rainbow_base(M, blk, k):
            continue
        st["inst"] += 1
        for _ in range(30):
            mode = rng.random()
            if mode < 0.4:
                v = [rng.randint(0, 5) for _ in range(M.m)]
            elif mode < 0.8:
                a = [rng.randint(0, 3) for _ in range(k)]
                v = [U[e] + a[blk[e]] if e < 10 else rng.randint(0, 8) for e in range(M.m)]
            else:
                v = [2 * U[e] + rng.randint(0, 1) if e < 10 else rng.randint(0, 12) for e in range(M.m)]
            inst = ("embed", M.m, k, blk, edges, None, v)
            check_state(M, blk, k, v, st, ex, inst)
            if time.time() - t0 > budget:
                break
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(17100 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
