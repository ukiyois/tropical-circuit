"""Goal 2: search for a decrease of nu(L(s)) along the path of a stage-r block (nu0 < r).

Random instances with larger k (graphic on 6 to 7 vertices, binary rank 5 to 6, uniform
rank 5, sparse paving rank 5, sums), weights small, spread, exponential and ladder-like;
states: the start w, and every state along the LS iteration and along the regular
schedule from w (typical states).  For each state and every r with nu0 < r <= k - 1:
the path profile (open intervals).  Reports PATH drops (nu(L) decreasing between
consecutive open intervals), END drops (nu(M^{v'}) < nu0) and counts.
Usage: python ls_search_drop.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import sparse_paving, has_rainbow_base


def rmat(rng):
    kind = rng.choice(["graphic", "graphic", "graphic", "binary", "uniform", "paving", "sum"])
    if kind == "graphic":
        n = rng.randint(6, 7)
        m = rng.randint(n + 1, 12)
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        return kind, sc.graphic(n, edges)
    if kind == "binary":
        r = rng.randint(5, 6)
        m = rng.randint(r + 2, 11)
        return kind, sc.gf2([rng.randint(1, (1 << r) - 1) for _ in range(m)])
    if kind == "uniform":
        return kind, sc.uniform(5, rng.randint(6, 9))
    if kind == "paving":
        return kind, sparse_paving(5, rng.randint(7, 9), rng)
    A = sc.graphic(4, [tuple(rng.sample(range(4), 2)) for _ in range(rng.randint(4, 6))])
    B = sc.graphic(4, [tuple(rng.sample(range(4), 2)) for _ in range(rng.randint(4, 6))])
    return kind, sc.direct_sum(A, B)


def rweights(rng, m):
    st = rng.choice(["ties", "spread", "exp", "ladder"])
    if st == "ties":
        return [rng.randint(0, 5) for _ in range(m)]
    if st == "spread":
        return [rng.randint(0, 10 ** 4) for _ in range(m)]
    if st == "exp":
        return [rng.choice([0, 1 << rng.randint(0, 14), rng.randint(0, 1 << 14)]) for _ in range(m)]
    L = rng.randint(3, 8)
    A = 1 << L
    return [rng.choice([0, A, A + 1, A >> rng.randint(1, L), rng.randint(0, A)]) for _ in range(m)]


def check_state(M, blk, k, v, st, ex, inst):
    nu0, _ = lc.nu_state(M, blk, k, v)
    for r in range(nu0 + 1, k):
        pr = lc.path_profile(M, blk, k, v, r)
        st["blocks"] += 1
        sq = pr["nu_seq"]
        st["intervals"] += len(sq)
        if any(y < x for x, y in zip(sq, sq[1:])) or (sq and sq[0] < nu0):
            st["PATH"] += 1
            ex.setdefault("PATH", inst + (r, list(v)))
        if pr["nu_end"] < nu0:
            st["END"] += 1
            ex.setdefault("END", inst + (r, list(v)))
        if pr["gain"] < pr["lower"]:
            st["ASCENT"] += 1
            ex.setdefault("ASCENT", inst + (r, list(v)))


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"inst": 0, "blocks": 0, "intervals": 0, "PATH": 0, "END": 0, "ASCENT": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = rmat(rng)
        k = M.k
        if k < 4:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        w = rweights(rng, M.m)
        st["inst"] += 1
        inst = (kind, M.m, k, blk, getattr(M, "edges", None), getattr(M, "cols", None), w)
        # states along the LS iteration
        v = list(w)
        for _ in range(12):
            if time.time() - t0 > budget:
                break
            nu0, _ = lc.nu_state(M, blk, k, v)
            if nu0 >= k:
                break
            check_state(M, blk, k, v, st, ex, inst)
            a, pcs, tau = lc.block(M, blk, k, v, k - 1)
            v = lc.shift(v, blk, a)
        # states along the regular schedule (start of each update)
        v = list(w)
        cnt = 0
        while cnt < 12 and time.time() - t0 < budget:
            nu0, _ = lc.nu_state(M, blk, k, v)
            if nu0 >= k:
                break
            if cnt > 0:
                check_state(M, blk, k, v, st, ex, inst)
            tau, lam, a, info = sc.update(M, blk, k, v, nu0)
            v = sc.shift(v, blk, a)
            cnt += 1
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 11000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
