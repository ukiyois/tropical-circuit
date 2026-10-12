"""Goal 2 (random states): the stage-r block at states with nu0 < r.

For random matroids (graphic, binary, uniform, sparse paving, direct sums), random blocks
with a rainbow base and random states v (small integers with ties, spread integers,
exponential), and every r with nu0 < r <= k - 1, run ls_core.path_profile and record:
  MONO_END   nu(M^{v'}) >= nu0                                  (conjecture)
  MONO_PATH  nu(L(s)) >= nu0 on every open interval of the path  (stronger)
  ASCENT     Psi(p+a) - Psi(p) >= int_0^tau (k - nu(N(t))) dt    (Lead 1, a theorem)
and the deliberately false variants
  F_EQ       Psi gain == (k - nu0) tau  (validity's equality, only for r = nu0)
  F_RATE0    Psi gain >= (k - nu0) tau  (rate of the first stage throughout)
  F_PATHMON  nu(L(s)) nondecreasing along the path
Usage: python ls_mono_random.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc


def sparse_paving(k, m, rng, tries=40):
    import itertools
    allk = list(itertools.combinations(range(m), k))
    rng.shuffle(allk)
    hyp = []
    for H in allk[:tries]:
        Hs = set(H)
        if all(len(Hs & G) <= k - 2 for G in hyp):
            hyp.append(Hs)
    hmasks = {sc.mask_of(H) for H in hyp}

    def r(S):
        c = sc.popcount(S)
        if c < k:
            return c
        if c == k and S in hmasks:
            return k - 1
        return k
    return sc.Matroid(m, r, "paving")


def random_matroid(rng):
    kind = rng.choice(["graphic", "graphic", "binary", "uniform", "paving", "sum"])
    if kind == "graphic":
        n = rng.randint(5, 6)
        m = rng.randint(n + 1, 10)
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        return kind, sc.graphic(n, edges)
    if kind == "binary":
        r = rng.randint(4, 5)
        m = rng.randint(r + 2, 10)
        return kind, sc.gf2([rng.randint(1, (1 << r) - 1) for _ in range(m)])
    if kind == "uniform":
        r = rng.randint(4, 5)
        return kind, sc.uniform(r, rng.randint(r + 1, 9))
    if kind == "paving":
        r = rng.randint(4, 5)
        return kind, sparse_paving(r, rng.randint(r + 2, 9), rng)
    A = sc.uniform(rng.randint(1, 3), rng.randint(3, 5))
    n = rng.randint(3, 4)
    B = sc.graphic(n, [tuple(rng.sample(range(n), 2)) for _ in range(rng.randint(n, 6))])
    return kind, sc.direct_sum(A, B)


def random_v(rng, m):
    st = rng.choice(["ties3", "ties6", "spread", "exp", "exp"])
    if st == "ties3":
        return [rng.randint(0, 3) for _ in range(m)]
    if st == "ties6":
        return [rng.randint(0, 6) for _ in range(m)]
    if st == "spread":
        return [rng.randint(0, 1000) for _ in range(m)]
    return [rng.choice([0, 1 << rng.randint(0, 12), rng.randint(0, 1 << 12)]) for _ in range(m)]


def has_rainbow_base(M, blk, k):
    nu, _, _ = sc.rainbow_av(M, blk, k)
    return nu == k


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"states": 0, "blocks": 0, "multi": 0, "MONO_END": 0, "MONO_PATH": 0, "ASCENT": 0,
          "F_EQ": 0, "F_RATE0": 0, "F_PATHMON": 0, "eq_cases": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = random_matroid(rng)
        k = M.k
        if k < 3:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        v = random_v(rng, M.m)
        nu0, _ = lc.nu_state(M, blk, k, v)
        if nu0 >= k:
            continue
        st["states"] += 1
        for r in range(nu0, k):
            pr = lc.path_profile(M, blk, k, v, r)
            st["blocks"] += 1
            inst = (kind, M.m, k, r, blk, v, getattr(M, "edges", None), getattr(M, "cols", None))
            if r == nu0:
                st["eq_cases"] += 1
                # validity: equality must hold here (sanity of the harness)
                assert pr["gain"] == (k - nu0) * pr["tau"], inst
                assert pr["nu_end"] >= nu0, inst
                continue
            st["multi"] += 1
            if pr["nu_end"] < nu0:
                st["MONO_END"] += 1
                ex.setdefault("MONO_END", inst)
            if pr["nu_min_open"] < nu0:
                st["MONO_PATH"] += 1
                ex.setdefault("MONO_PATH", inst)
            if pr["gain"] < pr["lower"]:
                st["ASCENT"] += 1
                ex.setdefault("ASCENT", inst)
            if pr["gain"] != (k - nu0) * pr["tau"]:
                st["F_EQ"] += 1
            sq = pr["nu_seq"]
            if any(y < x for x, y in zip(sq, sq[1:])):
                st["F_PATHMON"] += 1
                ex.setdefault("F_PATHMON", inst)
            if pr["gain"] < (k - nu0) * pr["tau"]:
                st["F_RATE0"] += 1
                ex.setdefault("F_RATE0", inst)
    return st, ex


def path_nonmono(M, blk, k, v, r):
    """F_PATHMON: is nu(L(s)) nondecreasing along the open intervals?"""
    a, pcs, tau = lc.block(M, blk, k, v, r)
    prev = None
    for item in lc.path_intervals(M, blk, k, v, pcs):
        if item[0] != "open":
            continue
        nu, _ = lc.nu_state(M, blk, k, item[3])
        if prev is not None and nu < prev:
            return True
        prev = nu
    return False


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(7100 + s, budget) for s in range(workers)])
    tot = {}
    exs = {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
