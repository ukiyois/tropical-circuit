"""Block-constant runs of the local form of Proposition 2.4.

M' = M^u for a random u with ties (so M' is a direct sum of minors of M), required to have
a rainbow base; linkage classes Lambda = K cap {u = l} (K a component of M); random state
x in R^k (values x_{blk e}).  Iterate x -> x - a'(x), a' the block of the family N'_Lambda
up to its first time tau' with nu = k, until nu(M'^{x_blk}) = k.  Records the number of
steps T' against k and against the number of distinct values of x; checks the final
Psi' = Opt' of the block-constant problem (all rainbow bases of M' have the same x-weight
sum_b x_b, so Opt' = sum x_b).
Claims tested:  BC1  T' <= k;   BC2  T' <= number of distinct values of x.
False variants:  BCF1  T' <= k - 2;  BCF2  T' <= (distinct values) - 2.
Usage: python lsu_bc_local.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc
from lsu_local import make_family, Wrap
from lsu_blockconst import rand_x


def bc_run(Mp, blk, k, x, fam, cap=200):
    xv = list(x)
    T = 0
    while True:
        v = [xv[blk[e]] for e in range(Mp.m)]
        nu, _, _ = sc.rainbow_av(Wrap(sc.MinBase(Mp, v)), blk, k)
        if nu == k:
            return T, xv
        a, pcs, tau = lc.block(Mp, blk, k, v, k - 1, fam)
        if not any(a):
            raise RuntimeError("zero block")
        xv = [xv[b] - a[b] for b in range(k)]
        T += 1
        if T > cap:
            raise RuntimeError("cap")


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "BC1": 0, "BC2": 0, "BCF1": 0, "BCF2": 0, "maxT": 0, "OPT": 0,
          "disconnected_Mp": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        u = [rng.randint(0, rng.choice([1, 2, 3])) for _ in range(M.m)]
        Mp = Wrap(sc.MinBase(M, u))
        nu, _, _ = sc.rainbow_av(Mp, blk, k)
        if nu < k:
            continue
        lam = [(M.comp[e], u[e]) for e in range(M.m)]
        fam = make_family(lam)
        x = rand_x(rng, k)
        try:
            T, xf = bc_run(Mp, blk, k, x, fam)
        except RuntimeError as err:
            st["OPT"] += 1
            ex.setdefault("ERR", (uc.describe(M), blk, u, x, str(err)))
            continue
        st["runs"] += 1
        st["maxT"] = max(st["maxT"], T)
        nv = len(set(x))
        if T > k:
            st["BC1"] += 1
            ex.setdefault("BC1", (uc.describe(M), blk, u, x, T))
        if T > nv:
            st["BC2"] += 1
            ex.setdefault("BC2", (uc.describe(M), blk, u, x, T))
        st["BCF1"] += T > k - 2
        st["BCF2"] += T > nv - 2
        # Psi' at the end equals sum_b x_b (Opt' of the block-constant problem)
        p = [x[b] - xf[b] for b in range(k)]
        v = [xf[blk[e]] for e in range(M.m)]
        order = sorted(range(M.m), key=lambda e: v[e])
        B = 0
        for e in order:
            if Mp.rank(B | (1 << e)) > sc.popcount(B):
                B |= 1 << e
        if sum(p) + sum(v[e] for e in sc.bits(B)) != sum(x):
            st["OPT"] += 1
            ex.setdefault("OPT", (uc.describe(M), blk, u, x))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 9000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = max(tot.get(key, val), val) if key.startswith("max") else tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
