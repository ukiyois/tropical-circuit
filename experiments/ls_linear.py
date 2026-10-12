"""Theorem 5.1 check: linear convergence of the LS iteration.

At every LS iteration from state v (p the potentials, gap = Opt - Psi(p) > 0):
  T51a   gap <= k (2q - 1) tau,  tau = tau_{k-1}(v), q = max over components of the
         number of distinct values of a minimum base of v in that component;
  T51b   gap' <= gap - tau  (Proposition 2.1), hence gap' <= (1 - 1/(k(2q-1))) gap;
  T51c   tau >= t*/(2q-1), t* = least theta of a rainbow base (base enumeration);
false variants (discrimination): F1 gap <= (2q-1) tau; F2 gap <= k tau;
F3 gap <= k t* / 2.  Also the bound T_LS <= 1 + k(2k-1) ln(k W) for integer w.
Usage: python ls_linear.py workers seconds"""
import math
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_search_drop import rmat, rweights
from ls_mono_random import has_rainbow_base


def q_of(M, v):
    order = sorted(range(M.m), key=lambda e: v[e])
    B = M.greedy(order)
    q = 0
    for c in range(M.ncomp):
        vals = {v[e] for e in sc.bits(B & M.comp_mask[c])}
        q = max(q, len(vals))
    return max(q, 1)


def tstar(M, blk, k, v, bases):
    best = None
    for B in bases:
        if len({blk[e] for e in sc.bits(B)}) == k:
            th = sc.theta(M, v, B)
            best = th if best is None else min(best, th)
    return best


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "iters": 0, "T51a": 0, "T51b": 0, "T51c": 0, "F1": 0, "F2": 0, "F3": 0,
          "TBOUND": 0, "maxT": 0, "max_ratio": 0.0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = rmat(rng)
        k = M.k
        if k < 3 or M.m > 10:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        w = rweights(rng, M.m)
        bases = sc.all_bases(M)
        opt = sc.opt_rainbow(M, blk, k, w, bases)
        st["runs"] += 1
        v = list(w)
        p = [0] * k
        T = 0
        while True:
            nu, _ = lc.nu_state(M, blk, k, v)
            psi = sum(p) + sc.beta(M, v)
            gap = opt - psi
            if nu >= k:
                assert gap == 0
                break
            assert gap > 0
            a, pcs, tau = lc.block(M, blk, k, v, k - 1)
            q = q_of(M, v)
            ts = tstar(M, blk, k, v, bases)
            st["iters"] += 1
            inst = (kind, M.m, k, blk, getattr(M, "edges", None), getattr(M, "cols", None), list(v))
            if gap > k * (2 * q - 1) * tau:
                st["T51a"] += 1
                ex.setdefault("T51a", inst)
            if tau * (2 * q - 1) < ts:
                st["T51c"] += 1
                ex.setdefault("T51c", inst)
            if gap > (2 * q - 1) * tau:
                st["F1"] += 1
            if gap > k * tau:
                st["F2"] += 1
            if 2 * gap > k * ts:
                st["F3"] += 1
            st["max_ratio"] = max(st["max_ratio"], gap / (k * (2 * q - 1) * tau))
            v = lc.shift(v, blk, a)
            p = [p[b] + a[b] for b in range(k)]
            T += 1
            gap2 = opt - (sum(p) + sc.beta(M, v))
            if gap2 > gap - tau:
                st["T51b"] += 1
                ex.setdefault("T51b", inst)
        W = max(w) - min(w)
        if W > 0 and T > 1 + k * (2 * k - 1) * math.log(k * W):
            st["TBOUND"] += 1
        st["maxT"] = max(st["maxT"], T)
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(41000 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            if key in ("maxT", "max_ratio"):
                tot[key] = max(tot.get(key, 0), val)
            else:
                tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
