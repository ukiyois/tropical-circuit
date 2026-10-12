"""Goal 2, the abstract refinement claim.

Claim R.  Let N be a matroid of rank k on E with blocks blk : E -> [k], A = Av(N),
X = E_A, and u in R^E arbitrary; T = N^u.  Then
    nu(T|X (+) T/X)  >=  nu(T/X^c (+) T|X^c),
i.e. nu(T^{-1_X}) >= nu(T^{+1_X}): the bases of T with the most elements in X meet at
least as many blocks as those with the fewest.  Equivalently h -> nu(N^{u - h 1_X}) is
nondecreasing on the open intervals between breakpoints.
Also tested (false variants, to show the harness discriminates):
  V_ANY    the same with X = E_Q for a random set of blocks Q (not Av(N))
  V_SUPER  with A replaced by a random superset of Av(N)
  V_SUB    with A replaced by a random proper subset of Av(N)
  V_DEFMAX with A replaced by a random maximizer of the deficiency of N (not the least)
Matroids N: random graphic, binary, uniform, sparse paving, sums, and min-base matroids
M^w of those (so that N has the shape of a PO-SL matroid M^{u_t}).
Usage: python ls_refine.py workers seconds"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from ls_mono_random import random_matroid, has_rainbow_base


def T_pm(N, u, X, sign):
    """The min-base matroid of N at u - sign*eps*1_X, eps -> 0+ (lexicographic)."""
    m = N.m
    # weights (u, -sign*[e in X]) compared lexicographically: encode as pairs
    w = [(u[e], -sign if X >> e & 1 else 0) for e in range(m)]
    return sc.MinBase(N, w)


def nu_of(T, blk, k):
    return sc.rainbow_av(T, blk, k)[0]


def deficiency(N, blk, k, Q):
    return len(Q) - N.rank(sc.mask_of(e for e in range(N.m) if blk[e] in Q))


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"cases": 0, "CLAIM": 0, "V_ANY": 0, "V_SUPER": 0, "V_SUB": 0, "V_DEFMAX": 0,
          "n_any": 0, "n_super": 0, "n_sub": 0, "n_defmax": 0, "nontriv": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = random_matroid(rng)
        k = M.k
        if k < 3:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k:
            continue
        if rng.random() < 0.6:
            w0 = [rng.randint(0, 3) for _ in range(M.m)]
            N = sc.MinBase(M, w0)
            N.k = k
        else:
            w0 = None
            N = M
        nuN, A, _ = sc.rainbow_av(N, blk, k)
        if nuN >= k:
            continue
        X = sc.mask_of(e for e in range(M.m) if blk[e] in A)
        for _ in range(4):
            u = [rng.randint(0, 4) for _ in range(M.m)]
            T = sc.MinBase(N, u)
            # T as a matroid object for refinement: wrap rank
            Tm = sc.Matroid(M.m, T.rank, "T")
            st["cases"] += 1
            nplus = nu_of(T_pm(Tm, [0] * M.m, X, +1), blk, k)
            nminus = nu_of(T_pm(Tm, [0] * M.m, X, -1), blk, k)
            if nplus != nminus:
                st["nontriv"] += 1
            if nplus < nminus:
                st["CLAIM"] += 1
                ex.setdefault("CLAIM", (kind, M.m, k, blk, getattr(M, "edges", None), getattr(M, "cols", None), w0, u, sorted(A), nplus, nminus))
            # variants
            Q = {b for b in range(k) if rng.random() < 0.5}
            XQ = sc.mask_of(e for e in range(M.m) if blk[e] in Q)
            st["n_any"] += 1
            if nu_of(T_pm(Tm, [0] * M.m, XQ, +1), blk, k) < nu_of(T_pm(Tm, [0] * M.m, XQ, -1), blk, k):
                st["V_ANY"] += 1
            rest = [b for b in range(k) if b not in A]
            if rest:
                Q = set(A) | set(rng.sample(rest, rng.randint(1, len(rest))))
                XQ = sc.mask_of(e for e in range(M.m) if blk[e] in Q)
                st["n_super"] += 1
                if nu_of(T_pm(Tm, [0] * M.m, XQ, +1), blk, k) < nu_of(T_pm(Tm, [0] * M.m, XQ, -1), blk, k):
                    st["V_SUPER"] += 1
                    # is Q a deficiency maximizer?
                    if deficiency(N, blk, k, Q) == k - nuN:
                        st["V_DEFMAX"] += 1
                if deficiency(N, blk, k, Q) == k - nuN:
                    st["n_defmax"] += 1
            if len(A) >= 1:
                Al = sorted(A)
                Q = set(rng.sample(Al, rng.randint(0, len(Al) - 1)))
                XQ = sc.mask_of(e for e in range(M.m) if blk[e] in Q)
                st["n_sub"] += 1
                if nu_of(T_pm(Tm, [0] * M.m, XQ, +1), blk, k) < nu_of(T_pm(Tm, [0] * M.m, XQ, -1), blk, k):
                    st["V_SUB"] += 1
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(5100 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
