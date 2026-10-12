"""Goal 2 diagnostics: the tie points of the path of a multi-stage block.

At a breakpoint s1 inside a piece (direction X = E_A, A = Av(N(s1))), with tie matroid
T = M^{v(s1)}, the matroids on the two adjacent open intervals are
    before  T^{+1_X} = T/X^c (+) T|X^c,     after  T^{-1_X} = T|X (+) T/X,
so  nu(before) = nu_A(T/X^c) + nu_{A^c}(T|X^c),  nu(after) = nu_A(T|X) + nu_{A^c}(T/X),
nu_Q the rainbow number for the blocks of Q.  We record the gain on A,
gA = nu_A(T|X) - nu_A(T/X^c) >= 0, and the loss on A^c, lC = nu_{A^c}(T|X^c) -
nu_{A^c}(T/X) >= 0, and at piece boundaries nu before / at / after.
Usage: python ls_ties.py workers seconds"""
import random
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_search_drop import rmat, rweights
from ls_mono_random import has_rainbow_base


class Restr:
    """A matroid given by a rank function on masks (restriction/contraction views)."""

    def __init__(self, m, rank):
        self.m = m
        self.rank = rank

    def indep(self, S):
        return self.rank(S) == sc.popcount(S)


def rainbow_on(T, blk, k, Q, ground):
    """Rainbow number of T restricted to ground (mask) for the blocks in Q."""
    sub = [e for e in range(T.m) if ground >> e & 1 and blk[e] in Q]
    if not sub:
        return 0
    smask = sc.mask_of(sub)
    R = Restr(T.m, lambda S: T.rank(S & smask))
    nu, _, _ = sc.rainbow_av(R, blk, k)
    return nu


def contract(T, Y):
    rY = T.rank(Y)
    return Restr(T.m, lambda S: T.rank((S & ~Y) | Y) - rY)


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"ties": 0, "gain_pos": 0, "loss_pos": 0, "loss_gt_gain": 0, "bound": 0,
          "bound_drop_vs_before": 0, "bound_after_lt_at": 0}
    hist = {}
    ex = {}
    while time.time() - t0 < budget:
        kind, M = rmat(rng)
        k = M.k
        if k < 4:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        v = rweights(rng, M.m)
        nu0, _ = lc.nu_state(M, blk, k, v)
        if nu0 >= k - 1:
            continue
        r = k - 1
        a, pcs, tau = lc.block(M, blk, k, v, r)
        cur = list(v)
        prevX = None
        for idx, (c0, c1, nuN, A) in enumerate(pcs):
            Xs = {e for e in range(M.m) if blk[e] in A}
            X = sc.mask_of(Xs)
            Xc = M.full & ~X
            # piece boundary at c0 (idx > 0): before = T^{+1_{X'}}, after = T^{-1_X}
            if idx > 0 and A and prevX is not None:
                T = sc.MinBase(M, cur)
                nb = sc.rainbow_av(sc.MinBase(M, [(cur[e], 1 if prevX >> e & 1 else 0) for e in range(M.m)]), blk, k)[0]
                nt = sc.rainbow_av(T, blk, k)[0]
                na = sc.rainbow_av(sc.MinBase(M, [(cur[e], -1 if X >> e & 1 else 0) for e in range(M.m)]), blk, k)[0]
                st["bound"] += 1
                if na < nb:
                    st["bound_drop_vs_before"] += 1
                    ex.setdefault("BOUND", (kind, M.m, k, blk, getattr(M, "edges", None), w_str(v), idx))
                if na < nt:
                    st["bound_after_lt_at"] += 1
            if A:
                prevX = X
            if not A:
                continue
            ts = set()
            for e in Xs:
                for f in range(M.m):
                    if f in Xs:
                        continue
                    d = cur[e] - cur[f]
                    if 0 < d < c1 - c0:
                        ts.add(d)
            for d in sorted(ts):
                vt = [cur[e] - d if e in Xs else cur[e] for e in range(M.m)]
                T = sc.MinBase(M, vt)
                Tm = Restr(M.m, T.rank)
                Ac = [b for b in range(k) if b not in A]
                nA_TX = rainbow_on(Tm, blk, k, A, X)
                nA_TXc = rainbow_on(contract(Tm, Xc), blk, k, A, X)
                nC_TXc = rainbow_on(Tm, blk, k, Ac, Xc)
                nC_TX = rainbow_on(contract(Tm, X), blk, k, Ac, Xc)
                gA = nA_TX - nA_TXc
                lC = nC_TXc - nC_TX
                st["ties"] += 1
                st["gain_pos"] += gA > 0
                st["loss_pos"] += lC > 0
                key = (gA, lC)
                hist[key] = hist.get(key, 0) + 1
                if lC > gA:
                    st["loss_gt_gain"] += 1
                    ex.setdefault("TIE", (kind, M.m, k, blk, getattr(M, "edges", None), w_str(v), idx, d))
            cur = [cur[e] - (c1 - c0) if e in Xs else cur[e] for e in range(M.m)]
    return st, hist, ex


def w_str(v):
    return [str(x) for x in v]


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(13100 + s, budget) for s in range(workers)])
    tot, H, exs = {}, {}, {}
    for st, hist, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in hist.items():
            H[key] = H.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    print("(gain on A, loss on A^c) histogram:", sorted(H.items()), flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
