"""Exhaustive check of three Phase 2b statements on the referee's matroid zoo,
all block assignments (restricted growth strings, rainbow base exists) and all
v in {0..L}^m with min v = 0:

  (W)  Window lemma: every PO-SL cluster at scale t in a component K has value
       range <= (2 q_K - 1) t, q_K = number of distinct values of a minimum base
       of v inside K (so <= (2 rank(K) - 1) t).
  (S)  Scale sandwich: every base B of N(t) has theta(B) <= (2 q - 1) t with
       q = max_K q_K; that is P_t <= Bases N(t) <= P_{(2q-1)t}.
  (T1) Stage one: at every state with nu0 = 1 < k, one PO-SL update gives nu0 >= 2.
Usage: python stage_verify_lemmas.py L [names...]"""
import itertools
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import exhaustive as EX  # noqa: E402
import stage_core as sc  # noqa: E402


def zoo_sc(name):
    Mr = EX.matroid_zoo()[name][0]()
    return sc.from_rank_table(Mr.m, Mr.R)


def check_state(M, bases, blk, k, v, stats):
    m = M.m
    order = sorted(range(m), key=lambda e: v[e])
    B = M.greedy(order)
    q = {}
    for c in range(M.ncomp):
        q[c] = len({v[e] for e in sc.bits(B) if M.comp[e] == c})
    qmax = max(q.values()) if q else 0
    for t in sc.levels_of(v):
        u = sc.posl_u(M, v, t)
        # (W)
        groups = {}
        for e in range(m):
            if u[e] <= m:
                groups.setdefault((M.comp[e], u[e]), []).append(v[e])
        for (c, _), vals in groups.items():
            stats["W"] += 1
            if max(vals) - min(vals) > (2 * q[c] - 1) * t:
                stats["W_fail"] += 1
        # (S)
        N = sc.MinBase(M, u)
        for Bb in bases:
            if N.rank(Bb) == M.k:
                stats["S"] += 1
                if sc.theta(M, v, Bb) > (2 * qmax - 1) * t:
                    stats["S_fail"] += 1
    nu0, S0 = sc.state(M, blk, k, v)
    if nu0 == 1 and k > 1:
        stats["T1"] += 1
        tau, lam, a, _ = sc.update(M, blk, k, v, 1)
        v2 = sc.shift(v, blk, a)
        nu1, _ = sc.state(M, blk, k, v2)
        if nu1 < 2:
            stats["T1_fail"] += 1
            if stats["T1_ex"] is None:
                stats["T1_ex"] = (blk, v)


def work(args):
    name, L, part, nparts = args
    M = zoo_sc(name)
    k = M.k
    bases = sc.all_bases(M)
    stats = {"W": 0, "W_fail": 0, "S": 0, "S_fail": 0, "T1": 0, "T1_fail": 0, "T1_ex": None, "states": 0}
    idx = 0
    for blk in EX.rgs(M.m, k):
        if not any(len({blk[e] for e in sc.bits(B)}) == k for B in bases):
            continue
        for v in itertools.product(range(L + 1), repeat=M.m):
            if min(v) != 0:
                continue
            idx += 1
            if idx % nparts != part:
                continue
            stats["states"] += 1
            check_state(M, bases, blk, k, list(v), stats)
    return stats


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    names = sys.argv[2:] or ["U24", "U35", "U36", "MK4", "W3", "P6dbl", "K4minus+par", "C4+chord par",
                             "sumU12U23", "gf3_U24", "U23+loop+coloop"]
    nparts = 30
    for name in names:
        t0 = time.time()
        with Pool(nparts) as pool:
            res = pool.map(work, [(name, L, p, nparts) for p in range(nparts)])
        tot = {}
        ex = None
        for s in res:
            for key, val in s.items():
                if key == "T1_ex":
                    ex = ex or val
                else:
                    tot[key] = tot.get(key, 0) + val
        print(f"{name}: L={L} {tot} example={ex} time {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
