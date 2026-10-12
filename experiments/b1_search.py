"""B1: hill climbing for large restart deficits (exact, time-bounded).

State: a p x q bipartite instance given by a flow x0 (entries 0..U), capacity
slacks (cap = x0 + slack, slack possibly INF_CAP), costs w, and a start vector
P_start.  The chain (floor or balanced) is built from x0; the potentials at the
finest restart are those of the scaled schedule run with all stages (mode
'sched'), or, in mode 'adv', the schedule of I_1 started at P_start (any
optimal Lagrange multiplier of I_1 the schedule can reach).  Objective:
deficit - (a reference), the reference being 0, m0, q, p + q, or the bound of
Corollary 3.5 (floor chain).
Usage: python b1_search.py chain mode p q U budget_seconds workers objective
"""
import random
import sys
import time
from multiprocessing import Pool

from b1_core import (Transport, values, chain_floor, chain_balanced, INF_CAP,
                     deficit_rado)


def evaluate(st, p, q, chain, mode):
    x0, slack, w, Pst = st
    E = sorted(x0)
    if sum(x0.values()) == 0:
        return None
    cap = {e: (INF_CAP if slack[e] == "inf" else x0[e] + slack[e]) for e in E}
    insts = chain(x0, cap, p, q)
    if len(insts) < 2 or sum(insts[1][0]) == 0:
        return None
    I0, I1 = insts[0], insts[1]
    if mode == "sched":
        P = [0] * p
        for I in reversed(insts[1:]):
            if sum(I[0]) == 0:
                continue
            P, _ = Transport(I[0], I[1], I[2], w).schedule(P)
    else:
        P, _ = Transport(I1[0], I1[1], I1[2], w).schedule(list(Pst))
    T = Transport(I0[0], I0[1], I0[2], w)
    d = T.F - T.state(P)[0]
    m0 = sum(1 for e in E if cap[e] > 0)
    return d, m0, P, insts


def mutate(st, rng, p, q, U, wb):
    x0, slack, w, Pst = dict(st[0]), dict(st[1]), dict(st[2]), list(st[3])
    E = sorted(x0)
    e = rng.choice(E)
    op = rng.random()
    if op < 0.35:
        x0[e] = max(0, min(U, x0[e] + rng.choice([-2, -1, 1, 2, rng.randint(-U, U)])))
    elif op < 0.5:
        slack[e] = rng.choice([0, 0, 1, 2, rng.randint(0, U), "inf"])
    elif op < 0.8:
        w[e] = rng.choice([rng.randint(0, wb), w[rng.choice(E)], max(0, w[e] + rng.randint(-3, 3))])
    else:
        i = rng.randrange(p)
        Pst[i] = rng.randint(-wb, wb)
    return (x0, slack, w, Pst)


def objective(res, ref, p, q):
    d, m0, P, insts = res
    if ref == "0":
        return d
    if ref == "m0":
        return d - m0
    if ref == "q":
        return d - q
    if ref == "pq":
        return d - p - q
    if ref == "pqm":
        return d - p - q - m0
    raise ValueError(ref)


def hill(args):
    seed, chain_name, mode, p, q, U, budget, ref = args
    chain = chain_floor if chain_name == "floor" else chain_balanced
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None)
    while time.time() - t0 < budget:
        E = [(i, j) for i in range(p) for j in range(q) if rng.random() < 0.85] or [(0, 0)]
        wb = rng.choice([3, 10, 100])
        st = ({e: rng.randint(0, U) for e in E}, {e: rng.choice([0, 1, 2, "inf"]) for e in E},
              {e: rng.randint(0, wb) for e in E}, [rng.randint(-wb, wb) for _ in range(p)])
        res = evaluate(st, p, q, chain, mode)
        if res is None:
            continue
        s = objective(res, ref, p, q)
        stall = 0
        while stall < 400 and time.time() - t0 < budget:
            cand = mutate(st, rng, p, q, U, wb)
            r2 = evaluate(cand, p, q, chain, mode)
            stall += 1
            if r2 is None:
                continue
            s2 = objective(r2, ref, p, q)
            if s2 >= s:
                if s2 > s:
                    stall = 0
                st, s, res = cand, s2, r2
        if s > best[0]:
            best = (s, st, res[0], res[1])
    return best


if __name__ == "__main__":
    chain_name, mode = sys.argv[1], sys.argv[2]
    p, q, U = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    budget, workers = float(sys.argv[6]), int(sys.argv[7])
    ref = sys.argv[8] if len(sys.argv) > 8 else "0"
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, chain_name, mode, p, q, U, budget, ref) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    s, st, d, m0 = res[0]
    print(f"chain={chain_name} mode={mode} p={p} q={q} U={U} ref={ref}: best objective {s} "
          f"(deficit {d}, m0 {m0}, p+q+m0 = {p + q + m0}); all workers: {[r[0] for r in res]}")
    print("x0", st[0])
    print("slack", st[1])
    print("w", st[2])
    print("Pstart", st[3], flush=True)
