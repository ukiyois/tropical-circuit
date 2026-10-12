"""B1: hill climbing for long stages on capacitated transportation instances
(type-compressed PO-SL, exact).  Objective: the longest stage.
Usage: python stage_transport_search.py p q U budget"""
import random
import sys
import time
from multiprocessing import Pool

from stage_transport_fast import Transport, min_cost_flow


def evaluate(inst):
    a, b, cap, w = inst
    if sum(a) != sum(b) or min_cost_flow(a, b, cap, w) is None:
        return None
    T = Transport(a, b, cap, w)
    try:
        P, lens = T.schedule()
    except RuntimeError:
        return None
    if T.psi(P) != min_cost_flow(a, b, cap, w):
        return ("WRONG", inst)
    return max(lens.values()) if lens else 0


def mutate(inst, rng, U):
    a, b, cap, w = inst
    a, b, cap, w = list(a), list(b), dict(cap), dict(w)
    op = rng.random()
    edges = list(cap)
    if op < 0.45:
        e = rng.choice(edges)
        f = rng.choice(edges)
        g = rng.choice(edges)
        w[e] = (w[f] + w[g]) // 2 if rng.random() < 0.5 else max(0, w[e] + rng.randint(-(1 << 12), 1 << 12))
    elif op < 0.6:
        e = rng.choice(edges)
        w[e] = rng.randrange(1 << rng.randint(1, 20))
    elif op < 0.8:
        e = rng.choice(edges)
        cap[e] = max(1, min(U, cap[e] + rng.choice([-1, 1, -U // 4 or -1, U // 4 or 1])))
    else:
        i, i2 = rng.randrange(len(a)), rng.randrange(len(a))
        j, j2 = rng.randrange(len(b)), rng.randrange(len(b))
        d = rng.choice([1, 2])
        if a[i] - d >= 1 and b[j] - d >= 1:
            a[i] -= d; a[i2] += d; b[j] -= d; b[j2] += d
    return (a, b, cap, w)


def hill(args):
    seed, p, q, U, budget = args
    from stage_transport_fast import random_instance
    rng = random.Random(seed)
    t0 = time.time()
    best = (-1, None)
    while time.time() - t0 < budget:
        cur = random_instance(rng, p, q, U)
        s = evaluate(cur)
        if s is None or isinstance(s, tuple):
            continue
        stall = 0
        while stall < 300 and time.time() - t0 < budget:
            cand = mutate(cur, rng, U)
            s2 = evaluate(cand)
            stall += 1
            if s2 is None:
                continue
            if isinstance(s2, tuple):
                return (999, s2)
            if s2 >= s:
                if s2 > s:
                    stall = 0
                cur, s = cand, s2
        if s > best[0]:
            best = (s, cur)
    return best


if __name__ == "__main__":
    p, q, U, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    with Pool(14) as pool:
        res = pool.map(hill, [(s, p, q, U, budget) for s in range(14)])
    res.sort(key=lambda x: -x[0])
    print(f"p={p} q={q} U={U}: longest stage found {res[0][0]}  (bound p(m0^2/4+1) = {p * ((p*q)**2 // 4 + 1)})")
    print("instance", res[0][1])
