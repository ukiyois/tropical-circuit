"""B1: does the static scaled schedule with X = p + q + 2 m0 (floor chain) fail?

Faithful simulation of the static circuit: in phase f, stages
r = max(1, F_f - X) .. F_f - 1, each stage applies K = p (floor(m0^2/4) + 1)
times the circuit of stage r, which computes
    eta_i = sum over levels l_k < tau of (l_{k+1} - l_k) [nu(N(l_k)) <= r] [i in Av(N(l_k))]
(the threshold integral of equation (update-integral)), also at states with
nu0 < r, where Definition def:update does not apply.  The result is compared
with Opt.  Hill climbing over T-like instances: old sources with even flow
entries, new sources with entries in {0, 1}, random costs.  Objective:
(Opt - Psi_static) if positive (failure), else the restart deficit minus X.
Usage: python b1_static_fail.py budget_seconds workers"""
import random
import sys
import time
from multiprocessing import Pool

from b1_core import Transport, chain_floor, min_cost_flow


def circuit_update(T, P, r):
    """The stage-r block of the circuit (integral form), at any state."""
    v = T.values(P)
    levels = sorted({0} | {abs(v[e] - v[f]) for e in T.edges for f in T.edges})
    eta = [0] * T.p
    for k in range(len(levels)):
        nu, av = T.nu_av(T.structure(v, levels[k]))
        if nu >= r + 1:
            break
        if k + 1 == len(levels):
            break
        gap = levels[k + 1] - levels[k]
        for i in av:
            eta[i] += gap
    return eta


def static_run(insts, w, X, K):
    p = len(insts[0][0])
    P = [0] * p
    first = True
    for (af, bf, cf, xf) in reversed(insts):
        if sum(af) == 0:
            continue
        T = Transport(af, bf, cf, w)
        rmin = 1 if first else max(1, T.F - X)
        for r in range(rmin, T.F):
            for _ in range(K):
                nu0, _ = T.state(P)
                if nu0 > r:
                    break
                eta = circuit_update(T, P, r)
                if not any(eta):
                    break
                P = [P[i] + eta[i] for i in range(p)]
        first = False
    return P


def build(st):
    old, new, D, xold, slack, w = st
    p = old + new
    x0, cap = {}, {}
    for j in range(D):
        for i in range(old):
            x0[(i, j)] = xold[(i, j)]
            cap[(i, j)] = xold[(i, j)] + slack[(i, j)]
        for t in range(old, p):
            x0[(t, j)] = 1
            cap[(t, j)] = D
    return p, D, x0, cap, w


def evaluate(st):
    p, q, x0, cap, w = build(st)
    m0 = len(cap)
    X = p + q + 2 * m0
    K = p * (m0 * m0 // 4 + 1)
    insts = chain_floor(x0, cap, p, q)
    if len(insts) < 2 or sum(insts[1][0]) == 0:
        return None
    a, b, c, _ = insts[0]
    opt = min_cost_flow(a, b, c, w)
    if opt is None:
        return None
    # restart deficit with the real schedule (all stages) for comparison
    P = [0] * p
    for I in reversed(insts[1:]):
        if sum(I[0]):
            P, _ = Transport(I[0], I[1], I[2], w).schedule(P)
    T0 = Transport(a, b, c, w)
    d = T0.F - T0.state(P)[0]
    Ps = static_run(insts, w, X, K)
    psi = T0.psi(Ps)
    nu_end = T0.state(Ps)[0]
    gap = opt - psi
    score = 10 ** 6 * gap if gap > 0 else (d - X)
    return score, d, X, gap, nu_end, T0.F


def mutate(st, rng):
    old, new, D, xold, slack, w = st
    xold, slack, w = dict(xold), dict(slack), dict(w)
    op = rng.random()
    keys = list(w)
    if op < 0.6:
        e = rng.choice(keys)
        w[e] = max(0, w[e] + rng.choice([-2, -1, 1, 2, rng.randint(-20, 20)]))
    elif op < 0.8:
        e = rng.choice(list(xold))
        xold[e] = max(0, xold[e] + rng.choice([-2, 2]))
    else:
        e = rng.choice(list(slack))
        slack[e] = rng.choice([0, 1, 2, 5])
    return (old, new, D, xold, slack, w)


def hill(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-10 ** 9, None, None)
    while time.time() - t0 < budget:
        old = rng.choice([1, 2])
        new = rng.choice([1, 2])
        D = rng.choice([5, 6, 7])
        xold = {(i, j): 2 * rng.randint(1, 4) for i in range(old) for j in range(D)}
        slack = {e: rng.choice([0, 0, 1]) for e in xold}
        w = {}
        for j in range(D):
            for i in range(old + new):
                w[(i, j)] = rng.randint(0, 12)
        st = (old, new, D, xold, slack, w)
        res = evaluate(st)
        if res is None:
            continue
        s = res[0]
        stall = 0
        while stall < 60 and time.time() - t0 < budget:
            cand = mutate(st, rng)
            r2 = evaluate(cand)
            stall += 1
            if r2 is None:
                continue
            if r2[0] >= s:
                if r2[0] > s:
                    stall = 0
                st, s, res = cand, r2[0], r2
            if res[3] > 0:
                return (s, st, res)
        if s > best[0]:
            best = (s, st, res)
    return best


if __name__ == "__main__":
    budget, workers = float(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(hill, [(900 + s, budget) for s in range(workers)])
    res.sort(key=lambda r: -r[0])
    for s, st, r in res:
        if st is None:
            continue
        print(f"score {s}: deficit {r[1]} X {r[2]} Opt-Psi_static {r[3]} nu0_end {r[4]}/{r[5]}", flush=True)
    s, st, r = res[0]
    print("best instance:", st, flush=True)
