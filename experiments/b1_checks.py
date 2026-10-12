"""B1: random checks of the lemmas of docs/phase3-b1-warmstart-2026-10-12.md.

Part A (sinks).  Random sinks (edges with values, capacities kappa, demand b,
a subset A of the edges): Lemma 3.2 (min-max formula = eq. (rank-mu)), and the
sink comparison of Lemma 3.3:
    g(A; kappa, b) >= 2 g(A; kappa', b') - max(L_A, G_notA - beta),
L_A = sum_{A} (2 kappa' - kappa)^+, G_notA = sum_{not A} (kappa - 2 kappa')^+,
beta = b - 2 b'.  Discriminating variants (must fail somewhere):
    V1: loss allowance L_A only;  V2: G_notA - beta only;
    V3: min instead of max;       V4: (G_notA - 2 beta) in place of G - beta.
Part B (pairs).  Random feasible pairs I, I' on one bipartite graph, potentials
P from the schedule of I' started at a random symmetric state (so nu0^{I'}(P) =
F'), values v = w - P.  Checks: Lemma 3.1 (max-flow deficit = compressed Rado
formula), Theorem 3.4 for every source set A, and the variant without the
alpha(A) term (must fail).
Part C (chains).  Random instances, floor chain and balanced chain, P from the
real scaled schedule: Corollary 3.5 (floor chain) and Corollary 3.7 (balanced
chain) for every A and every restart; |Delta_e| <= 1, |alpha|, |beta| <= 1 on
the balanced chain.
Usage: python b1_checks.py [workers] [scale]
"""
import itertools
import random
import sys
from multiprocessing import Pool

from b1_core import (Transport, unit, values, g_sink, g_minmax, rank_v, deficit_rado,
                     comparison_terms, chain_floor, chain_balanced, feasible_flow,
                     run_scaled, min_cost_flow, INF_CAP)


# ------------------------------------------------------------------ Part A
def part_a(seed, trials):
    rng = random.Random(seed)
    stats = {"cases": 0, "minmax_fail": 0, "cmp_fail": 0, "V1": 0, "V2": 0, "V3": 0, "V4": 0}
    for _ in range(trials):
        n = rng.randint(1, 6)
        edges = list(range(n))
        vmax = rng.choice([1, 2, 4, 10])
        v = {e: rng.randint(0, vmax) for e in edges}
        kap2 = {e: rng.randint(0, 6) for e in edges}
        kap = {e: max(0, 2 * kap2[e] + rng.randint(-3, 3)) for e in edges}
        if rng.random() < 0.3:
            kap = {e: rng.randint(0, 14) for e in edges}
        tot, tot2 = sum(kap.values()), sum(kap2.values())
        b2 = rng.randint(0, tot2)
        b = rng.randint(0, tot)
        if rng.random() < 0.5:
            b = min(tot, max(0, 2 * b2 + rng.randint(-3, 3)))
        for mask in range(1 << n):
            inA = {e: bool(mask >> e & 1) for e in edges}
            g = g_sink(kap, b, v, edges, inA)
            g2 = g_sink(kap2, b2, v, edges, inA)
            stats["cases"] += 1
            if g != g_minmax(kap, b, v, edges, inA) or g2 != g_minmax(kap2, b2, v, edges, inA):
                stats["minmax_fail"] += 1
            L = sum(max(2 * kap2[e] - kap[e], 0) for e in edges if inA[e])
            G = sum(max(kap[e] - 2 * kap2[e], 0) for e in edges if not inA[e])
            beta = b - 2 * b2
            if g < 2 * g2 - max(L, G - beta):
                stats["cmp_fail"] += 1
            if g < 2 * g2 - L:
                stats["V1"] += 1
            if g < 2 * g2 - (G - beta):
                stats["V2"] += 1
            if g < 2 * g2 - min(L, G - beta):
                stats["V3"] += 1
            if g < 2 * g2 - max(L, G - 2 * beta):
                stats["V4"] += 1
    return stats


# ------------------------------------------------------------------ Part B
def random_pair(rng, p, q):
    while True:
        E = [(i, j) for i in range(p) for j in range(q) if rng.random() < 0.75]
        if not E:
            continue
        x = {e: rng.randint(0, 6) for e in E}
        x2 = {e: rng.randint(0, 3) for e in E}
        cap = {e: x[e] + rng.choice([0, 0, 1, 2, 5, INF_CAP]) for e in E}
        cap2 = {e: x2[e] + rng.choice([0, 0, 1, 3, INF_CAP]) for e in E}
        a = [sum(x[e] for e in E if e[0] == i) for i in range(p)]
        b = [sum(x[e] for e in E if e[1] == j) for j in range(q)]
        a2 = [sum(x2[e] for e in E if e[0] == i) for i in range(p)]
        b2 = [sum(x2[e] for e in E if e[1] == j) for j in range(q)]
        if sum(a) == 0 or sum(a2) == 0:
            continue
        return (a, b, cap), (a2, b2, cap2), E


def part_b(seed, trials):
    rng = random.Random(seed)
    st = {"pairs": 0, "sets": 0, "rado_fail": 0, "thm_fail": 0, "noalpha_fail": 0,
          "max_d": 0, "tight": 0}
    for _ in range(trials):
        p, q = rng.randint(1, 4), rng.randint(1, 4)
        I, I2, E = random_pair(rng, p, q)
        wb = rng.choice([2, 5, 12])
        w = {e: rng.randint(0, wb) for e in E}
        T2 = Transport(I2[0], I2[1], I2[2], w)
        P0 = [rng.randint(-wb, wb) for _ in range(p)]
        P, _ = T2.schedule(P0)
        assert T2.state(P)[0] == T2.F
        T = Transport(I[0], I[1], I[2], w)
        v = values(w, P)
        d_flow = T.F - T.state(P)[0]
        d_rado, _ = deficit_rado(I[0], I[1], I[2], v)
        st["pairs"] += 1
        st["rado_fail"] += d_flow != d_rado
        st["max_d"] = max(st["max_d"], d_flow)
        best_bound = 0
        for rr in range(0, p + 1):
            for A in itertools.combinations(range(p), rr):
                A = frozenset(A)
                dA = sum(I[0][i] for i in A) - rank_v(I[0], I[1], I[2], v, A)
                alphaA, per = comparison_terms(I + (None,), I2 + (None,), v, A)
                bound = alphaA + sum(max(L, G - beta) for (L, G, beta) in per)
                st["sets"] += 1
                st["thm_fail"] += dA > bound
                st["noalpha_fail"] += dA > bound - alphaA
                best_bound = max(best_bound, bound)
        st["tight"] += d_flow == best_bound
    return st


# ------------------------------------------------------------------ Part C
def random_instance(rng, p, q, U):
    while True:
        E = [(i, j) for i in range(p) for j in range(q) if rng.random() < 0.8]
        if not E:
            continue
        x = {e: rng.randint(0, U) for e in E}
        if sum(x.values()) == 0:
            continue
        cap = {e: x[e] + rng.choice([0, 0, 1, rng.randint(0, U), INF_CAP]) for e in E}
        return x, cap, E


def floor_bound(I, I2, A, deg):
    """Corollary 3.5: alpha(A) + gamma#(A) + sum_{i not in A} alpha_i (deg i - 1)."""
    a, b, cap = I[0], I[1], I[2]
    a2, cap2 = I2[0], I2[2]
    alpha = [a[i] - 2 * a2[i] for i in range(len(a))]
    gam = sum(1 for e in cap if e[0] in A and cap2[e] <= a2[e[0]] and cap[e] < 2 * cap2[e])
    return (sum(alpha[i] for i in A) + gam
            + sum(alpha[i] * (deg[i] - 1) for i in range(len(a)) if i not in A))


def part_c(seed, trials):
    rng = random.Random(seed)
    st = {"restarts_floor": 0, "restarts_bal": 0, "thm_fail": 0, "floorcor_fail": 0,
          "floor_global_fail": 0, "bal_fail": 0, "bal_delta_fail": 0, "max_floor": 0,
          "max_bal": 0, "correct": 0, "runs": 0, "max_bal_minus_m0": -10 ** 9}
    for _ in range(trials):
        p, q = rng.randint(1, 4), rng.randint(1, 4)
        U = rng.choice([3, 8, 30])
        x0, cap, E = random_instance(rng, p, q, U)
        m0 = len(E)
        wb = rng.choice([3, 20, 1 << 12])
        w = {e: rng.randint(0, wb) for e in E}
        deg = [sum(1 for e in E if e[0] == i) for i in range(p)]
        for kind, ch in (("floor", chain_floor), ("bal", chain_balanced)):
            insts = ch(x0, cap, p, q)
            # potentials along the scaled schedule (all stages run, so every
            # restart starts from P with nu0^{I_{f+1}} = F_{f+1})
            P = [0] * p
            seq = list(reversed(insts))
            for idx, I in enumerate(seq):
                T = Transport(I[0], I[1], I[2], w)
                if idx > 0 and sum(I[0]) > 0 and sum(seq[idx - 1][0]) > 0:
                    I2 = seq[idx - 1]
                    v = values(w, P)
                    d = T.F - T.state(P)[0]
                    st["restarts_" + kind] += 1
                    for rr in range(0, p + 1):
                        for A in itertools.combinations(range(p), rr):
                            A = frozenset(A)
                            dA = sum(I[0][i] for i in A) - rank_v(I[0], I[1], I[2], v, A)
                            alphaA, per = comparison_terms(I, I2, v, A)
                            bound = alphaA + sum(max(L, G - beta) for (L, G, beta) in per)
                            st["thm_fail"] += dA > bound
                            if kind == "floor":
                                st["floorcor_fail"] += dA > floor_bound(I, I2, A, deg)
                    if kind == "floor":
                        st["max_floor"] = max(st["max_floor"], d)
                        st["floor_global_fail"] += d > m0 * max(q, 2)
                    else:
                        st["max_bal"] = max(st["max_bal"], d)
                        st["max_bal_minus_m0"] = max(st["max_bal_minus_m0"], d - m0)
                        st["bal_fail"] += d > p + q + m0
                        kap, kap2 = unit(I[0], I[2]), unit(I2[0], I2[2])
                        if any(abs(kap[e] - 2 * kap2[e]) > 1 for e in E) or \
                           any(abs(I[0][i] - 2 * I2[0][i]) > 1 for i in range(p)) or \
                           any(abs(I[1][j] - 2 * I2[1][j]) > 1 for j in range(q)):
                            st["bal_delta_fail"] += 1
                if sum(I[0]) > 0:
                    P, _ = T.schedule(P)
            st["runs"] += 1
            st["correct"] += Transport(*insts[0][:3], w).psi(P) == min_cost_flow(*insts[0][:3], w)
    return st


def merge(dicts):
    out = {}
    for d in dicts:
        for k, val in d.items():
            if k.startswith("max"):
                out[k] = max(out.get(k, val), val)
            else:
                out[k] = out.get(k, 0) + val
    return out


if __name__ == "__main__":
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    scale = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    with Pool(workers) as pool:
        ra = merge(pool.starmap(part_a, [(100 + s, 300 * scale) for s in range(workers)]))
        print("Part A (sinks):", ra, flush=True)
        rb = merge(pool.starmap(part_b, [(200 + s, 60 * scale) for s in range(workers)]))
        print("Part B (pairs):", rb, flush=True)
        rc = merge(pool.starmap(part_c, [(300 + s, 25 * scale) for s in range(workers)]))
        print("Part C (chains):", rc, flush=True)
