"""B1: Proposition 5.3, general min-cost flow through uncapacitated transportation.

Random digraphs without loops (n <= 4 nodes, m <= 6 arcs, capacities up to U),
demands from a random feasible flow, real-valued (integer, possibly negative)
costs.  T(D): one source per arc (supply u_a), one sink per node (demand
d_v + u(out(v))), edges (a, head) of cost w_a and (a, tail) of cost 0, both
uncapacitated.  Runs the scaled schedule on the floor chain with X = 2m,
checks every restart deficit against |O_f| and 2m, and compares the final
Psi with the minimum cost of D computed by brute force over all integral flows.
With the environment variable B1_BIGU=1, capacities go up to 1000 and the
reference is the exact min-cost flow of T(D) (stage_transport.min_cost_flow,
successive shortest paths from the zero flow on an acyclic network).
Usage: python b1_mincostflow.py workers trials"""
import itertools
import os
BIGU = int(os.environ.get("B1_BIGU", "0"))
import random
import sys
from multiprocessing import Pool

from b1_core import Transport, chain_floor, chain_balanced, INF_CAP


def brute_min_cost(n, arcs, u, d, w):
    best = None
    for phi in itertools.product(*[range(ua + 1) for ua in u]):
        net = [0] * n
        for (s, t), f in zip(arcs, phi):
            net[t] += f
            net[s] -= f
        if net == d:
            cost = sum(wa * f for wa, f in zip(w, phi))
            best = cost if best is None else min(best, cost)
    return best


def reduction(n, arcs, u, d, w, phi0):
    m = len(arcs)
    a = list(u)
    b = [d[v] + sum(u[k] for k, (s, t) in enumerate(arcs) if s == v) for v in range(n)]
    cap, cost, x0 = {}, {}, {}
    for k, (s, t) in enumerate(arcs):
        cap[(k, t)], cost[(k, t)], x0[(k, t)] = INF_CAP, w[k], phi0[k]
        cap[(k, s)], cost[(k, s)], x0[(k, s)] = INF_CAP, 0, u[k] - phi0[k]
    return a, b, cap, cost, x0


def run(args):
    seed, trials = args
    rng = random.Random(seed)
    st = {"inst": 0, "restarts": 0, "fail_O": 0, "fail_2m": 0, "wrong": 0, "max_d": 0,
          "max_upd": 0, "bal_wrong": 0}
    done = 0
    while done < trials:
        n = rng.randint(2, 4)
        m = rng.randint(1, 6)
        arcs = []
        for _ in range(m):
            s, t = rng.sample(range(n), 2)
            arcs.append((s, t))
        U = rng.choice([1, 2, 3]) if BIGU == 0 else rng.choice([10, 100, 1000])
        u = [rng.randint(0, U) for _ in range(m)]
        if sum(u) == 0 or any(x > 0 for x in []):
            continue
        phi0 = [rng.randint(0, ua) for ua in u]
        d = [0] * n
        for (s, t), f in zip(arcs, phi0):
            d[t] += f
            d[s] -= f
        wb = rng.choice([3, 30])
        w = [rng.randint(-wb, wb) for _ in range(m)]
        a, b, cap, cost, x0 = reduction(n, arcs, u, d, w, phi0)
        if BIGU == 0:
            opt = brute_min_cost(n, arcs, u, d, w)
        else:
            from stage_transport import min_cost_flow
            capf = {e: sum(u) + 1 for e in cap}
            opt = min_cost_flow(a, b, capf, cost)
        done += 1
        st["inst"] += 1
        X = 2 * m
        for kind, ch in (("floor", chain_floor), ("bal", chain_balanced)):
            insts = ch(x0, cap, m, n)
            P = [0] * m
            seq = list(reversed(insts))
            upd = 0
            for idx, I in enumerate(seq):
                if sum(I[0]) == 0:
                    continue
                T = Transport(I[0], I[1], I[2], cost)
                rmin = 1
                if idx > 0 and sum(seq[idx - 1][0]) > 0:
                    dd = T.F - T.state(P)[0]
                    if kind == "floor":
                        st["restarts"] += 1
                        nodd = sum(1 for e, xe in I[3].items() if xe % 2 == 1)
                        st["fail_O"] += dd > nodd
                        st["fail_2m"] += dd > X
                        st["max_d"] = max(st["max_d"], dd)
                    rmin = max(1, T.F - (X if kind == "floor" else 2 * m + (m + n) // 2))
                P, lens = T.schedule(P, rmin=rmin)
                upd += sum(lens.values())
            psi = Transport(*insts[0][:3], cost).psi(P)
            if kind == "floor":
                st["wrong"] += psi != opt
                st["max_upd"] = max(st["max_upd"], upd)
            else:
                st["bal_wrong"] += psi != opt
    return st


if __name__ == "__main__":
    workers, trials = int(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(run, [(700 + s, trials) for s in range(workers)])
    out = {}
    for d in res:
        for k, v in d.items():
            out[k] = max(out.get(k, v), v) if k.startswith("max") else out.get(k, 0) + v
    print(out, flush=True)
