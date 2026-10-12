"""B1: a capacity-scaling PO-SL schedule for transportation (type-compressed, exact).

Chain of instances: x_0 a feasible flow of I_0 = I (fixed data, no costs);
x_{f+1} = floor(x_f / 2), I_{f+1} = (row sums of x_{f+1}, column sums of
x_{f+1}, ceil(c_f / 2)).  The schedule runs the coarsest instance from P = 0,
then for f = J-1..0 restarts from the previous potentials and runs only the
stages r >= F_f - X, X = p + q + 2 m0 (the doubling bound of the note).
Checked: the deficit F_f - nu0 at every restart is <= X (so no skipped stage
is ever active), the final Psi equals Opt(I), and the number of updates.
Static cost compared: (phases) * X stages against F stages without scaling.
Usage: python stage_transport_scaling.py p q U trials"""
import math
import random
import sys
from multiprocessing import Pool

from stage_transport_fast import Transport, random_instance, min_cost_flow


def feasible_flow(a, b, cap):
    """A feasible integral flow via max flow (fixed data)."""
    from stage_transport_fast import Flow
    p, q = len(a), len(b)
    S, T = p + q, p + q + 1
    fl = Flow(p + q + 2)
    eidx = {}
    for i in range(p):
        fl.add(S, i, a[i])
    for j in range(q):
        fl.add(p + j, T, b[j])
    for (i, j), c in cap.items():
        eidx[(i, j)] = (i, len(fl.g[i]))
        fl.add(i, p + j, c)
    assert fl.maxflow(S, T) == sum(a)
    x = {}
    for e, (u, k) in eidx.items():
        x[e] = cap[e] - fl.g[u][k][1]
    return x


def chain(a, b, cap):
    p, q = len(a), len(b)
    x = feasible_flow(a, b, cap)
    out = [(list(a), list(b), dict(cap))]
    while sum(out[-1][0]) > 0:
        x = {e: xe // 2 for e, xe in x.items()}
        c_prev = out[-1][2]
        a2 = [sum(x[(i, j)] for j in range(q) if (i, j) in x) for i in range(p)]
        b2 = [sum(x[(i, j)] for i in range(p) if (i, j) in x) for j in range(q)]
        c2 = {e: (c + 1) // 2 for e, c in c_prev.items()}
        out.append((a2, b2, c2))
    return out[::-1]          # coarsest first


def run(args):
    seed, p, q, U, trials = args
    rng = random.Random(seed)
    res = []
    for _ in range(trials):
        a, b, cap, w = random_instance(rng, p, q, U, wbits=rng.choice([6, 20]))
        m0 = len(cap)
        X = p + q + 2 * m0
        insts = chain(a, b, cap)
        P = [0] * p
        worst_deficit, updates, ok = 0, 0, True
        for idx, (ai, bi, ci) in enumerate(insts):
            if sum(ai) == 0:
                continue
            T = Transport(ai, bi, ci, w)
            nu0, _ = T.state(P)
            deficit = T.F - nu0
            worst_deficit = max(worst_deficit, deficit)
            if deficit > X and idx > 0:
                ok = False
            P, lens = T.schedule(P, rmin=max(1, T.F - X) if idx > 0 else 1)
            updates += sum(lens.values())
        Tf = Transport(a, b, cap, w)
        correct = Tf.psi(P) == min_cost_flow(a, b, cap, w)
        res.append((worst_deficit, X, ok, correct, updates, len(insts), sum(a)))
    return res


if __name__ == "__main__":
    p, q, U, trials = map(int, sys.argv[1:5])
    with Pool(28) as pool:
        res = sum(pool.map(run, [(s, p, q, U, trials) for s in range(28)]), [])
    print(f"p={p} q={q} U={U}: instances {len(res)}  max restart deficit {max(r[0] for r in res)} "
          f"(bound X up to {max(r[1] for r in res)})  deficit<=X {sum(r[2] for r in res)}/{len(res)}  "
          f"Psi=Opt {sum(r[3] for r in res)}/{len(res)}  updates max {max(r[4] for r in res)} "
          f"phases max {max(r[5] for r in res)}  F max {max(r[6] for r in res)}", flush=True)
