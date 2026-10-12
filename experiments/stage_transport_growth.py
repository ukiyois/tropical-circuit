"""B1: growth of the PO-SL schedule with the capacities (type-compressed, exact).
For U in a range, random p x q transportation instances with supplies,
demands and capacities up to U and 20-bit costs: max stage length, number of
active stages, total updates, F, and checks Psi = Opt.
Usage: python stage_transport_growth.py p q trials"""
import random
import sys
from multiprocessing import Pool

from stage_transport_fast import Transport, random_instance, min_cost_flow


def work(args):
    seed, p, q, U, trials = args
    rng = random.Random(seed)
    out = []
    for _ in range(trials):
        a, b, cap, w = random_instance(rng, p, q, U)
        T = Transport(a, b, cap, w)
        P, lens = T.schedule()
        ok = T.psi(P) == min_cost_flow(a, b, cap, w)
        out.append((T.F, max(lens.values()) if lens else 0, sum(1 for x in lens.values() if x), sum(lens.values()), ok))
    return out


if __name__ == "__main__":
    p, q, trials = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for U in [1, 2, 4, 8, 16, 32, 64, 128, 256]:
        with Pool(28) as pool:
            res = sum(pool.map(work, [(1000 * U + s, p, q, U, trials) for s in range(28)]), [])
        F = [r[0] for r in res]
        print(f"U={U:4d} instances={len(res)} F mean {sum(F)/len(F):7.1f} max {max(F):5d} | "
              f"max stage {max(r[1] for r in res):3d} | active stages mean {sum(r[2] for r in res)/len(res):5.2f} "
              f"max {max(r[2] for r in res):3d} | total updates mean {sum(r[3] for r in res)/len(res):6.2f} "
              f"max {max(r[3] for r in res):4d} | Psi=Opt {sum(r[4] for r in res)}/{len(res)}", flush=True)
