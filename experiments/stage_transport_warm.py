"""B1: the warm-start deficit under doubling.
I' random (balanced, feasible); I = 2 I' + bits (a = 2a' + alpha, b = 2b' + beta with
sum alpha = sum beta, c = 2c' + gamma, alpha, beta, gamma in {0,1}); P' = final
potentials of the PO-SL schedule on I'; deficit = F - nu0^I(P').  Reports the
largest deficit against m0 (edges), p, q, and checks that the schedule restarted
at P' with stages r >= F - X only reaches Opt(I).
Usage: python stage_transport_warm.py p q U trials"""
import random
import sys
from multiprocessing import Pool

from stage_transport_fast import Transport, random_instance, min_cost_flow


def work(args):
    seed, p, q, U, trials = args
    rng = random.Random(seed)
    out = []
    for _ in range(trials):
        a1, b1, c1, w = random_instance(rng, p, q, U, wbits=rng.choice([4, 10, 20]))
        T1 = Transport(a1, b1, c1, w)
        P1, _ = T1.schedule()
        for _ in range(5):
            alpha = [rng.randint(0, 1) for _ in range(p)]
            s = sum(alpha)
            beta = [0] * q
            idx = list(range(q)) * (s // q + 1)
            rng.shuffle(idx)
            for j in idx[:s]:
                beta[j] += 1
            gamma = {e: rng.randint(0, 1) for e in c1}
            a = [2 * x + y for x, y in zip(a1, alpha)]
            b = [2 * x + y for x, y in zip(b1, beta)]
            c = {e: 2 * c1[e] + gamma[e] for e in c1}
            opt = min_cost_flow(a, b, c, w)
            if opt is None:
                continue
            T = Transport(a, b, c, w)
            nu0, _ = T.state(P1)
            deficit = T.F - nu0
            P, lens = T.schedule(P1)
            out.append((deficit, len(c1), T.psi(P) == opt, min(lens) if lens else T.F, sum(lens.values())))
    return out


if __name__ == "__main__":
    p, q, U, trials = map(int, sys.argv[1:5])
    with Pool(28) as pool:
        res = sum(pool.map(work, [(s, p, q, U, trials) for s in range(28)]), [])
    d = [r[0] for r in res]
    print(f"p={p} q={q} U={U}: cases {len(res)}  deficit max {max(d)} mean {sum(d)/len(d):.2f}  "
          f"m0 max {max(r[1] for r in res)}  restart reaches Opt {sum(r[2] for r in res)}/{len(res)}  "
          f"updates after restart max {max(r[4] for r in res)}", flush=True)
    hist = {}
    for x in d:
        hist[x] = hist.get(x, 0) + 1
    print("deficit histogram", sorted(hist.items()))
