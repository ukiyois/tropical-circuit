"""B1: the scaled schedule with the proven restart bounds (exact).

For random capacitated transportation instances (p x q, supplies up to about
U per edge, capacities with slack 0, 1, random or INF, costs of 3 to 20 bits):
  floor chain,    X = m0 * max(q, 2)            (Corollary 3.5)
  balanced chain, X = m0 + floor((p + q) / 2)   (Corollary 3.7)
runs the static schedule of Theorem 5.1 (coarsest phase all stages, every
other phase only the stages r >= F_f - X), checks every restart deficit
against X and against the finer bound of the corollary, and checks
Psi(P) = Opt(I) at the end.  Also: the uncompressed cross-check of Lemma 3.1
(nu0 of the rainbow form of stage_transport.build against the compressed Rado
formula) on small instances.
Usage: python b1_scaled.py workers trials_per_worker"""
import random
import sys
from multiprocessing import Pool

import stage_core as sc
from stage_transport import build
from b1_core import (Transport, chain_floor, chain_balanced, values, deficit_rado,
                     unit, min_cost_flow, INF_CAP)


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


def floor_fine_bound(I, I2, deg):
    a, cap = I[0], I[2]
    a2 = I2[0]
    alpha = [a[i] - 2 * a2[i] for i in range(len(a))]
    gam = sum(1 for e, c in cap.items() if c < INF_CAP and c % 2 == 1)
    return gam + sum(al * max(1, d - 1) for al, d in zip(alpha, deg))


def bal_fine_bound(I, I2):
    kap, kap2 = unit(I[0], I[2]), unit(I2[0], I2[2])
    nz = sum(1 for e in kap if kap[e] != 2 * kap2[e])
    plus = sum(1 for i in range(len(I[0])) if I[0][i] - 2 * I2[0][i] == 1)
    minus = sum(1 for j in range(len(I[1])) if I[1][j] - 2 * I2[1][j] == -1)
    return nz + plus + minus


def run(args):
    seed, trials = args
    rng = random.Random(seed)
    st = {"inst": 0, "restarts": 0, "X_fail": 0, "fine_fail": 0, "wrong": 0,
          "max_ratio_floor": 0.0, "max_ratio_bal": 0.0, "max_upd_floor": 0, "max_upd_bal": 0,
          "max_d_floor": 0, "max_d_bal": 0, "unc_cases": 0, "unc_fail": 0}
    for _ in range(trials):
        p, q = rng.randint(1, 5), rng.randint(1, 5)
        U = rng.choice([2, 5, 16, 100, 1000])
        x0, cap, E = random_instance(rng, p, q, U)
        m0 = len(E)
        wb = rng.choice([3, 50, 1 << 20])
        w = {e: rng.randint(-wb, wb) for e in E}
        deg = [sum(1 for e in E if e[0] == i) for i in range(p)]
        st["inst"] += 1
        for kind, ch, X in (("floor", chain_floor, m0 * max(q, 2)),
                            ("bal", chain_balanced, m0 + (p + q) // 2)):
            insts = ch(x0, cap, p, q)
            P = [0] * p
            seq = list(reversed(insts))
            upd = 0
            for idx, I in enumerate(seq):
                if sum(I[0]) == 0:
                    continue
                T = Transport(I[0], I[1], I[2], w)
                rmin = 1
                if idx > 0 and sum(seq[idx - 1][0]) > 0:
                    d = T.F - T.state(P)[0]
                    st["restarts"] += 1
                    st["X_fail"] += d > X
                    fine = floor_fine_bound(I, seq[idx - 1], deg) if kind == "floor" \
                        else bal_fine_bound(I, seq[idx - 1])
                    st["fine_fail"] += d > fine
                    st["max_d_" + kind] = max(st["max_d_" + kind], d)
                    st["max_ratio_" + kind] = max(st["max_ratio_" + kind], d / X)
                    rmin = max(1, T.F - X)
                P, lens = T.schedule(P, rmin=rmin)
                upd += sum(lens.values())
            st["max_upd_" + kind] = max(st["max_upd_" + kind], upd)
            ok = Transport(*insts[0][:3], w).psi(P) == min_cost_flow(*insts[0][:3], w)
            st["wrong"] += not ok
        # uncompressed cross-check of Lemma 3.1 on small instances
        if rng.random() < 0.5:
            pp, qq = rng.randint(1, 3), rng.randint(1, 3)
            x0s, caps, Es = random_instance(rng, pp, qq, 2)
            a = [sum(x0s[e] for e in Es if e[0] == i) for i in range(pp)]
            b = [sum(x0s[e] for e in Es if e[1] == j) for j in range(qq)]
            if 0 < sum(a) <= 7:
                ws = {e: rng.randint(0, 4) for e in Es}
                P = [rng.randint(-3, 3) for _ in range(pp)]
                capf = {e: min(c, 50) for e, c in caps.items()}
                M, blk, k, ww, elems = build(a, b, capf, ws)
                vv = [ws[(i, j)] - P[i] for (i, j, s) in elems]
                nu_unc, _ = sc.state(M, blk, k, vv)
                d_rado, _ = deficit_rado(a, b, capf, values(ws, P))
                st["unc_cases"] += 1
                st["unc_fail"] += (k - nu_unc) != d_rado
    return st


def merge(ds):
    out = {}
    for d in ds:
        for k, v in d.items():
            out[k] = max(out.get(k, v), v) if k.startswith("max") else out.get(k, 0) + v
    return out


if __name__ == "__main__":
    workers, trials = int(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = merge(pool.map(run, [(500 + s, trials) for s in range(workers)]))
    print(res, flush=True)
