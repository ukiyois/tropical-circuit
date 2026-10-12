"""B1 (exploratory): updates of a stage r applied at nu0 < r.

The circuit block of stage r computes the threshold integral
    eta_i = sum over levels l_k < tau_r of (l_{k+1} - l_k) [i in Av(N(l_k))],
tau_r the first level with nu(N(t)) >= r + 1, at any state.  This script
measures, on random transportation instances (type-compressed, exact):
  (a) 'last': from P = 0 on the full instance, apply only the block of stage
      r = F - 1 until nu0 = F: number of updates, and whether Psi stays <= Opt
      and nu0 never decreases;
  (b) 'scaled_last': the balanced chain, each phase applies only the block of
      stage F_f - 1 until nu0 = F_f: total updates.
Compared with the regular schedule (all stages).
Usage: python b1_laststage.py workers trials"""
import random
import sys
from multiprocessing import Pool

from b1_core import Transport, chain_balanced, min_cost_flow, INF_CAP
from b1_static_fail import circuit_update


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


def last_stage_run(T, P, cap_updates=400):
    """Apply the block of stage F - 1 until nu0 = F; returns (P, updates, ok_monotone)."""
    r = T.F - 1
    upd, mono = 0, True
    nu_prev = T.state(P)[0]
    while True:
        nu0 = T.state(P)[0]
        if nu0 < nu_prev:
            mono = False
        nu_prev = nu0
        if nu0 >= T.F:
            return P, upd, mono
        eta = circuit_update(T, P, r)
        if not any(eta):
            return P, -1, mono
        P = [P[i] + eta[i] for i in range(T.p)]
        upd += 1
        if upd > cap_updates:
            return P, -2, mono


def run(args):
    seed, trials = args
    rng = random.Random(seed)
    st = {"inst": 0, "last_ok": 0, "last_stuck": 0, "last_nonmono": 0, "last_max_upd": 0,
          "reg_max_upd": 0, "scaled_last_ok": 0, "scaled_last_max_upd": 0, "psi_over": 0,
          "last_sum_upd": 0, "reg_sum_upd": 0}
    for _ in range(trials):
        p, q = rng.randint(1, 4), rng.randint(1, 4)
        U = rng.choice([3, 10, 40])
        x0, cap, E = random_instance(rng, p, q, U)
        wb = rng.choice([5, 100, 1 << 16])
        w = {e: rng.randint(-wb, wb) for e in E}
        a = [sum(x0[e] for e in E if e[0] == i) for i in range(p)]
        b = [sum(x0[e] for e in E if e[1] == j) for j in range(q)]
        T = Transport(a, b, cap, w)
        if T.F < 2:
            continue
        opt = min_cost_flow(a, b, cap, w)
        st["inst"] += 1
        # regular schedule
        Pr, lens = T.schedule([0] * p)
        st["reg_max_upd"] = max(st["reg_max_upd"], sum(lens.values()))
        st["reg_sum_upd"] += sum(lens.values())
        # (a) last stage only, unscaled
        P, upd, mono = last_stage_run(T, [0] * p)
        if upd >= 0:
            st["last_ok"] += T.psi(P) == opt
            st["last_max_upd"] = max(st["last_max_upd"], upd)
            st["last_sum_upd"] += upd
        else:
            st["last_stuck"] += 1
        st["last_nonmono"] += not mono
        st["psi_over"] += T.psi(P) > opt
        # (b) scaled, last stage per phase
        insts = chain_balanced(x0, cap, p, q)
        P = [0] * p
        tot, ok = 0, True
        for I in reversed(insts):
            if sum(I[0]) == 0:
                continue
            TI = Transport(I[0], I[1], I[2], w)
            if TI.F < 2:
                P, lens = TI.schedule(P)
                continue
            P, upd, mono = last_stage_run(TI, P)
            if upd < 0:
                ok = False
                break
            tot += upd
        if ok:
            st["scaled_last_ok"] += T.psi(P) == opt
            st["scaled_last_max_upd"] = max(st["scaled_last_max_upd"], tot)
    return st


if __name__ == "__main__":
    workers, trials = int(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(run, [(1100 + s, trials) for s in range(workers)])
    out = {}
    for d in res:
        for k, v in d.items():
            out[k] = max(out.get(k, v), v) if k.endswith("max_upd") else out.get(k, 0) + v
    print(out, flush=True)
