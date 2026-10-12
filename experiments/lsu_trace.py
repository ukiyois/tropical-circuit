"""Trace an LS run step by step.

For each LS step at state v: nu0, S0, the pieces (c_i, c_{i+1}, nu_i, A_i) of the block,
the jumps t_i of nu(N(.)) with nu(L(t_i)) (mismatch when < mu_i), and the outcome
nu0', S0'.  Usage (module): trace(M, blk, k, w) -> list of step dicts; print_trace."""
from fractions import Fraction

import stage_core as sc
import ls_core as lc


def state_at(v, blk, pcs, s):
    """v(s) along the block path."""
    a = {}
    for c0, c1, nu, A in pcs:
        if s <= c0:
            break
        ln = min(s, c1) - c0
        for b in A:
            a[b] = a.get(b, 0) + ln
    return [v[e] - a.get(blk[e], 0) for e in range(len(v))]


def step_info(M, blk, k, v):
    nu0, S0 = lc.nu_state(M, blk, k, v)
    a, pcs, tau = lc.block(M, blk, k, v, k - 1)
    # jumps of nu along pieces
    jumps = []
    prev = None
    for c0, c1, nu, A in pcs:
        if prev is not None and nu != prev:
            vs = state_at(v, blk, pcs, c0)
            nuL, AvL = lc.nu_state(M, blk, k, vs)
            jumps.append((c0, prev, nu, nuL))
        prev = nu
    v2 = lc.shift(v, blk, a)
    nu1, S1 = lc.nu_state(M, blk, k, v2)
    return {"v": list(v), "nu0": nu0, "S0": S0, "a": a, "tau": tau, "pcs": pcs,
            "jumps": jumps, "mismatch": any(nl < nu for (_, _, nu, nl) in jumps),
            "nu1": nu1, "S1": S1, "v2": v2}


def trace(M, blk, k, w, cap=500):
    v = list(w)
    out = []
    nu, _ = lc.nu_state(M, blk, k, v)
    while nu < k:
        st = step_info(M, blk, k, v)
        out.append(st)
        v = st["v2"]
        nu = st["nu1"]
        if len(out) > cap:
            raise RuntimeError("cap")
    return out


def fmt_pcs(pcs):
    return " ".join(f"[{c0},{c1}):nu{nu}:{sorted(A)}" for c0, c1, nu, A in pcs)


def print_trace(tr):
    for j, st in enumerate(tr):
        print(f"step {j}: nu0={st['nu0']} S0={sorted(st['S0'])} tau={st['tau']} a={st['a']} "
              f"-> nu0'={st['nu1']} S0'={sorted(st['S1'])} mismatch={st['mismatch']}")
        print("    pieces:", fmt_pcs(st["pcs"]))
        if st["jumps"]:
            print("    jumps (t, mu_prev, mu, nu(L(t))):", st["jumps"])
