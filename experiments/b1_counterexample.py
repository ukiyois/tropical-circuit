"""B1: exact counterexample to Conjecture 4.3 (phase 2b note, Section 4.3).

Family T(s, D, B): sources 0 (old) and 1..s (new), sinks 0..D-1;
  x0(0, j) = 2B, cap(0, j) = 2B, cost w(0, j) = 1;
  x0(t, j) = 1,  cap(t, j) = D,  cost w(t, j) = 0      (t = 1..s);
so a = (2BD, D, ..., D), b_j = 2B + s, m0 = (s+1) D, p = s+1, q = D.
In every coarser instance of the chain only source 0 has supply, the schedule
never moves (P = 0), and at the restart of the finest phase the deficit is
s D (D - 1) = (m0 - q)(q - 1) whenever s D <= 2B + s.
The script computes everything exactly: the chain, the schedule of the coarser
phases, the restart deficit by max flow (Transport.state) and by the
compressed Rado formula (enumeration of source sets, eq. (rank-mu)), and the
static scaled schedule with X = p + q + 2 m0, which skips active stages.
It also checks the mechanism with the uncompressed rainbow form
(stage_transport.build + stage_core.state) on the small member T(1, 3, 1).
Usage: python b1_counterexample.py
"""
import sys

import stage_core as sc
from stage_transport import build
from b1_core import (Transport, chain_floor, deficit_rado, values, run_scaled,
                     min_cost_flow, comparison_bound)


def family(s, D, B):
    p, q = s + 1, D
    x0, cap, w = {}, {}, {}
    for j in range(D):
        x0[(0, j)], cap[(0, j)], w[(0, j)] = 2 * B, 2 * B, 1
        for t in range(1, s + 1):
            x0[(t, j)], cap[(t, j)], w[(t, j)] = 1, D, 0
    return p, q, x0, cap, w


def static_scaled(insts, w, X, K):
    """Faithful simulation of the static circuit: coarsest phase all stages,
    finer phases stages r in [F - X, F - 1]; every stage applies the stage-r
    update K times (identity when nu0 > r)."""
    P = [0] * len(insts[0][0])
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
                a_, tau = T.update(P, r)
                P = [P[i] + a_[i] for i in range(len(P))]
        first = False
    return P


def main():
    print("== uncompressed check of the mechanism, T(1, 3, 1)")
    p, q, x0, cap, w = family(1, 3, 1)
    insts = chain_floor(x0, cap, p, q)
    a, b, c, _ = insts[0]
    a1, b1, c1, _ = insts[1]
    print("I_0: a", a, "b", b, "| I_1: a", a1, "b", b1)
    T = Transport(a, b, c, w)
    nu0, av = T.state([0, 0])
    M, blk, k, ww, elems = build(a, b, c, w)
    nu0u, avu = sc.state(M, blk, k, ww)
    print(f"  m = {M.m} elements, k = {k}; compressed nu0 = {nu0}, uncompressed nu0 = {nu0u}; "
          f"deficit {k - nu0u}; Av (uncompressed slots) = {sorted(avu)}")
    print()
    print("== the family T(s, D, B): restart deficit against X = p + q + 2 m0")
    rows = []
    for (s, D, B) in [(1, 3, 1), (1, 5, 2), (1, 6, 3), (1, 7, 3), (1, 8, 4), (2, 5, 4),
                      (2, 6, 5), (3, 5, 6), (5, 4, 8), (2, 8, 7), (4, 6, 10)]:
        p, q, x0, cap, w = family(s, D, B)
        m0 = len(cap)
        X = p + q + 2 * m0
        insts = chain_floor(x0, cap, p, q)
        res = run_scaled(insts[0][0], insts[0][1], insts[0][2], w, insts, X=None)
        a, b, c, _ = insts[0]
        # potentials at the end of the schedule for I_1
        res1 = run_scaled(insts[1][0], insts[1][1], insts[1][2], w, insts[1:], X=None, check=False)
        P1 = res1["P"]
        T = Transport(a, b, c, w)
        nu0, _ = T.state(P1)
        d_flow = T.F - nu0
        d_rado, argA = deficit_rado(a, b, c, values(w, P1))
        bound = comparison_bound(insts[0], insts[1], values(w, P1), argA)
        # the schedule from I_1 is correct at I_1:
        T1 = Transport(*insts[1][:3], w)
        ok1 = T1.psi(P1) == min_cost_flow(*insts[1][:3], w) and T1.state(P1)[0] == T1.F
        K = p * (m0 * m0 // 4 + 1)
        Pst = static_scaled(insts, w, X, K)
        psi_st = T.psi(Pst)
        opt = min_cost_flow(a, b, c, w)
        nu_end = T.state(Pst)[0]
        rows.append((s, D, B, p, q, m0, T.F, X, d_flow, d_rado, s * D * (D - 1), bound,
                     ok1, P1, psi_st, opt, nu_end, res["correct"]))
        print(f"s={s} D={D} B={B}: p={p} q={q} m0={m0} F={T.F} X={X} | P(I_1 end)={P1} "
              f"(nu0=F and Psi=Opt at I_1: {ok1}) | deficit: max flow {d_flow}, Rado {d_rado} "
              f"(A* = {sorted(argA)}), formula sD(D-1) = {s * D * (D - 1)}, Thm 3.4 bound {bound} "
              f"| {'COUNTEREXAMPLE' if d_flow > X else 'within X'} | static scaled schedule with X: "
              f"Psi = {psi_st}, Opt = {opt}, nu0 = {nu_end}/{T.F} | full restart correct: {res['correct']}",
              flush=True)
    bad = [r for r in rows if r[8] != r[9] or r[8] != r[10] or r[8] > r[11]]
    print("rows with a mismatch between max flow, Rado, s D (D - 1), or above the bound:", len(bad))


if __name__ == "__main__":
    main()
