"""B1: a family with restart deficit about m0 from capacity rounding alone.

R(k, q): sources 1..k (the set A) and 0, sinks 1..q and 0 (complete bipartite,
p = k + 1, Q = q + 1, m0 = p Q).  Flow x (all entries even) and capacities:
  x(i, j) = 2,  c(i, j) = 3 (odd),   w(i, j) = 0     (i in A, j >= 1)
  x(i, 0) = 2q, c(i, 0) = 2q,        w(i, 0) = H     (i in A)
  x(0, j) = 2k, c(0, j) = 2k,        w(0, j) = H     (j >= 1)
  x(0, 0) = 0,  c(0, 0) = INF,       w(0, 0) = 0.
x is even, so x' = x / 2 for both chains (alpha = beta = 0 at the first
halving) and c' = ceil(c / 2).  At P = 0 the coarse instance I_1 is optimal
(A fills sinks 1..q through the capacities c' = 2, source 0 fills sink 0), and
at I_0 the set A loses one unit on each of its k q cheap edges: deficit k q
= m0 - p - Q + 1.  The script computes the restart deficit exactly for the
real scaled schedule (floor and balanced chains) and for P = 0.
Usage: python b1_lower_linear.py"""
from b1_core import (Transport, chain_floor, chain_balanced, values, deficit_rado,
                     INF_CAP, run_scaled)


def family(k, q, H=10):
    x, cap, w = {}, {}, {}
    for i in range(1, k + 1):
        for j in range(1, q + 1):
            x[(i, j)], cap[(i, j)], w[(i, j)] = 2, 3, 0
        x[(i, 0)], cap[(i, 0)], w[(i, 0)] = 2 * q, 2 * q, H
    for j in range(1, q + 1):
        x[(0, j)], cap[(0, j)], w[(0, j)] = 2 * k, 2 * k, H
    x[(0, 0)], cap[(0, 0)], w[(0, 0)] = 0, INF_CAP, 0
    return k + 1, q + 1, x, cap, w


def restart_deficit(insts, w, P):
    I0 = insts[0]
    T = Transport(I0[0], I0[1], I0[2], w)
    return T.F - T.state(P)[0]


if __name__ == "__main__":
    for (k, q) in [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (2, 5), (4, 4), (3, 6), (5, 5)]:
        p, Q, x, cap, w = family(k, q)
        m0 = len(cap)
        line = f"k={k} q={q}: p={p} Q={Q} m0={m0} kq={k * q} m0-p-Q+1={m0 - p - Q + 1} |"
        for name, ch in (("floor", chain_floor), ("bal", chain_balanced)):
            insts = ch(x, cap, p, Q)
            T1 = Transport(*insts[1][:3], w)
            P1_zero_ok = T1.state([0] * p)[0] == T1.F
            d0 = restart_deficit(insts, w, [0] * p)
            # real schedule: all phases down to I_1
            res1 = run_scaled(insts[1][0], insts[1][1], insts[1][2], w, insts[1:], X=None, check=False)
            P1 = res1["P"]
            d_sched = restart_deficit(insts, w, P1)
            d_rado, A = deficit_rado(*insts[0][:3], values(w, P1))
            line += (f" {name}: nu0(I_1, P=0)=F: {P1_zero_ok}, deficit at P=0 {d0}, schedule P={P1} "
                     f"deficit {d_sched} (Rado {d_rado}, A*={sorted(A)}) |")
        print(line, flush=True)
