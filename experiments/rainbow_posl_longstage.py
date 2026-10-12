"""Reproduce the referee's long-stage examples for the PO-SL update.

Example 1: multigraph on 4 vertices, edges 01,02,03,12,13,13, colors
[0,1,1,1,2,0], w = (3,1,0,3,3,2): stage r = 2 takes 4 applications, and a
schedule with only r+1 applications per stage outputs 6 against Opt = 7.
Example 2: edges 23,10,03,10,21,30,02,20,30, colors [1,0,1,2,0,1,1,1,1],
w = (5,9,6,12,10,9,3,2,4): stage r = 2 takes 7 applications (Opt = 26).
"""
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_rpim import components
from rainbow_posl import theta_posl

ZERO = Fraction(0)


def run(edges, colors, w, cap=None):
    n = 1 + max(max(e) for e in edges)
    M = rp.Matroid(len(edges), rp.graphic_rank_fn(n, edges))
    k = M.k
    blk = dict(enumerate(colors))
    w = {e: Fraction(x) for e, x in enumerate(w)}
    comp = components(M)
    p = {b: ZERO for b in range(k)}
    lengths = []
    for r in range(k):
        used = 0
        while cap is None or used < cap(r):
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_posl(M, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
            used += 1
        lengths.append(used)
    return lengths, rp.psi(M, blk, w, p), rp.opt(M, blk, k, w)


if __name__ == "__main__":
    ex = [([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)], [0, 1, 1, 1, 2, 0], [3, 1, 0, 3, 3, 2]),
          ([(2, 3), (1, 0), (0, 3), (1, 0), (2, 1), (3, 0), (0, 2), (2, 0), (3, 0)],
           [1, 0, 1, 2, 0, 1, 1, 1, 1], [5, 9, 6, 12, 10, 9, 3, 2, 4])]
    for edges, colors, w in ex:
        full = run(edges, colors, w)
        short = run(edges, colors, w, cap=lambda r: r + 1)
        print(f"stage lengths {full[0]}  Psi {full[1]}  Opt {full[2]}  |  r+1 schedule Psi {short[1]}")
