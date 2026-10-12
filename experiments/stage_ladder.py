"""The halving ladder: PO-SL stages of length L + 2 at k = 3 on m = L + 5 elements.

Graph on vertices {0,1,2,3}, rank k = 3, blocks 0,1,2:
  gp = (3,0) block 1, value 0        (a coloop: block 1 is never avoidable)
  g  = (2,0) block 1, value 0
  h  = (1,0) block 0, value A        raised
  hp = (1,0) block 2, value A        raised
  y  = (2,1) block 0, value A + 1    raised
  b_i = (2,0) block 1, value A / 2^i, i = 1..L   (bridges, parallel to g)
with A = 2^L.  The unique rainbow tree is {gp, y, hp}.  Stage 2 needs the raised
blocks {0, 2} to move down by A + 1 in total; single linkage reaches h from g
through one bridge only at scale >= (current A)/2, so each update halves A.
Exact integer arithmetic.  Usage: python stage_ladder.py Lmax
"""
import sys

import stage_core as sc


def ladder(L, c=1):
    A = 2 ** L
    edges = [(3, 0), (2, 0), (1, 0), (1, 0), (2, 1)] + [(2, 0)] * L
    blk = [1, 1, 0, 2, 0] + [1] * L
    w = [0, 0, A, A, A + c] + [A // 2 ** i for i in range(1, L + 1)]
    return edges, blk, w


def run(L, family=sc.posl, exact=False):
    edges, blk, w = ladder(L)
    M = sc.graphic(4, edges)
    k = M.k
    lens, v = sc.run_schedule(M, blk, k, w, family)
    psi = sc.psi_from_v(M, blk, k, w, v)
    out = {"L": L, "m": M.m, "lens": lens, "Psi": psi}
    if exact:
        vv = list(w)
        ex = []
        for r in range(1, k):
            nu, _ = sc.state(M, blk, k, vv)
            if nu > r:
                ex.append(0)
                continue
            c, vv = sc.run_stage_exact(M, blk, k, vv, r)
            ex.append(c)
        out["exact_lens"] = ex
        out["Opt"] = sc.opt_rainbow(M, blk, k, w)
    return out


if __name__ == "__main__":
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    for L in range(0, Lmax + 1):
        print(run(L, exact=(L <= 8)), flush=True)
