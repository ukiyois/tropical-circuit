"""Stage r = 2 of length 7 (= r + 5) on a 9-edge multigraph on 4 vertices (k = 3),
found by hill_long.py.  Checked with the referee code and with the authors'
code (read-only import; run with python -B).  Also prints the per-application
trace (tau, raised blocks, S) and the result of an (r+1)-per-stage schedule."""
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
from core import *

EDGES = [(2, 3), (1, 0), (0, 3), (1, 0), (2, 1), (3, 0), (0, 2), (2, 0), (3, 0)]
BLK = [1, 0, 1, 2, 0, 1, 1, 1, 1]
W = [Fraction(x) for x in [5, 9, 6, 12, 10, 9, 3, 2, 4]]


def run(M, k, per_stage=None, verbose=False):
    p = {b: F0 for b in range(k)}
    lens = []
    for r in range(k):
        used = 0
        cap = per_stage(r) if per_stage else 10 ** 9
        while used < cap:
            v = [W[e] - p[BLK[e]] for e in range(M.m)]
            N0, _ = opt_bases(M, v)
            if nu_of(N0, BLK) > r:
                break
            S, _ = avoidable(N0, BLK, k)
            tau, lam, a, _ = posl_update(M, BLK, k, v, r)
            if verbose:
                print(f"  r={r} app {used + 1}: tau={tau} S={sorted(S)} a={ {b: str(x) for b, x in a.items()} }")
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
        lens.append(used)
    return lens, psi(M, BLK, k, W, p)


def authors():
    sys.path.insert(0, r"D:\Dsektop\daishu\experiments")
    import rainbow_prototype as rp
    from rainbow_filtrations import update
    from rainbow_rpim import components
    from rainbow_posl import theta_posl
    M = rp.Matroid(len(EDGES), rp.graphic_rank_fn(4, EDGES))
    k = M.k
    blk = {e: BLK[e] for e in range(M.m)}
    w = {e: W[e] for e in range(M.m)}
    comp = components(M)
    p = {b: Fraction(0) for b in range(k)}
    lens = []
    for r in range(k):
        used = 0
        while True:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_posl(M, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
            used += 1
        lens.append(used)
    return lens, rp.psi(M, blk, w, p), rp.opt(M, blk, k, w)


if __name__ == "__main__":
    M = graphic(4, EDGES)
    k = M.k
    lens, val = run(M, k, verbose=True)
    print("referee: stage lengths", lens, "output", val, "Opt", opt_rainbow(M, BLK, k, W))
    print("authors' code: stage lengths, output, Opt =", authors())
    lens, val = run(M, k, per_stage=lambda r: r + 1)
    print("static schedule with r+1 applications per stage: output", val)
    lens, val = run(M, k, per_stage=lambda r: (r + 1) * (M.m * M.m // 4 + 1))
    print("static schedule with the Theorem 8 count: output", val)
