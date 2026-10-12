"""A PO-SL stage with r+2 applications (r = 2, k = 3, m = 6, graphic).

Graph on vertices 0..3, edges  e0=01 e1=02 e2=03 e3=12 e4=13 e5=13' (parallel),
blocks (colors) [0,1,1,1,2,0], weights w = [3,1,0,3,3,2].
nu0(w) = 2, so stages 0 and 1 are identities and stage 2 starts at v = w.
Run with (A) the referee's implementation and (B) the authors' own code
(rainbow_prototype / rainbow_posl / rainbow_filtrations / rainbow_rpim),
imported read-only.  Run with  python -B  so no bytecode is written."""
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
from core import *

EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)]
BLK = [0, 1, 1, 1, 2, 0]
W = [Fraction(x) for x in [3, 1, 0, 3, 3, 2]]


def referee():
    M = graphic(4, EDGES)
    k = M.k
    p = {b: F0 for b in range(k)}
    per_stage = []
    for r in range(k):
        used = 0
        while True:
            v = [W[e] - p[BLK[e]] for e in range(M.m)]
            N0, _ = opt_bases(M, v)
            nu0 = nu_of(N0, BLK)
            if nu0 > r:
                break
            S, _ = avoidable(N0, BLK, k)
            tau, lam, a, _ = posl_update(M, BLK, k, v, r)
            print(f"  r={r} app {used + 1}: v={[str(x) for x in v]} nu0={nu0} S={sorted(S)} tau={tau} "
                  f"lam={ {b: str(x) for b, x in lam.items()} } a={ {b: str(x) for b, x in a.items()} }")
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
        per_stage.append(used)
    print("  referee: applications per stage", per_stage,
          " final Psi", psi(M, BLK, k, W, p), " Opt", opt_rainbow(M, BLK, k, W))


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
    per_stage = []
    for r in range(k):
        used = 0
        while True:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_posl(M, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            a, tau = res
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
        per_stage.append(used)
    print("  authors' code: applications per stage", per_stage,
          " final Psi", rp.psi(M, blk, w, p), " Opt", rp.opt(M, blk, k, w))


if __name__ == "__main__":
    print("(A) referee implementation")
    referee()
    print("(B) authors' implementation")
    authors()
