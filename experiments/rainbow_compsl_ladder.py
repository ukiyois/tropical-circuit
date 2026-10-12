"""Ladder instances: is the component-wise single-linkage update pseudo-polynomial?

Uniform matroid U_{k,m}, one connected component.  Values form a ladder with
spacing h between 0 and V, elements spread over the blocks; one block has a
single element far above.  If the number of applications grows like V/h with
m fixed, the update is not polynomial in the input size.  The local family is
run on the same inputs for comparison.
"""
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map
from rainbow_rpim import components
from rainbow_family_stress import theta_compsl

ZERO = Fraction(0)


def count_apps(M, blk, k, w, kind, cap=400):
    comp = components(M)
    p = {b: ZERO for b in range(k)}
    total = 0
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_compsl(M, v, comp) if kind == "comp-SL" else theta_map(M, v)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
            used += 1
        total += used
    ok = rp.psi(M, blk, w, p) == rp.opt(M, blk, k, w)
    return total, ok


def ladder(k, rungs, h, top):
    """k blocks; block k-1 holds one element at value `top`; the other blocks
    share a ladder of `rungs` elements at 0, h, 2h, ... (round robin)."""
    m = rungs + 1
    blk, w = {}, {}
    for i in range(rungs):
        blk[i] = i % (k - 1)
        w[i] = h * i
    blk[rungs] = k - 1
    w[rungs] = Fraction(top)
    M = rp.Matroid(m, lambda S, k=k: min(len(S), k))
    return M, blk, k, w


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rungs = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    for top in (4, 8, 16, 32):
        row = []
        for kind in ("comp-SL", "local"):
            M, blk, kk, w = ladder(k, rungs, Fraction(1), top)
            apps, ok = count_apps(M, blk, kk, w, kind)
            row.append(f"{kind}: {apps} apps ({'ok' if ok else 'WRONG'})")
        print(f"k={k} rungs={rungs} spacing 1, top={top}:  " + "  |  ".join(row), flush=True)


if __name__ == "__main__":
    main()
