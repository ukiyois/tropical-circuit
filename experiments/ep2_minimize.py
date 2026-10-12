"""Phase 2e: greedy minimization of an instance violating Conjecture Q of B0d.

Moves (kept when an epoch with rho >= 2 still has Q slack >= 1): delete an edge (graphic;
block labels are renumbered so that the blocks stay 0..k-1), halve a weight, replace a
weight by a rounded value, relabel a weight to a smaller distinct value keeping the order.
Usage: python ep2_minimize.py "<descriptor>"
"""
import ast
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from ep2_common import epoch_states
from ep2_searchQ import epoch_stats


def qslack(d):
    try:
        M = build(d)
        _, _, blk, w = d
        k = M.k
        if sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
            return None
        best = None
        for rec in epoch_states(d, cap=400):
            if rec["rho"] >= 2:
                q, p, n, low = epoch_stats(rec)
                best = q if best is None else max(best, q)
        return best
    except (RuntimeError, AssertionError, ValueError):
        return None


def candidates(d):
    kind, (nv, edges), blk, w = d
    m = len(w)
    for i in range(m):                       # delete edge i
        e2 = edges[:i] + edges[i + 1:]
        b2 = blk[:i] + blk[i + 1:]
        w2 = w[:i] + w[i + 1:]
        labels = sorted(set(b2))
        b2 = [labels.index(b) for b in b2]
        yield (kind, (nv, e2), b2, w2)
    for i in range(m):                       # smaller weights
        for x in sorted({w[i] // 2, w[i] - 1, (w[i] >> 4) << 4, (w[i] >> 8) << 8}):
            if 0 <= x < w[i]:
                w2 = list(w)
                w2[i] = x
                yield (kind, (nv, edges), blk, w2)


def main():
    d = ast.literal_eval(sys.argv[1])
    assert qslack(d) is not None and qslack(d) >= 1
    changed = True
    while changed:
        changed = False
        for c in candidates(d):
            s = qslack(c)
            if s is not None and s >= 1:
                d = c
                changed = True
                print("  m =", len(d[3]), "sum w =", sum(d[3]), flush=True)
                break
    print("minimized:", d)
    print("Q slack:", qslack(d))


if __name__ == "__main__":
    main()
