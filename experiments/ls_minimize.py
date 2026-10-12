"""Minimize a counterexample to "the last-stage block never decreases nu0".

Greedy: delete edges, merge/shift weights down, while keeping a rainbow base and the
END drop of the last-stage block at p = 0 (w = v).  Graphic matroids.
Usage: python ls_minimize.py   (uses the instance found by ls_embed.py)"""
import random
import sys

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base


def end_drop(n, edges, blk, w):
    M = sc.graphic(n, edges)
    k = M.k
    if k < 3 or len(set(blk)) < k or max(blk) >= k or not has_rainbow_base(M, blk, k):
        return False
    nu0, _ = lc.nu_state(M, blk, k, w)
    if nu0 >= k - 1:
        return False
    a, pcs, tau = lc.block(M, blk, k, w, k - 1)
    nu2, _ = lc.nu_state(M, blk, k, lc.shift(w, blk, a))
    return nu2 < nu0


def relabel(blk):
    lab = {}
    return [lab.setdefault(b, len(lab)) for b in blk]


def minimize(n, edges, blk, w, rng, rounds=400):
    assert end_drop(n, edges, blk, w)
    changed = True
    while changed:
        changed = False
        for i in range(len(edges)):
            e2 = edges[:i] + edges[i + 1:]
            b2 = blk[:i] + blk[i + 1:]
            w2 = w[:i] + w[i + 1:]
            M = sc.graphic(n, e2)
            # blocks must be 0..k-1
            if len(set(b2)) != M.k:
                continue
            b2 = relabel(b2)
            if end_drop(n, e2, b2, w2):
                edges, blk, w = e2, b2, w2
                changed = True
                break
    # weights: try to lower each weight / compress values
    for _ in range(rounds):
        i = rng.randrange(len(w))
        cand = list(w)
        cand[i] = rng.randint(0, max(0, w[i] - 1)) if w[i] > 0 else 0
        if cand != w and end_drop(n, edges, blk, cand):
            w = cand
    m0 = min(w)
    w = [x - m0 for x in w]
    return edges, blk, w


if __name__ == "__main__":
    rng = random.Random(1)
    n = 6
    edges = [(2, 3), (5, 1), (1, 0), (1, 0), (4, 2), (5, 1), (0, 3), (5, 3), (0, 4), (3, 0), (0, 5), (1, 0), (2, 4)]
    blk = [4, 1, 2, 1, 4, 3, 4, 4, 0, 0, 2, 0, 1]
    w = [2, 4, 5, 5, 2, 5, 4, 3, 5, 7, 4, 2, 8]
    best = None
    for trial in range(30):
        e2, b2, w2 = minimize(n, list(edges), list(blk), list(w), rng)
        key = (len(e2), sum(w2), max(w2))
        if best is None or key < best[0]:
            best = (key, e2, b2, w2)
            print(key, e2, b2, w2, flush=True)
    print("best", best, flush=True)
