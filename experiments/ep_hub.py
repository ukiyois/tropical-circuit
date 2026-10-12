"""Hub designs for long epochs (graphic, exact integers), with weight-only hill climbing.

Design H(c, L): vertices 0 (hub), 1 (g side), 2..c+1 (raised anchors), c+2 (coloop).
  g'   = (c+2, 0)  coloop, unraised block 0
  g    = (1, 0)    unraised anchor, block 0
  b_i  = (1, 0)    L bridges parallel to g, block 0
  h_j  = (j+1, 0)  raised anchors, block j            (j = 1..c)
  y    = (1, 2)    raised, closes the triangle {g, h_1, y}, block c+1
  ch_j = (j+1, j+2) chords between consecutive h's, raised, block c+1 (j < c)
  hp_c = (c+1, 0)  parallel to h_c, block c+1 (makes the blocks of S0 avoidable)
so k = c + 2, the only unraised block is 0 (with a coloop: rigid epochs), rho = c.
Weights are optimized by hill climbing; objective = longest epoch minus m.
Usage: python ep_hub.py c L budget workers [bits] [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import has_rainbow
from ep_common import epochs


def design(c, L):
    edges, blk, names = [], [], []
    def add(e, b, nm):
        edges.append(e); blk.append(b); names.append(nm)
    add((c + 2, 0), 0, "g'")
    add((1, 0), 0, "g")
    for i in range(L):
        add((1, 0), 0, f"b{i+1}")
    for j in range(1, c + 1):
        add((j + 1, 0), j, f"h{j}")
    add((1, 2), c + 1, "y")
    for j in range(1, c):
        add((j + 1, j + 2), c + 1, f"ch{j}")
    add((c + 1, 0), c + 1, f"hp{c}")
    return c + 3, edges, blk, names


def score(M, blk, w):
    k = M.k
    try:
        eps, _ = epochs(M, blk, k, list(w), cap=800)
    except RuntimeError:
        return None
    if not eps:
        return None
    best = max(eps, key=lambda e: e["n"])
    return (best["n"] - M.m, best["n"])


def hill(args):
    seed, c, L, budget, bits = args
    rng = random.Random(seed)
    nv, edges, blk, names = design(c, L)
    M = sc.graphic(nv, edges)
    assert has_rainbow(M, blk, M.k)
    m = M.m
    t0 = time.time()
    best = ((-999, 0), None)
    while time.time() - t0 < budget:
        w = [rng.randrange(0, 1 << rng.randint(1, bits)) for _ in range(m)]
        s = score(M, blk, w)
        if s is None:
            continue
        stall = 0
        while stall < 1500 and time.time() - t0 < budget:
            w2 = list(w)
            i = rng.randrange(m)
            op = rng.random()
            if op < 0.3:
                j, l = rng.randrange(m), rng.randrange(m)
                w2[i] = (w2[j] + w2[l]) // 2
            elif op < 0.45:
                w2[i] = max(0, w2[i] * 2 if rng.random() < 0.5 else w2[i] // 2)
            elif op < 0.6:
                w2[i] = max(0, w2[i] + rng.choice([-2, -1, 1, 2]))
            elif op < 0.8:
                j = rng.randrange(m)
                w2[i] = max(0, w2[j] + rng.choice([-1, 1]) * (1 << rng.randrange(bits)))
            else:
                w2[i] = rng.randrange(0, 1 << rng.randint(1, bits))
            s2 = score(M, blk, w2)
            stall += 1
            if s2 is None:
                continue
            if s2 >= s:
                if s2 > s:
                    stall = 0
                w, s = w2, s2
        if s > best[0]:
            best = (s, w)
    return best, (nv, edges, blk, names)


if __name__ == "__main__":
    c, L, budget, workers = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    bits = int(sys.argv[5]) if len(sys.argv) > 5 else 30
    seed0 = int(sys.argv[6]) if len(sys.argv) > 6 else 9000
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, c, L, budget, bits) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0][0], reverse=True)
    nv, edges, blk, names = res[0][1]
    print(f"hub c={c} L={L} m={len(edges)} k={nv-1} budget={budget}")
    print("names", names)
    for (s, w), _ in res[:4]:
        print("score", s, "desc", ("graphic", (nv, edges), blk, w))
    sys.stdout.flush()
