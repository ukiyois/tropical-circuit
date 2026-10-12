"""Structured hill climbing for long epochs: graphic matroids made of a spanning
tree, parallel copies of tree edges (bridges) and a few chords (the shape of the
halving ladder), optionally with a pendant edge (a coloop) in an unraised block
so that the unraised elements move rigidly.

Objective: max over epochs of (n - bound), bound from ep_common.BOUNDS.
Usage: python ep_struct.py nv m budget workers bound [bits] [seed0] [chords]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow
from ep_common import epochs, BOUNDS
from ep_search import score as _unused  # noqa: F401  (keeps module import order uniform)

BOUND = "m"


def score(desc):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return None
    try:
        eps, _ = epochs(M, blk, k, list(w), cap=800)
    except RuntimeError:
        return None
    f = BOUNDS[BOUND]
    best = None
    for e in eps:
        key = (e["n"] - f(e), e["n"])
        if best is None or key > best[0]:
            best = (key, (e["n"], e["r"], e["rho"], e["U"], e["R"]))
    return best


def rand_w(rng, bits):
    return rng.randrange(0, 1 << rng.randint(1, bits))


def random_struct(rng, nv, m, bits, chords):
    # random spanning tree on nv vertices
    tree = []
    for v in range(1, nv):
        tree.append((v, rng.randrange(v)))
    edges = list(tree)
    for _ in range(chords):
        a, b = rng.sample(range(nv), 2)
        edges.append((a, b))
    while len(edges) < m:
        edges.append(rng.choice(tree))   # bridge: parallel copy of a tree edge
    k = nv - 1
    blk = [i if i < k else rng.randrange(k) for i in range(m)]
    rng.shuffle(blk)
    rng.shuffle(edges)
    return ("graphic", (nv, edges), blk, [rand_w(rng, bits) for _ in range(m)])


def mutate(desc, rng, bits):
    kind, data, blk, w = desc
    nv, edges = data
    blk, w, edges = list(blk), list(w), list(edges)
    m = len(w)
    op = rng.random()
    i = rng.randrange(m)
    if op < 0.25:
        j, l = rng.randrange(m), rng.randrange(m)
        w[i] = (w[j] + w[l]) // 2
    elif op < 0.38:
        w[i] = min(1 << bits, max(0, w[i] * 2 if rng.random() < 0.5 else w[i] // 2))
    elif op < 0.5:
        w[i] = max(0, w[i] + rng.choice([-2, -1, 1, 2]))
    elif op < 0.58:
        j = rng.randrange(m)
        w[i] = max(0, w[j] + rng.choice([-1, 1]) * (1 << rng.randrange(bits)))
    elif op < 0.63:
        w[i] = rand_w(rng, bits)
    elif op < 0.8:
        blk[i] = rng.randrange(max(blk) + 1)
    elif op < 0.9:
        j = rng.randrange(m)
        edges[i] = edges[j]
    else:
        edges[i] = tuple(rng.sample(range(nv), 2))
    return (kind, (nv, edges), blk, w)


def _init(b):
    global BOUND
    BOUND = b


def hill(args):
    seed, nv, m, budget, bits, chords = args
    rng = random.Random(seed)
    t0 = time.time()
    best = ((-999, 0), None, None)
    while time.time() - t0 < budget:
        cur = random_struct(rng, nv, m, bits, chords)
        s = score(cur)
        if s is None:
            continue
        stall = 0
        while stall < 1000 and time.time() - t0 < budget:
            cand = mutate(cur, rng, bits)
            s2 = score(cand)
            stall += 1
            if s2 is None:
                continue
            if s2[0] >= s[0]:
                if s2[0] > s[0]:
                    stall = 0
                cur, s = cand, s2
        if s[0] > best[0]:
            best = (s[0], s[1], cur)
    return best


if __name__ == "__main__":
    nv, m, budget, workers, bound = (int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]),
                                     int(sys.argv[4]), sys.argv[5])
    bits = int(sys.argv[6]) if len(sys.argv) > 6 else 24
    seed0 = int(sys.argv[7]) if len(sys.argv) > 7 else 5000
    chords = int(sys.argv[8]) if len(sys.argv) > 8 else 2
    with Pool(workers, initializer=_init, initargs=(bound,)) as pool:
        res = pool.map(hill, [(s, nv, m, budget, bits, chords) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"struct nv={nv} m={m} budget={budget} bound={bound} bits={bits} chords={chords}")
    for key, info, desc in res[:6]:
        print("score", key, "(n,r,rho,|U|,|R|)", info, "desc", desc)
    sys.stdout.flush()
