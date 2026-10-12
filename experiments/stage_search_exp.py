"""Hill climbing for long PO-SL stages with exponentially ranged integer weights.

Mutations include midpoints w_i <- (w_j + w_l) // 2 and doublings, which are the
moves that build the halving ladder.  Score: the longest stage of the schedule
from p = 0, or (with target 'excess') the longest stage minus m.
Usage: python stage_search_exp.py kind n m budget [workers] [target] [bits]
  kind 'graphic' (n vertices, k = n - 1) or 'binary' (rank n)
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow


def evaluate(desc, cap=600):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return None
    try:
        lens, v = sc.run_schedule(M, blk, k, list(w), cap=cap)
    except RuntimeError:
        return ("cap", desc)
    return lens


def rand_w(rng, bits):
    return rng.randrange(0, 1 << rng.randint(1, bits))


def random_desc(rng, kind, n, m, bits):
    if kind == "graphic":
        while True:
            edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
            if sc.graphic(n, edges).k == n - 1:
                break
        k = n - 1
        data = (n, edges)
    else:
        k = n
        while True:
            cols = [rng.randrange(1, 1 << k) for _ in range(m)]
            if sc.gf2(cols).k == k:
                break
        data = cols
    blk = [i if i < k else rng.randrange(k) for i in range(m)]
    rng.shuffle(blk)
    return (kind, data, blk, [rand_w(rng, bits) for _ in range(m)])


def mutate(desc, rng, bits):
    kind, data, blk, w = desc
    blk, w = list(blk), list(w)
    m = len(w)
    op = rng.random()
    i = rng.randrange(m)
    if op < 0.25:
        j, l = rng.randrange(m), rng.randrange(m)
        w[i] = (w[j] + w[l]) // 2
    elif op < 0.4:
        w[i] = min(1 << bits, max(0, w[i] * 2 if rng.random() < 0.5 else w[i] // 2))
    elif op < 0.55:
        w[i] = max(0, w[i] + rng.choice([-2, -1, 1, 2]))
    elif op < 0.65:
        w[i] = rand_w(rng, bits)
    elif op < 0.8:
        blk[i] = rng.randrange(max(blk) + 1)
    else:
        if kind == "graphic":
            n, edges = data
            edges = list(edges)
            edges[i] = tuple(rng.sample(range(n), 2))
            data = (n, edges)
        else:
            cols = list(data)
            k = max(c.bit_length() for c in cols)
            cols[i] = rng.randrange(1, 1 << k)
            data = cols
    return (kind, data, blk, w)


def score(lens, m, target):
    return max(lens) - (m if target == "excess" else 0)


def hill(args):
    seed, kind, n, m, budget, target, bits = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-999, None, None)
    while time.time() - t0 < budget:
        cur = random_desc(rng, kind, n, m, bits)
        r0 = evaluate(cur)
        if r0 is None or r0[0] == "cap":
            continue
        s = score(r0, m, target)
        stall = 0
        while stall < 600 and time.time() - t0 < budget:
            cand = mutate(cur, rng, bits)
            r1 = evaluate(cand)
            stall += 1
            if r1 is None or r1[0] == "cap":
                continue
            s1 = score(r1, m, target)
            if s1 >= s:
                if s1 > s:
                    stall = 0
                cur, s, r0 = cand, s1, r1
        if s > best[0]:
            best = (s, cur, r0)
    return best


def main():
    kind, n, m, budget = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 30
    target = sys.argv[6] if len(sys.argv) > 6 else "max"
    bits = int(sys.argv[7]) if len(sys.argv) > 7 else 20
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, kind, n, m, budget, target, bits) for s in range(500, 500 + workers)])
    res.sort(key=lambda x: -x[0])
    print(f"kind={kind} n={n} m={m} target={target} bits={bits} budget={budget}s workers={workers}")
    for s, desc, lens in res[:5]:
        print("score", s, "lens", lens, "desc", desc)
    sys.stdout.flush()


if __name__ == "__main__":
    main()
