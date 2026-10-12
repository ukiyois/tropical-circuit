"""Random instances and hill climbing for long PO-SL stages (stage_core, exact ints).

Instance descriptor: (kind, data, blk, w) with
  kind 'graphic': data = (n, edges);  'binary': data = cols (ints);  'uniform': data = (k, m)
Score: the list of stage lengths of the schedule from p = 0 (stages r = 1..k-1).
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc


def build(desc):
    kind, data, blk, w = desc
    if kind == "graphic":
        n, edges = data
        return sc.graphic(n, edges)
    if kind == "binary":
        return sc.gf2(data)
    if kind == "uniform":
        k, m = data
        return sc.uniform(k, m)
    raise ValueError(kind)


def has_rainbow(M, blk, k):
    nu, av, _ = sc.rainbow_av(M, blk, k)
    return nu == k


def evaluate(desc, cap=400):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)):
        return None
    if not has_rainbow(M, blk, k):
        return None
    try:
        lens, v = sc.run_schedule(M, blk, k, list(w), cap=cap)
    except RuntimeError:
        return ("cap", desc)
    nu, _ = sc.state(M, blk, k, v)
    assert nu == k
    return lens


def random_desc(rng, kind, n=None, m=None, k=None, wmax=12):
    if kind == "graphic":
        while True:
            edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
            M = sc.graphic(n, edges)
            if M.k == n - 1:
                break
        k = n - 1
        blk = [i if i < k else rng.randrange(k) for i in range(m)]
        rng.shuffle(blk)
        return ("graphic", (n, edges), blk, [rng.randrange(0, wmax + 1) for _ in range(m)])
    if kind == "binary":
        while True:
            cols = [rng.randrange(1, 1 << k) for _ in range(m)]
            if sc.gf2(cols).k == k:
                break
        blk = [i if i < k else rng.randrange(k) for i in range(m)]
        rng.shuffle(blk)
        return ("binary", cols, blk, [rng.randrange(0, wmax + 1) for _ in range(m)])
    if kind == "uniform":
        blk = [i if i < k else rng.randrange(k) for i in range(m)]
        rng.shuffle(blk)
        return ("uniform", (k, m), blk, [rng.randrange(0, wmax + 1) for _ in range(m)])
    raise ValueError(kind)


def mutate(desc, rng, wmax=12):
    kind, data, blk, w = desc
    blk, w = list(blk), list(w)
    m = len(w)
    op = rng.random()
    if op < 0.55:
        i = rng.randrange(m)
        w[i] = max(0, min(wmax, w[i] + rng.choice([-3, -2, -1, 1, 2, 3])))
    elif op < 0.75:
        i = rng.randrange(m)
        blk[i] = rng.randrange(max(blk) + 1)
    else:
        i = rng.randrange(m)
        if kind == "graphic":
            n, edges = data
            edges = list(edges)
            edges[i] = tuple(rng.sample(range(n), 2))
            data = (n, edges)
        elif kind == "binary":
            cols = list(data)
            k = max(c.bit_length() for c in cols)
            cols[i] = rng.randrange(1, 1 << k)
            data = cols
        else:
            j = rng.randrange(m)
            w[i], w[j] = w[j], w[i]
    return (kind, data, blk, w)


def stage_score(lens, which):
    if which == "max":
        return max(lens)
    return lens[which - 1] if which - 1 < len(lens) else 0


def hill(args):
    seed, kind, n, m, k, budget, which, wmax = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-1, None, None)
    caps = []
    while time.time() - t0 < budget:
        cur = random_desc(rng, kind, n, m, k, wmax)
        sc0 = evaluate(cur)
        if sc0 is None:
            continue
        if sc0[0] == "cap":
            caps.append(cur)
            continue
        s = stage_score(sc0, which)
        stall = 0
        while stall < 400 and time.time() - t0 < budget:
            cand = mutate(cur, rng, wmax)
            r = evaluate(cand)
            if r is None:
                stall += 1
                continue
            if r[0] == "cap":
                caps.append(cand)
                continue
            s2 = stage_score(r, which)
            if s2 >= s:
                if s2 > s:
                    stall = 0
                cur, s, sc0 = cand, s2, r
            stall += 1
        if s > best[0]:
            best = (s, cur, sc0)
    return best, caps[:2]


def main():
    kind = sys.argv[1]
    n = int(sys.argv[2])            # vertices (graphic) or rank (binary/uniform)
    m = int(sys.argv[3])
    budget = float(sys.argv[4])
    which = sys.argv[5] if len(sys.argv) > 5 else "max"
    which = which if which == "max" else int(which)
    workers = int(sys.argv[6]) if len(sys.argv) > 6 else 30
    wmax = int(sys.argv[7]) if len(sys.argv) > 7 else 12
    k = n - 1 if kind == "graphic" else n
    args = [(s, kind, n, m, k, budget, which, wmax) for s in range(1000, 1000 + workers)]
    with Pool(workers) as pool:
        res = pool.map(hill, args)
    res.sort(key=lambda x: -x[0][0])
    print(f"kind={kind} n={n} m={m} k={k} target={which} budget={budget}s workers={workers}")
    print("cap hits:", sum(len(c) for _, c in res))
    for (s, desc, lens), caps in res[:5]:
        print("score", s, "lens", lens, "desc", desc)
    sys.stdout.flush()


if __name__ == "__main__":
    main()
