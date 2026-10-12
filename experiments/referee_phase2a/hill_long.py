"""Hill-climbing for long PO-SL stages (graphic multigraphs and binary matroids).
Objective: max over the schedule's stages of (applications - (r+1)), starting at
p = 0 (so stage nu0(w) starts at v = w).  Also verifies the final value is Opt and
the Theorem 8 bound.  Prints the best instance per worker."""
import random
import sys
import time
from multiprocessing import Pool
from core import *


def stage_lengths(M, blk, k, w, cap=200):
    p = {b: F0 for b in range(k)}
    excess = -99
    lens = []
    for r in range(k):
        used = 0
        while True:
            v = [w[e] - p[blk[e]] for e in range(M.m)]
            N0, _ = opt_bases(M, v)
            if nu_of(N0, blk) > r:
                break
            tau, lam, a, _ = posl_update(M, blk, k, v, r)
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            if used > cap:
                return None, None, None
        lens.append(used)
        if used:
            excess = max(excess, used - (r + 1))
    ok = psi(M, blk, k, w, p) == opt_rainbow(M, blk, k, w)
    return excess, lens, ok


def build(desc):
    kind, data, blk, w = desc
    if kind == "graphic":
        n, edges = data
        M = graphic(n, edges)
    else:
        M = gf2(data)
    return M


def mutate(desc, rng):
    kind, data, blk, w = desc
    blk = list(blk)
    w = list(w)
    if kind == "graphic":
        n, edges = data
        edges = list(edges)
    else:
        cols = list(data)
    op = rng.random()
    m = len(w)
    if op < 0.5:
        i = rng.randrange(m)
        w[i] = max(0, w[i] + rng.choice([-2, -1, 1, 2]))
    elif op < 0.7:
        i = rng.randrange(m)
        blk[i] = rng.randrange(max(blk) + 1 if rng.random() < 0.9 else max(blk) + 1)
    elif op < 0.85:
        i = rng.randrange(m)
        if kind == "graphic":
            edges[i] = tuple(rng.sample(range(n), 2))
        else:
            k = max(c.bit_length() for c in cols)
            cols[i] = rng.randrange(1, 1 << k)
    else:
        if m < 9 and rng.random() < 0.6:
            if kind == "graphic":
                edges.append(tuple(rng.sample(range(n), 2)))
            else:
                k = max(c.bit_length() for c in cols)
                cols.append(rng.randrange(1, 1 << k))
            blk.append(rng.randrange(max(blk) + 1))
            w.append(rng.randrange(0, 7))
        elif m > 5:
            i = rng.randrange(m)
            del blk[i], w[i]
            if kind == "graphic":
                del edges[i]
            else:
                del cols[i]
    data = (n, edges) if kind == "graphic" else cols
    return (kind, data, blk, w)


def score(desc):
    kind, data, blk, w = desc
    M = build(desc)
    k = M.k
    if k < 2 or len(set(blk)) != k or max(blk) >= k:
        return None
    if not has_rainbow(M, blk, k):
        return None
    ex, lens, ok = stage_lengths(M, blk, k, [Fraction(x) for x in w])
    if ex is None:
        return (999, lens, False)
    return (ex, lens, ok)


def random_desc(rng):
    if rng.random() < 0.7:
        n = rng.randint(4, 5)
        m = rng.randint(n + 1, 8)
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        k = n - 1
        blk = [i if i < k else rng.randrange(k) for i in range(m)]
        return ("graphic", (n, edges), blk, [rng.randrange(0, 7) for _ in range(m)])
    k = rng.randint(3, 4)
    m = rng.randint(k + 2, 8)
    cols = [rng.randrange(1, 1 << k) for _ in range(m)]
    blk = [i if i < k else rng.randrange(k) for i in range(m)]
    return ("binary", cols, blk, [rng.randrange(0, 7) for _ in range(m)])


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    best = (-99, None, None)
    bad = []
    while time.time() - t0 < budget:
        cur = random_desc(rng)
        sc = score(cur)
        if sc is None:
            continue
        for _ in range(300):
            if time.time() - t0 > budget:
                break
            cand = mutate(cur, rng)
            s2 = score(cand)
            if s2 is None:
                continue
            if not s2[2]:
                bad.append(cand)
            if s2[0] >= sc[0]:
                cur, sc = cand, s2
        if sc[0] > best[0]:
            best = (sc[0], cur, sc[1])
    return best, bad[:3]


def main():
    nw = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    with Pool(nw) as pool:
        res = pool.map(work, [(s, budget) for s in range(7000, 7000 + nw)])
    res.sort(key=lambda x: -x[0][0])
    print("non-optimal or runaway instances:", sum(len(b) for _, b in res))
    for (ex, desc, lens), bad in res[:6]:
        print("excess", ex, "stage lengths", lens, "instance", desc)


if __name__ == "__main__":
    main()
