"""Phase 2e: weight-only hill climbing on fixed designs aimed at (F-T) updates
(Theorem E.5) and at violations of Conjecture P (n > 1 + P1).

Design 'ft2' (graphic, 6 vertices, k = 5, one unraised block 0):
  0 h_a=(0,1) b1   1 h_T=(1,2) b2   2 g=(2,3) b0   3 g_f=(2,4) b0   4 g_3=(2,5) b0
  5 x_a=(0,1) b3   6 x_T=(1,2) b4   7 y=(1,3) b1   8 y_f=(1,4) b3   9 y_3=(1,5) b4
  10 c=(0,2) b2    11 f=(2,4) b0    12 f_3=(2,5) b0
Intended: IT(g) [F-T], Ia(f), IT(f), IT(g_f) [F-T], Ia(f_3), IT(f_3), IT(g_3), last.
Objective (lexicographic): (n - 1 - P1, #(F-T updates), n) over epochs with rho >= 2.
Usage: python ep2_ft_search.py design budget workers [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

from ep2_common import epoch_states, P1, raised_anchor_values
from ep_cases2 import classify

DESIGNS = {
    "ft2": ((6, [(0, 1), (1, 2), (2, 3), (2, 4), (2, 5), (0, 1), (1, 2), (1, 3), (1, 4), (1, 5),
                 (0, 2), (2, 4), (2, 5)]),
            [1, 2, 0, 0, 0, 3, 4, 1, 3, 4, 2, 0, 0]),
}


def ft_count(rec):
    M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
    sts = rec["states"]
    n = len(sts) - 1
    ft = 0
    for i in range(n - 1):
        v, v2 = sts[i], sts[i + 1]
        cls = classify(M, rec["blk"], rec["k"], v, rec["r"], rec["S"], Bs, rec["delta"][i])
        if cls[0] != "I":
            continue
        g = cls[3]
        c = M.comp[g]
        vals = raised_anchor_values(rec, v)[c]
        if len(vals) < 2:
            continue
        a, T = vals[0], vals[-1]
        W = [z for z in U if M.comp[z] == c and a <= v[z] < T]
        below2 = [z for z in U if M.comp[z] == c and v2[z] < a]
        if W == [g] and cls[2] == g and v2[g] >= v2[cls[1]] and below2:
            ft += 1
    return ft


def score(desc):
    best = None
    try:
        for rec in epoch_states(desc, cap=400):
            if rec["rho"] < 2:
                continue
            n = len(rec["states"]) - 1
            key = (n - 1 - P1(rec, rec["states"][0]), ft_count(rec), n)
            if best is None or key > best:
                best = key
    except (RuntimeError, AssertionError):
        return None
    return best


def mutate_w(w, rng, bits):
    w = list(w)
    i = rng.randrange(len(w))
    op = rng.random()
    if op < 0.3:
        j, l = rng.randrange(len(w)), rng.randrange(len(w))
        w[i] = (w[j] + w[l]) // 2
    elif op < 0.5:
        w[i] = max(0, w[i] * 2 if rng.random() < 0.5 else w[i] // 2)
    elif op < 0.7:
        j = rng.randrange(len(w))
        w[i] = max(0, w[j] + rng.choice([-1, 1]) * (1 << rng.randrange(bits)))
    else:
        w[i] = max(0, w[i] + rng.choice([-1, 1]) * rng.randrange(1, 1 + (1 << rng.randrange(bits))))
    return [min(x, 1 << bits) for x in w]


def hill(args):
    seed, design, budget, bits = args
    data, blk = DESIGNS[design]
    rng = random.Random(seed)
    t0 = time.time()
    best = ((-99, -99, 0), None)
    while time.time() - t0 < budget:
        w = [rng.randrange(0, 1 << rng.randint(1, bits)) for _ in blk]
        cur = ("graphic", data, blk, w)
        s = score(cur)
        if s is None:
            continue
        stall = 0
        while stall < 600 and time.time() - t0 < budget:
            cand = ("graphic", data, blk, mutate_w(cur[3], rng, bits))
            s2 = score(cand)
            stall += 1
            if s2 is None:
                continue
            if s2 >= s:
                if s2 > s:
                    stall = 0
                cur, s = cand, s2
        if s > best[0]:
            best = (s, cur)
    return best


if __name__ == "__main__":
    design, budget, workers = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
    seed0 = int(sys.argv[4]) if len(sys.argv) > 4 else 5000
    bits = 24
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, design, budget, bits) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"design={design} budget={budget} objective=(n-1-P1, #FT, n)")
    for key, desc in res:
        print("score", key, "desc", desc)
