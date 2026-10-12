"""Phase 2e: hill climbing against the gap potential Phi (ep2_phi.py).

Objective per instance: max over epochs with rho >= MINRHO of
    (max_i [Phi(v^{i+1}) - Phi(v^i) + 1],  n - 1 - Phi(v^0),  n)
over the updates i that are not last; a positive first entry refutes the claim
"Phi drops by at least 1 at every update that is not last", a positive second
entry refutes n <= 1 + Phi(v^0).
Instances: 'graphic' (random multigraph, n vertices), 'cut' (two random multigraphs
glued at a vertex: several connected components of M), 'struct' (tree + parallel
copies + 3 chords), exponential integer weights.
Usage: python ep2_search.py kind n m budget workers [minrho] [bits] [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc, mutate
from ep_search import mutate2
from ep_struct import random_struct
from ep2_common import epoch_states
from ep2_phi import phi

MINRHO = 2


def score(desc):
    best = None
    try:
        for rec in epoch_states(desc, cap=600, want_delta=False):
            if rec["rho"] < MINRHO:
                continue
            sts = rec["states"]
            n = len(sts) - 1
            ph = [phi(rec, v) for v in sts[:n]]
            viol = max([ph[i + 1] - ph[i] + 1 for i in range(n - 1)], default=-99)
            key = (viol, n - 1 - ph[0], n)
            info = (n, rec["r"], rec["rho"], len(rec["U"]), len(rec["R"]))
            if best is None or key > best[0]:
                best = (key, info)
    except (RuntimeError, AssertionError):
        return None
    return best


def random_cut(rng, n, m, bits):
    # two random multigraphs on vertex sets {0..h} and {h..n-1}, glued at vertex h
    h = n // 2
    while True:
        edges = []
        for i in range(m):
            if i % 2 == 0:
                edges.append(tuple(rng.sample(range(0, h + 1), 2)))
            else:
                edges.append(tuple(rng.sample(range(h, n), 2)))
        if sc.graphic(n, edges).k == n - 1:
            break
    k = n - 1
    blk = [i if i < k else rng.randrange(k) for i in range(m)]
    rng.shuffle(blk)
    return ("graphic", (n, edges), blk, [rng.randrange(0, 1 << rng.randint(1, bits)) for _ in range(m)])


def hill(args):
    seed, kind, n, m, budget, bits, minrho = args
    global MINRHO
    MINRHO = minrho
    rng = random.Random(seed)
    t0 = time.time()
    best = ((-999, -999, 0), None, None)
    while time.time() - t0 < budget:
        if kind == "cut":
            cur = random_cut(rng, n, m, bits)
        elif kind == "struct":
            cur = random_struct(rng, n, m, bits, 3)
        else:
            cur = random_desc(rng, kind, n, m, bits)
        s = score(cur)
        if s is None:
            continue
        stall = 0
        while stall < 600 and time.time() - t0 < budget:
            cand = mutate2(cur, rng, bits)
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
    kind, n, m, budget, workers = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    minrho = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    bits = int(sys.argv[7]) if len(sys.argv) > 7 else 24
    seed0 = int(sys.argv[8]) if len(sys.argv) > 8 else 1000
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, kind, n, m, budget, bits, minrho) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"kind={kind} n={n} m={m} budget={budget} minrho={minrho} bits={bits} objective=(Phi violation, n-1-Phi0, n)")
    for key, info, desc in res:
        print("score", key, "(n,r,rho,|U|,|R|)", info, "desc", desc)
    sys.stdout.flush()
