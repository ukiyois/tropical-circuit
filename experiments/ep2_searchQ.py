"""Phase 2e: hill climbing against Conjectures Q and P of B0d (epochs with rho >= MINRHO).

Per epoch: designations as in ep_cases2.classify; repeats = case (I) updates whose
z1 was designated before; Qslack = repeats + #IV - #{x in R - B*: v_x < T_K(x)};
Pslack = n - 1 - P1(v^0).  Objective (lexicographic): OBJ = 'Q' -> (Qslack, Pslack, n),
'P' -> (Pslack, Qslack, n).  Also counts the updates whose linking raised non-anchors
all have their nearby raised anchor below the top value of the component ('low').
Instances: 'graphic' (random multigraph), 'struct' (tree + parallel copies + chords),
'cut' (two multigraphs glued at a vertex).
Usage: python ep2_searchQ.py kind n m budget workers OBJ [minrho] [bits] [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search_exp import random_desc
from ep_search import mutate2
from ep_struct import random_struct
from ep_cases2 import classify
from stage_epoch_check import D_of
from ep2_common import epoch_states, P1, raised_anchor_values
from ep2_search import random_cut
from ep2_trace import linking_pairs

OBJ = "Q"
MINRHO = 2


def epoch_stats(rec):
    M, Bs, R, blk, k = rec["M"], rec["B"], rec["R"], rec["blk"], rec["k"]
    sts = rec["states"]
    n = len(sts) - 1
    v0 = sts[0]
    tops = {c: s[-1] for c, s in raised_anchor_values(rec, v0).items()}
    budget = sum(1 for x in R if not (Bs >> x & 1) and M.comp[x] in tops and v0[x] < tops[M.comp[x]])
    seen, rep, iv, low = set(), 0, 0, 0
    for i in range(n - 1):
        v = sts[i]
        delta = rec["delta"][i]
        c = classify(M, blk, k, v, rec["r"], rec["S"], Bs, delta)
        if c[0] == "I":
            if c[2] in seen:
                rep += 1
            seen.add(c[2])
        else:
            iv += 1
        vals = raised_anchor_values(rec, v)
        lp, _ = linking_pairs(M, Bs, R, v, delta)
        islow = True
        for (y, g) in lp:
            top = vals[M.comp[y]][-1]
            hs = [h for h in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y))
                  if h in R and v[y] - delta <= v[h] <= v[y] and v[h] == top]
            if hs:
                islow = False
        low += islow
    return rep + iv - budget, n - 1 - P1(rec, v0), n, low


def score(desc):
    best = None
    try:
        for rec in epoch_states(desc, cap=600, want_delta=True):
            if rec["rho"] < MINRHO:
                continue
            q, p, n, low = epoch_stats(rec)
            key = (q, p, n) if OBJ == "Q" else (p, q, n)
            info = (n, rec["r"], rec["rho"], len(rec["U"]), len(rec["R"]), "low", low)
            if best is None or key > best[0]:
                best = (key, info)
    except (RuntimeError, AssertionError):
        return None
    return best


def hill(args):
    seed, kind, n, m, budget, bits, obj, minrho = args
    global OBJ, MINRHO
    OBJ, MINRHO = obj, minrho
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
        while stall < 500 and time.time() - t0 < budget:
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
    kind, n, m, budget, workers, obj = (sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
                                        float(sys.argv[4]), int(sys.argv[5]), sys.argv[6])
    minrho = int(sys.argv[7]) if len(sys.argv) > 7 else 2
    bits = int(sys.argv[8]) if len(sys.argv) > 8 else 24
    seed0 = int(sys.argv[9]) if len(sys.argv) > 9 else 1000
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, kind, n, m, budget, bits, obj, minrho) for s in range(seed0, seed0 + workers)])
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"kind={kind} n={n} m={m} budget={budget} obj={obj} minrho={minrho} bits={bits}")
    for key, info, desc in res:
        print("score", key, "(n,r,rho,|U|,|R|,low)", info, "desc", desc)
    sys.stdout.flush()
