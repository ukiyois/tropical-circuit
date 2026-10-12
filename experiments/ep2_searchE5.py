"""Phase 2e: hill climbing against Theorem E.5 (a test of its proof) and against Conjecture P
in the regimes Theorem E.5 does not cover.

Mode 'E5': objective over epochs whose components with raised anchors are all of type a or b
(ep2_psi.comp_type): (#violations of C1 or C2, n - 1 - Psi(v^0), n); also rewards type-b
epochs (ties broken by the number of updates linking in a type-b component).
Mode 'LOW': objective (n - 1 - P1(v^0), #low-linking updates, n) over epochs with rho >= 2
that contain at least one low-linking update.
Mode 'S3': objective (n - 1 - P1(v^0), n) over epochs having a component with three or
more raised-anchor values.
Mode 'PHIT': objective (max over the non-last updates having a linking pair with
v_y >= T_K of [Phi(v^{i+1}) - Phi(v^i) + 1], number of raised values strictly inside
(a_K, T_K), n): a positive first entry is a failure of the gap potential at an update
whose linking reaches the top value.
Usage: python ep2_searchE5.py mode kind n m budget workers [bits] [seed0]
"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
from stage_search_exp import random_desc
from ep_search import mutate2
from ep_struct import random_struct
from ep2_common import epoch_states, P1, raised_anchor_values
from ep2_search import random_cut
from ep2_trace import linking_pairs
from ep2_psi import comp_type, psi
from ep2_phi import phi

MODE = "E5"


def e5_score(rec):
    M, Bs, R = rec["M"], rec["B"], rec["R"]
    sts = rec["states"]
    n = len(sts) - 1
    v0 = sts[0]
    comps = sorted(raised_anchor_values(rec, v0))
    types = {c: comp_type(rec, v0, c) for c in comps}
    if not all(t in ("a", "b") for t in types.values()):
        return None
    dl = rec["delta"]
    high = {c: False for c in comps}
    viol, inb = 0, 0
    for i in range(n - 1):
        v, v2 = sts[i], sts[i + 1]
        lp, _ = linking_pairs(M, Bs, R, v, dl[i])
        g = lp[0][1]
        cl = M.comp[g]
        newhigh = dict(high)
        if types[cl] == "b" and v[g] >= raised_anchor_values(rec, v)[cl][0]:
            newhigh[cl] = True
        for c in comps:
            p1 = psi(rec, v, c, types[c], high[c])
            p2 = psi(rec, v2, c, types[c], newhigh[c])
            if p2 > p1 or (c == cl and p1 - p2 < 1):
                viol += 1
        if types[cl] == "b":
            inb += 1
        high = newhigh
    s0 = sum(psi(rec, v0, c, types[c], False) for c in comps)
    return (viol + max(0, n - 1 - s0), inb, n)


def low_count(rec):
    M, Bs, R = rec["M"], rec["B"], rec["R"]
    sts = rec["states"]
    n = len(sts) - 1
    low = 0
    for i in range(n - 1):
        v = sts[i]
        vals = raised_anchor_values(rec, v)
        lp, _ = linking_pairs(M, Bs, R, v, rec["delta"][i])
        y, g = lp[0]
        top = vals[M.comp[y]][-1]
        hs = [h for h in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y))
              if h in R and v[y] - rec["delta"][i] <= v[h] <= v[y] and v[h] == top]
        low += not hs
    return low


def score(desc):
    best = None
    try:
        for rec in epoch_states(desc, cap=500):
            if rec["rho"] < 2:
                continue
            sts = rec["states"]
            n = len(sts) - 1
            if MODE == "E5":
                key = e5_score(rec)
            elif MODE == "LOW":
                lw = low_count(rec)
                key = (n - 1 - P1(rec, sts[0]), lw, n) if lw else None
            elif MODE == "PHIT":
                M, Bs, R = rec["M"], rec["B"], rec["R"]
                viol = None
                for i in range(n - 1):
                    v = sts[i]
                    lp, _ = linking_pairs(M, Bs, R, v, rec["delta"][i])
                    vals = raised_anchor_values(rec, v)
                    if any(v[y] >= vals[M.comp[y]][-1] for (y, g) in lp):
                        x = phi(rec, sts[i + 1]) - phi(rec, v) + 1
                        viol = x if viol is None else max(viol, x)
                if viol is None:
                    key = None
                else:
                    v0 = sts[0]
                    gates = 0
                    for c, s_ in raised_anchor_values(rec, v0).items():
                        gates += len({v0[x] for x in R if M.comp[x] == c and s_[0] < v0[x] < s_[-1]})
                    key = (viol, gates, n)
            else:
                vals = raised_anchor_values(rec, sts[0])
                key = (n - 1 - P1(rec, sts[0]), n) if max(len(s) for s in vals.values()) >= 3 else None
            if key is not None and (best is None or key > best):
                best = key
    except (RuntimeError, AssertionError):
        return None
    return best


def hill(args):
    seed, mode, kind, n, m, budget, bits = args
    global MODE
    MODE = mode
    rng = random.Random(seed)
    t0 = time.time()
    best = (None, None)
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
            if s2 >= s:
                if s2 > s:
                    stall = 0
                cur, s = cand, s2
        if best[0] is None or s > best[0]:
            best = (s, cur)
    return best


if __name__ == "__main__":
    mode, kind, n, m, budget, workers = (sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]),
                                         float(sys.argv[5]), int(sys.argv[6]))
    bits = int(sys.argv[7]) if len(sys.argv) > 7 else 24
    seed0 = int(sys.argv[8]) if len(sys.argv) > 8 else 9000
    with Pool(workers) as pool:
        res = pool.map(hill, [(s, mode, kind, n, m, budget, bits) for s in range(seed0, seed0 + workers)])
    res = [r for r in res if r[0] is not None]
    res.sort(key=lambda x: x[0], reverse=True)
    print(f"mode={mode} kind={kind} n={n} m={m} budget={budget} bits={bits}")
    for key, desc in res:
        print("score", key, "desc", desc)
    sys.stdout.flush()
