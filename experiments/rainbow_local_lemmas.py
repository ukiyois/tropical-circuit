"""Lemmas behind the 'local' update, checked along the schedule.

Notation: theta(B) = max { v_f - v_e : e notin B, f in C(B,e) }_+ ,
Bt = { B : theta(B) <= t },  dist(B, Bt) = min_{B' in Bt} |B - B'|.

(L1) layer cake:  excess(B) >= integral_0^inf dist(B, Bt) dt      (all bases B)
     [proof: steepest single-exchange descent; checked here, and equality
      is recorded separately]
(L2) Koenig-type bound, at a stage-r state and every t < tau:
         max_{B' in Bt} |B' cap E(S_t)| == |S_t| - (k - r),
     S_t = blocks avoided by some B' in Bt meeting r blocks.
(L3) exactness witness: some optimal base B0 has
         |B0 cap E(S_t)| == |S_t| - (k - r)   for every t < tau.
(L4) progress: nu0 rises, or the avoidable set at level 0 strictly grows.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import fundamental_circuit, update

ZERO = Fraction(0)
INF = rp.INF


def theta_map(M, v):
    out = {}
    for B in M.bases:
        th = ZERO
        for e in range(M.m):
            if e in B or M.rank([e]) == 0:
                continue
            for f in fundamental_circuit(M, B, e):
                th = max(th, v[f] - v[e])
        out[B] = th
    return out


def avoid_set(M, blk, k, fam, r):
    S = set()
    for B in fam:
        blocks = {blk[e] for e in B}
        if len(blocks) == r:
            S |= set(range(k)) - blocks
    return S


def check_state(M, blk, k, v, r, stats):
    th = theta_map(M, v)
    b0 = rp.beta(M, v)
    levels = sorted(set(th.values()))
    # L1 for every base
    for B in M.bases:
        integral = ZERO
        for i, t in enumerate(levels):
            nxt = levels[i + 1] if i + 1 < len(levels) else None
            if nxt is None:
                break
            fam = [B2 for B2 in M.bases if th[B2] <= t]
            d = min(len(B - B2) for B2 in fam)
            integral += d * (nxt - t)
        ex = rp.weight(v, B) - b0
        stats["L1"] += (ex >= integral)
        stats["L1_eq"] += (ex == integral)
        stats["L1_n"] += 1
    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
    res = update(entries, k, r)
    if res is None:
        return
    a, tau = res
    opt_bases = [B for B in M.bases if th[B] == 0]
    good_b0 = set(opt_bases)
    for t in levels:
        if t >= tau:
            break
        fam = [B for B in M.bases if th[B] <= t]
        S = avoid_set(M, blk, k, fam, r)
        ES = {e for e in range(M.m) if blk[e] in S}
        rho = max(len(B & ES) for B in fam)
        stats["L2"] += (rho == len(S) - (k - r))
        stats["L2_le"] += (rho <= len(S) - (k - r))
        stats["L2_n"] += 1
        good_b0 = {B for B in good_b0 if len(B & ES) == len(S) - (k - r)}
    stats["L3"] += bool(good_b0)
    stats["L3_n"] += 1
    # L4
    S0 = avoid_set(M, blk, k, opt_bases, r)
    v2 = {e: v[e] - a[blk[e]] for e in range(M.m)}
    th2 = theta_map(M, v2)
    opt2 = [B for B in M.bases if th2[B] == 0]
    nu2 = max(len({blk[e] for e in B}) for B in opt2)
    if nu2 > r:
        stats["L4_aug"] += 1
    else:
        S2 = avoid_set(M, blk, k, opt2, r)
        stats["L4_grow"] += (S2 > S0)
        stats["L4_fail"] += not (S2 > S0)
    return a


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow), ("binary5", st.binary5)]
    for name, fam in fams:
        stats = {key: 0 for key in ["L1", "L1_eq", "L1_n", "L2", "L2_le", "L2_n", "L3", "L3_n",
                                     "L4_aug", "L4_grow", "L4_fail"]}
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            p = {b: ZERO for b in range(k)}
            for r in range(k):
                for _ in range(r + 1):
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    a = check_state(M, blk, k, v, r, stats)
                    if a is None:
                        break
                    p = {b: p[b] + a[b] for b in range(k)}
        print(f"{name:13s} L1 {stats['L1']}/{stats['L1_n']} (equality {stats['L1_eq']})  "
              f"L2 == {stats['L2']}/{stats['L2_n']} (<= {stats['L2_le']})  "
              f"L3 {stats['L3']}/{stats['L3_n']}  "
              f"L4 augment {stats['L4_aug']} grow {stats['L4_grow']} fail {stats['L4_fail']}", flush=True)


if __name__ == "__main__":
    main()
