"""Phase 2e: one-update test of the gap potential Phi at random states.

Every state v with nu0(v) = r < k is the first state of an epoch of stage r, so the
claim "Phi(v') <= Phi(v) - 1 when the update v -> v' does not end the epoch" can be
tested state by state.  Phi does not depend on the choice of B* (Lemma P.0 of B0d).
Random graphic / binary instances, weights in {0..W}; only states with rho >= MINRHO.
Also reports the false variants F0 (no pending term), F3 (raised-anchor values only).
Usage: python ep2_phi_states.py count seed [W] [minrho] [kinds]
"""
import random
import sys
from collections import Counter

import stage_core as sc
from stage_search import build, has_rainbow
from stage_epoch_check import base_meeting_r, D_of, first_event
from ep2_phi import phi


def rand_inst(rng, kinds, W):
    kind = rng.choice(kinds)
    if kind == "graphic":
        n = rng.randint(5, 6)
        m = rng.randint(n + 3, 12)
        while True:
            edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
            if sc.graphic(n, edges).k == n - 1:
                break
        k = n - 1
        data = (n, edges)
    else:
        k = rng.randint(4, 5)
        m = rng.randint(k + 3, 11)
        while True:
            cols = [rng.randrange(1, 1 << k) for _ in range(m)]
            if sc.gf2(cols).k == k:
                break
        data = cols
    blk = [i if i < k else rng.randrange(k) for i in range(m)]
    rng.shuffle(blk)
    w = [rng.randint(0, W) for _ in range(m)]
    return (kind, data, blk, w)


def check(d, cnt, bad, minrho):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    if sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return
    v = list(w)
    nu, S = sc.state(M, blk, k, v)
    if nu >= k:
        return
    r = nu
    rho = len(S) - (k - r)
    if rho < minrho:
        return
    Bs = base_meeting_r(M, blk, k, v, r)
    R = {e for e in range(M.m) if blk[e] in S}
    rec = {"M": M, "B": Bs, "R": R, "U": {e for e in range(M.m) if e not in R}}
    tau, lam, a, _ = sc.update(M, blk, k, v, r)
    v2 = sc.shift(v, blk, a)
    nu2, S2 = sc.state(M, blk, k, v2)
    if nu2 > r or S2 != S:
        cnt["last"] += 1
        return
    cnt["nonlast"] += 1
    delta = first_event(M, blk, k, v, r, S)
    cnt["rigid" if delta == tau else "nonrigid"] += 1
    p1, p2 = phi(rec, v), phi(rec, v2)
    if p1 - p2 < 1:
        cnt["FAIL"] += 1
        if len(bad) < 5:
            bad.append((d, r, p1, p2))
    for var in ("F0", "F3"):
        if phi(rec, v, var) - phi(rec, v2, var) < 1:
            cnt[var] += 1


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    W = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    minrho = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    kinds = sys.argv[5].split(",") if len(sys.argv) > 5 else ["graphic", "binary"]
    rng = random.Random(seed)
    cnt = Counter()
    bad = []
    for _ in range(count):
        check(rand_inst(rng, kinds, W), cnt, bad, minrho)
    print(dict(cnt))
    for b in bad:
        print("FAIL", b)


if __name__ == "__main__":
    main()
