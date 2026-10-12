"""Per-update checks inside an epoch (S0 fixed, nu0 = r), PO-SL family.

For a state v in stage r with B* a minimum base meeting r blocks (kept fixed for
the epoch), R = E_S, U = E - R:
  D(v) = min { v_y - v_g : y in R - B*, g in C(B*, y) - R }  (> 0 inside the epoch)
Checked at every update:
  (G)  D' <= D - delta  and  delta >= D / (2q - 1),  q = max_K #distinct B*-values in K
  (A)  anchor crossing: some pair (x in R, z in U) with x or z in B*, v_x > v_z, v'_x <= v'_z
  (E)  D' = 0 exactly when the epoch ends (nu0 rises or S0 grows)
Usage: python stage_epoch_check.py seed trials
"""
import random
import sys

import stage_core as sc
from stage_search import random_desc, build, has_rainbow


def first_event(M, blk, k, v, r, S0):
    for t in sc.levels_of(v):
        N = sc.posl(M, v, t)
        nu, av, _ = sc.rainbow_av(N, blk, k)
        if nu > r or av != S0:
            return t
    return None


def base_meeting_r(M, blk, k, v, r):
    """A minimum base of v meeting exactly r blocks: extend a max rainbow independent set of M^v."""
    N = sc.MinBase(M, v)
    nu, av, I = sc.rainbow_av(N, blk, k)
    assert nu == r
    B = I
    order = sorted(range(M.m), key=lambda e: v[e])
    for e in order:
        if N.indep(B | (1 << e)):
            B |= 1 << e
    assert sc.popcount(B) == M.k
    assert len({blk[e] for e in sc.bits(B)}) == r
    return B


def D_of(M, Bs, R, v):
    best = None
    for y in R:
        if Bs >> y & 1:
            continue
        for g in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
            if g in R:
                continue
            d = v[y] - v[g]
            best = d if best is None or d < best else best
    return best


def check_stage(M, blk, k, v, r, stats, examples):
    Bs = None
    S_cur = None
    while True:
        nu0, S0 = sc.state(M, blk, k, v)
        if nu0 > r:
            return
        if S0 != S_cur:
            S_cur = S0
            Bs = base_meeting_r(M, blk, k, v, r)
        R = {e for e in range(M.m) if blk[e] in S0}
        D = D_of(M, Bs, R, v)
        assert D is not None and D > 0, (D,)
        q = 0
        for c in range(M.ncomp):
            q = max(q, len({v[e] for e in sc.bits(Bs) if M.comp[e] == c}))
        delta = first_event(M, blk, k, v, r, S0)
        tau, lam, a, _ = sc.update(M, blk, k, v, r)
        v2 = sc.shift(v, blk, a)
        D2 = D_of(M, Bs, R, v2)
        stats["steps"] += 1
        if not (D2 <= D - delta and delta * (2 * q - 1) >= D):
            stats["G_fail"] += 1
            examples.append(("G", blk, list(v), r))
        cross = False
        for x in R:
            for z in range(M.m):
                if z in R:
                    continue
                if not ((Bs >> x & 1) or (Bs >> z & 1)):
                    continue
                if v[x] > v[z] and v2[x] <= v2[z]:
                    cross = True
                    break
            if cross:
                break
        if not cross:
            stats["A_fail"] += 1
            if len(examples) < 5:
                examples.append(("A", blk, list(v), r))
        nu1, S1 = sc.state(M, blk, k, v2)
        ended = nu1 > r or S1 != S0
        if ended != (D2 == 0):
            stats["E_fail"] += 1
            examples.append(("E", blk, list(v), r))
        v = v2


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    stats = {"steps": 0, "G_fail": 0, "A_fail": 0, "E_fail": 0, "stages": 0}
    examples = []
    for _ in range(trials):
        kind = rng.choice(["graphic", "binary", "uniform"])
        wmax = rng.choice([6, 12, 100, 1000])
        if kind == "graphic":
            n = rng.randint(4, 6)
            d = random_desc(rng, kind, n, rng.randint(n + 2, 11), wmax=wmax)
        else:
            kk = rng.randint(3, 5)
            d = random_desc(rng, kind, kk, rng.randint(kk + 2, 11), kk, wmax=wmax)
        M = build(d)
        _, _, blk, w = d
        k = M.k
        if not has_rainbow(M, blk, k):
            continue
        v = list(w)
        for r in range(1, k):
            nu0, _ = sc.state(M, blk, k, v)
            if nu0 > r:
                continue
            stats["stages"] += 1
            check_stage(M, blk, k, v, r, stats, examples)
            c, v = sc.run_stage(M, blk, k, v, r)
    print(stats)
    for ex in examples[:5]:
        print(ex)


if __name__ == "__main__":
    main()
