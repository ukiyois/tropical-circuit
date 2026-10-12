"""Which readings of the note's definitions are needed?

(a) PO(t) with v_g <= v_f - t (g != f) instead of v_g < v_f - t      -> (F1)?
(b) single linkage with gaps < t instead of <= t                       -> (F1)?
(c) C(v,S) with v_y < v_g instead of v_y <= v_g                        -> Thm 8 item 3?
(d) lam_b read as 'some base of N(t) meeting AT MOST r blocks avoids b' -> Thm 6?
Each reading is tested on random states; the first counterexample is printed.
"""
import random
import sys
from core import *
import test_main as TM


def po_set_weak(M, v, t):
    out = []
    for f in range(M.m):
        if M.R[1 << f] == 0:
            continue
        low = 0
        for g in range(M.m):
            if g != f and v[g] <= v[f] - t:
                low |= 1 << g
        if not M.in_cl(low, f):
            out.append(f)
    return out


def N_variant(M, v, t, weak_po=False, strict_link=False):
    po = po_set_weak(M, v, t) if weak_po else po_set(M, v, t)
    u = [INF] * M.m
    for c in set(M.comp):
        el = sorted((e for e in po if M.comp[e] == c), key=lambda e: (v[e], e))
        lab = 0
        for i, e in enumerate(el):
            if i > 0 and (v[e] - v[el[i - 1]] >= t if strict_link else v[e] - v[el[i - 1]] > t):
                lab += 1
            u[e] = lab
    return opt_bases(M, u)[0]


def lam_atmost(M, blk, k, v, r):
    T = breakpoints(v, M.m)
    tau = None
    lam = {b: INF for b in range(k)}
    for t in T:
        N = N_posl(M, v, t)
        if nu_of(N, blk) > r:
            tau = t
            break
        for B in N:
            bl = blocks_of(B, blk)
            if len(bl) <= r:
                for b in set(range(k)) - bl:
                    if lam[b] == INF:
                        lam[b] = t
    a = {b: F0 if (tau is None or lam[b] == INF) else max(tau - lam[b], F0) for b in range(k)}
    return tau, a


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    found = {"a": None, "b": None, "c": None, "d": None}
    cnt = {"a": 0, "b": 0, "c": 0, "d": 0, "states": 0, "item3": 0}
    for _ in range(trials):
        kind, M = random_matroid(rng)
        if M.k == 0:
            continue
        k = M.k
        blk = rand_blocks(M, k, rng)
        if blk is None:
            continue
        v = rand_values(M.m, rng, rng.choice(["ties", "ties5", "spaced"]))
        N0, _ = opt_bases(M, v)
        r = nu_of(N0, blk)
        cnt["states"] += 1
        if N_variant(M, v, F0, weak_po=True) != N0:
            cnt["a"] += 1
            found["a"] = found["a"] or (kind, M.m, [str(x) for x in v])
        if N_variant(M, v, F0, strict_link=True) != N0:
            cnt["b"] += 1
            found["b"] = found["b"] or (kind, M.m, [str(x) for x in v])
        if r >= k:
            continue
        tau, lam, a, _ = posl_update(M, blk, k, v, r)
        v2 = [v[e] - a[blk[e]] for e in range(M.m)]
        N0b, _ = opt_bases(M, v2)
        S, _ = avoidable(N0, blk, k)
        if nu_of(N0b, blk) == r and avoidable(N0b, blk, k)[0] == S:
            cnt["item3"] += 1
            ES = [e for e in range(M.m) if blk[e] in S]
            rest = [e for e in range(M.m) if blk[e] not in S]
            Cs0 = {(y, g) for y in ES for g in rest if v[y] < v[g]}
            Cs1 = {(y, g) for y in ES for g in rest if v2[y] < v2[g]}
            if not Cs0 < Cs1:
                cnt["c"] += 1
                found["c"] = found["c"] or (kind, M.m, blk, [str(x) for x in v], r)
        tau2, a2 = lam_atmost(M, blk, k, v, r)
        v3 = [v[e] - a2[blk[e]] for e in range(M.m)]
        gain = sum(a2.values(), F0) + beta(M, v3) - beta(M, v)
        if gain != (k - r) * tau2:
            cnt["d"] += 1
            found["d"] = found["d"] or (kind, M.m, blk, [str(x) for x in v], r, str(gain), str((k - r) * tau2))
    print(cnt)
    for key, val in found.items():
        print(key, val)


if __name__ == "__main__":
    main()
