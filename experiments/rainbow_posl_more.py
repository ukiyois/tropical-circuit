"""PO-SL: continuity of U_r (r fixed) and the strict progress dichotomy.

(C) continuity: max |a(v + eps xi) - a(v)| for eps = 1e-2, 1e-3, 1e-4 at states
    with ties, r fixed to nu0(v).
(P) after one application: nu0 rises, or the level-0 avoidable set strictly
    grows (the matroid form of Theorem 4.9).
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import avoid_set
from rainbow_rpim import components
from rainbow_posl import theta_posl
from rainbow_family_stress import uniform_fine, binary_dense, graphic_multi

ZERO = Fraction(0)


def fixed_r_update(M, blk, k, v, comp, r):
    th = theta_posl(M, v, comp)
    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
    big = [x for x, S in entries if len(S) >= r + 1]
    tau = min(big) if big else rp.INF
    a = {}
    for b in range(k):
        c = [x for x, S in entries if len(S - {b}) >= r]
        lam = min(c) if c else rp.INF
        a[b] = ZERO if tau == rp.INF or lam == rp.INF else max(tau - lam, ZERO)
    return a


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 73
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    worst = {1: ZERO, 2: ZERO, 3: ZERO}
    for _ in range(trials):
        fam = rng.choice([rp.bipartite, st.uniform, rp.rainbow_tree, rp.binary_rainbow])
        M, blk, k = fam(rng)
        v = {e: Fraction(rng.randint(0, 3)) for e in range(M.m)}
        r = max(len({blk[e] for e in B}) for B in rp.optimal_bases(M, v))
        if r == k:
            continue
        comp = components(M)
        xi = {e: Fraction(rng.randint(-100, 100), 100) for e in range(M.m)}
        a0 = fixed_r_update(M, blk, k, v, comp, r)
        for j in (1, 2, 3):
            eps = Fraction(1, 10 ** (j + 1))
            a2 = fixed_r_update(M, blk, k, {e: v[e] + eps * xi[e] for e in range(M.m)}, comp, r)
            worst[j] = max(worst[j], max(abs(a2[b] - a0[b]) for b in range(k)))
    print(f"(C) PO-SL continuity: max change at eps=1e-2,1e-3,1e-4: "
          f"{float(worst[1]):.4f}, {float(worst[2]):.4f}, {float(worst[3]):.4f}", flush=True)

    gens = [uniform_fine, binary_dense, graphic_multi,
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*st.binary5(g))]
    aug = grow = fail = 0
    for i in range(trials * 2):
        M, blk, k, w = gens[i % len(gens)](rng)
        comp = components(M)
        p = {b: ZERO for b in range(k)}
        for r in range(k):
            for _ in range(r + 2):
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                th = theta_posl(M, v, comp)
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                if res is None or all(x == 0 for x in res[0].values()):
                    break
                S0 = avoid_set(M, blk, k, rp.optimal_bases(M, v), r)
                p = {b: p[b] + res[0][b] for b in range(k)}
                v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                ob = rp.optimal_bases(M, v2)
                if max(len({blk[e] for e in B}) for B in ob) > r:
                    aug += 1
                elif avoid_set(M, blk, k, ob, r) > S0:
                    grow += 1
                else:
                    fail += 1
    print(f"(P) progress dichotomy: augment {aug}, avoidable set grows {grow}, neither {fail}", flush=True)


if __name__ == "__main__":
    main()
