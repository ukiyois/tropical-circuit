"""A potential for termination of the PO-SL stage.

With S the level-0 avoidable set and E(S) its elements, let
  C(v, S) = { (y, g) : y in E(S), g notin E(S), v_y <= v_g }.
Within a stage the raised elements only move down relative to the others.
Hypothesis: every application either raises nu0, or strictly enlarges S, or
keeps S and strictly enlarges C (a raised element reaches or passes an
unraised one).  Then a stage has at most k * m^2 + 1 applications.
Checked on every application, with counts of each case and of violations
(S shrinking, or S unchanged and C not growing).
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


def cross_set(M, blk, v, S):
    ES = [e for e in range(M.m) if blk[e] in S]
    rest = [e for e in range(M.m) if blk[e] not in S]
    return {(y, g) for y in ES for g in rest if v[y] <= v[g]}


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 79
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    rng = random.Random(seed)
    gens = [uniform_fine, binary_dense, graphic_multi,
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*st.binary5(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*rp.bipartite(g))]
    cnt = {"aug": 0, "Sgrow": 0, "Cgrow": 0, "Sshrink": 0, "stuck": 0}
    for i in range(trials):
        M, blk, k, w = gens[i % len(gens)](rng)
        comp = components(M)
        p = {b: ZERO for b in range(k)}
        for r in range(k):
            for _ in range(3 * k + 3):
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                th = theta_posl(M, v, comp)
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                if res is None or all(x == 0 for x in res[0].values()):
                    break
                S0 = avoid_set(M, blk, k, rp.optimal_bases(M, v), r)
                C0 = cross_set(M, blk, v, S0)
                p = {b: p[b] + res[0][b] for b in range(k)}
                v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                ob = rp.optimal_bases(M, v2)
                if max(len({blk[e] for e in B}) for B in ob) > r:
                    cnt["aug"] += 1
                    continue
                S2 = avoid_set(M, blk, k, ob, r)
                if S2 > S0:
                    cnt["Sgrow"] += 1
                elif S2 != S0:
                    cnt["Sshrink"] += 1
                elif cross_set(M, blk, v2, S0) > C0:
                    cnt["Cgrow"] += 1
                else:
                    cnt["stuck"] += 1
    print(cnt)


if __name__ == "__main__":
    main()
