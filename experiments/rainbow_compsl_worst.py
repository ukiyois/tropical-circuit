"""Search for the worst stage length of the component-wise single-linkage update,
and print the trace of the worst instance found.

The update is valid and continuous; what is open is a polynomial bound on the
number of applications in a stage.  Reported: the distribution of
apps - (r+1), its maximum against m and k, and a full trace (tau, raised
blocks, level-0 avoidable set, rainbow rank) of the worst stage.
"""
import random
import sys
from collections import Counter
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import avoid_set
from rainbow_rpim import components
from rainbow_family_stress import theta_compsl, uniform_fine, binary_dense, graphic_multi

ZERO = Fraction(0)


def stage_trace(M, blk, k, w, comp, cap=80):
    p = {b: ZERO for b in range(k)}
    traces = []
    for r in range(k):
        tr = []
        while len(tr) < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_compsl(M, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            a, tau = res
            opt0 = rp.optimal_bases(M, v)
            tr.append((tau, {b: a[b] for b in range(k) if a[b] > 0}, sorted(avoid_set(M, blk, k, opt0, r)),
                       dict(v)))
            p = {b: p[b] + a[b] for b in range(k)}
        traces.append(tr)
    return traces, rp.psi(M, blk, w, p)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 61
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    rng = random.Random(seed)
    gens = [uniform_fine, binary_dense, graphic_multi,
            lambda g: (lambda M, blk, k: (M, blk, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g)),
            lambda g: (lambda M, blk, k: (M, blk, k, st.weights(g, M.m, "generic")))(*st.binary5(g))]
    hist = Counter()
    worst = None
    for i in range(trials):
        M, blk, k, w = gens[i % len(gens)](rng)
        comp = components(M)
        traces, val = stage_trace(M, blk, k, w, comp)
        assert val == rp.opt(M, blk, k, w)
        for r, tr in enumerate(traces):
            ex = len(tr) - (r + 1)
            hist[ex] += 1
            if worst is None or ex > worst[0]:
                worst = (ex, M.m, k, r, blk, w, tr)
    print("apps - (r+1) histogram:", dict(sorted(hist.items())))
    ex, m, k, r, blk, w, tr = worst
    print(f"worst: excess {ex} at m={m} k={k} stage r={r}; blocks {blk}")
    for j, (tau, a, S0, v) in enumerate(tr):
        print(f"  app {j}: tau={tau} raised={ {b: str(x) for b, x in a.items()} } S0={S0}"
              f" v={ {e: str(x) for e, x in v.items()} }")


if __name__ == "__main__":
    main()
