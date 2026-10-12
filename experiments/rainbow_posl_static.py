"""End-to-end check of Corollary 9 with the PO-SL update.

Static schedule semantics: stage r applies U_r a fixed number of times; an
application at a state with nu0 > r must be the identity.  Simulated by
running each stage until the update vanishes and then applying it once more.
Checked at every application: nu0 never drops (Theorem 6, item 2), the
avoidable set never shrinks while nu0 = r (Theorem 8, item 1), the stage length
stays within (r+1)(floor(m^2/4)+1) (Theorem 8), and the final value is Opt.
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


def nu0(M, blk, v):
    return max(len({blk[e] for e in B}) for B in rp.optimal_bases(M, v))


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 89
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    rng = random.Random(seed)
    gens = [uniform_fine, binary_dense, graphic_multi,
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*st.binary5(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*st.arborescence6(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*rp.bipartite(g))]
    bad = {"opt": 0, "nu_drop": 0, "S_shrink": 0, "over_bound": 0, "not_identity": 0}
    longest = 0
    for i in range(trials):
        M, blk, k, w = gens[i % len(gens)](rng)
        comp = components(M)
        p = {b: ZERO for b in range(k)}
        for r in range(k):
            bound = (r + 1) * (M.m * M.m // 4 + 1)
            used = 0
            while True:
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                n_before = nu0(M, blk, v)
                th = theta_posl(M, v, comp)
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                a = res[0] if res is not None else {b: ZERO for b in range(k)}
                if all(x == 0 for x in a.values()):
                    break
                S_before = avoid_set(M, blk, k, rp.optimal_bases(M, v), r) if n_before == r else None
                p = {b: p[b] + a[b] for b in range(k)}
                used += 1
                v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                n_after = nu0(M, blk, v2)
                bad["nu_drop"] += (n_after < n_before)
                if S_before is not None and n_after == r:
                    bad["S_shrink"] += not (avoid_set(M, blk, k, rp.optimal_bases(M, v2), r) >= S_before)
            bad["over_bound"] += (used > bound)
            longest = max(longest, used - (r + 1))
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            if nu0(M, blk, v) > r:
                th = theta_posl(M, v, comp)
                ent = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
                tau = min(x for x, S in ent if len(S) >= r + 1)
                bad["not_identity"] += (tau != 0)
        bad["opt"] += (rp.psi(M, blk, w, p) != rp.opt(M, blk, k, w))
    print("violations:", bad, " max(stage length - (r+1)):", longest, " runs:", trials)


if __name__ == "__main__":
    main()
