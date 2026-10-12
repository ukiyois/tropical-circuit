"""PO-SL applications where neither nu0 rises nor the level-0 avoidable set
grows: print the whole stage, with the level-0 structure before and after,
the PO sets and clusters at tau, and the raised blocks.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import avoid_set
from rainbow_rpim import components
from rainbow_posl import theta_posl, u_posl, po_set
from rainbow_family_stress import uniform_fine, binary_dense, graphic_multi

ZERO = Fraction(0)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 73
    want = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(seed)
    gens = [uniform_fine, binary_dense, graphic_multi,
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g)),
            lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*st.binary5(g))]
    shown = 0
    for i in range(600):
        M, blk, k, w = gens[i % len(gens)](rng)
        comp = components(M)
        p = {b: ZERO for b in range(k)}
        for r in range(k):
            log, bad = [], False
            for _ in range(r + 2):
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                th = theta_posl(M, v, comp)
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                if res is None or all(x == 0 for x in res[0].values()):
                    break
                a, tau = res
                ob0 = rp.optimal_bases(M, v)
                S0 = avoid_set(M, blk, k, ob0, r)
                p = {b: p[b] + a[b] for b in range(k)}
                v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                ob = rp.optimal_bases(M, v2)
                nu2 = max(len({blk[e] for e in B}) for B in ob)
                S2 = avoid_set(M, blk, k, ob, r) if nu2 == r else None
                st_ = "aug" if nu2 > r else ("grow" if S2 > S0 else "NEITHER")
                bad |= st_ == "NEITHER"
                u = u_posl(M, v, tau, comp)
                log.append((v, tau, a, S0, ob0, st_, S2, ob, sorted(po_set(M, v, tau)), u))
            if bad and shown < want:
                shown += 1
                print("=" * 76)
                print(f"m={M.m} k={k} stage r={r} blocks {blk} components {comp}")
                for j, (v, tau, a, S0, ob0, st_, S2, ob, po, u) in enumerate(log):
                    print(f" app {j}: v={ {e: str(x) for e, x in v.items()} }")
                    print(f"   tau={tau}  a={ {b: str(x) for b, x in a.items() if x} }  S0={sorted(S0)} -> {st_}"
                          f" S'={sorted(S2) if S2 is not None else '-'}")
                    print(f"   N0 {[sorted(B) for B in ob0]}")
                    print(f"   N0' {[sorted(B) for B in ob]}")
                    print(f"   PO(tau) {po}  clusters at tau { {e: (str(x) if x < 10**8 else 'inf') for e, x in u.items()} }")
        if shown >= want:
            break


if __name__ == "__main__":
    main()
