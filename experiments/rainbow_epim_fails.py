"""Inspect the applications of the computable family where the strict progress
dichotomy fails (nu0 unchanged, level-0 avoidable set not strictly larger).
For each such application print the state, the update, and what changed, and
follow the stage to its end.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map, avoid_set
from rainbow_rpim import components, exchange_pairs, theta_rpim

ZERO = Fraction(0)


def blocks_of(blk, B):
    return sorted({blk[e] for e in B})


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 47
    want = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(seed)
    shown = 0
    fams = [rp.bipartite, st.uniform, rp.arborescence, rp.rainbow_tree, rp.binary_rainbow, st.binary5]
    for trial in range(400):
        fam = fams[trial % len(fams)]
        M, blk, k = fam(rng)
        w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
        comp = components(M)
        pairs = {B: exchange_pairs(M, B) for B in M.bases}
        p = {b: ZERO for b in range(k)}
        for r in range(k):
            log = []
            failed = False
            for _ in range(3 * k + 3):
                v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                loc = theta_map(M, v)
                th = theta_rpim(M, v, comp, loc, pairs, "element")
                res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                if res is None or all(x == 0 for x in res[0].values()):
                    break
                a, tau = res
                opt0 = [B for B in M.bases if th[B] == 0]
                S0 = avoid_set(M, blk, k, opt0, r)
                p = {b: p[b] + a[b] for b in range(k)}
                v2 = {e: w[e] - p[blk[e]] for e in range(M.m)}
                opt2 = rp.optimal_bases(M, v2)
                nu2 = max(len(blocks_of(blk, B)) for B in opt2)
                S2 = avoid_set(M, blk, k, opt2, r) if nu2 == r else None
                status = "aug" if nu2 > r else ("grow" if S2 > S0 else "FAIL")
                failed |= status == "FAIL"
                log.append((v, tau, a, S0, opt0, status, S2, opt2))
            if failed and shown < want:
                shown += 1
                print("=" * 72)
                print(f"k={k} m={M.m} stage r={r} blocks {blk}")
                for i, (v, tau, a, S0, opt0, status, S2, opt2) in enumerate(log):
                    print(f" app {i}: v={ {e: str(x) for e, x in v.items()} }")
                    print(f"   N0 bases {[sorted(B) for B in opt0]}  S0={sorted(S0)}  tau={tau}"
                          f"  a={ {b: str(x) for b, x in a.items()} }  -> {status}"
                          f"  S'={sorted(S2) if S2 is not None else '-'}"
                          f"  N0' bases {[sorted(B) for B in opt2]}")
        if shown >= want:
            break


if __name__ == "__main__":
    main()
