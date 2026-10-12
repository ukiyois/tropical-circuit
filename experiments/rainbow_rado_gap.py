"""Does the possibly-optimal family obey a Rado-type min-max?

For Bt = { B : theta(B) <= t } put
  nu(t)       = max_{B in Bt} |blk(B)|
  rado(t)     = min_S ( rho_t(E_S) + k - |S| ),  rho_t(A) = max_{B in Bt} |B cap A|.
nu(t) <= rado(t) always.  For a matroid family the two are equal (Rado).
Reported: how often nu(t) < rado(t), over all levels t ("unguarded"), and at
states reached by the local schedule ("guarded").
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map

ZERO = Fraction(0)


def gap_at(M, blk, k, th, t):
    fam = [B for B in M.bases if th[B] <= t]
    nu = max(len({blk[e] for e in B}) for B in fam)
    best = None
    for s in range(k + 1):
        for S in itertools.combinations(range(k), s):
            ES = {e for e in range(M.m) if blk[e] in S}
            val = max(len(B & ES) for B in fam) + k - s
            best = val if best is None or val < best else best
    return nu, best


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 29
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    fams = [("uniform", st.uniform), ("arborescence", rp.arborescence), ("rainbow tree", rp.rainbow_tree),
            ("binary", rp.binary_rainbow), ("binary5", st.binary5), ("rainbow tree6", st.rainbow_tree6)]
    for name, fam in fams:
        un_n = un_gap = g_n = g_gap = 0
        example = None
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            th = theta_map(M, w)
            for t in sorted(set(th.values())):
                nu, rado = gap_at(M, blk, k, th, t)
                un_n += 1
                if nu < rado:
                    un_gap += 1
                    if example is None:
                        example = (k, dict(blk), {e: str(x) for e, x in w.items()}, str(t), nu, rado)
            p = {b: ZERO for b in range(k)}
            for r in range(k):
                for _ in range(r + 1):
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    thv = theta_map(M, v)
                    res = update([(thv[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
                    if res is None:
                        break
                    a, tau = res
                    for t in sorted(set(thv.values())):
                        if t > tau:
                            break
                        nu, rado = gap_at(M, blk, k, thv, t)
                        g_n += 1
                        g_gap += (nu < rado)
                    p = {b: p[b] + a[b] for b in range(k)}
        print(f"{name:13s} unguarded gaps {un_gap}/{un_n}   guarded gaps {g_gap}/{g_n}   example {example}",
              flush=True)


if __name__ == "__main__":
    main()
