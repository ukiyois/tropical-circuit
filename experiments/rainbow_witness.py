"""How far are the witnesses of tau and lam_b from the optimal bases?

At every application of the local update, take the witnesses
  tau  : bases with theta(B) = tau meeting r+1 blocks,
  lam_b: bases with theta(B) = lam_b meeting r blocks other than b (lam_b < tau),
and record min |B - B0| over witnesses B and optimal bases B0.
Distance 1 everywhere would mean single exchanges from N0 suffice.
"""
import random
import sys
from collections import Counter
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map

ZERO = Fraction(0)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 19
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("uniform", st.uniform), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow), ("binary5", st.binary5),
            ("rainbow tree6", st.rainbow_tree6)]
    for name, fam in fams:
        dtau, dlam = Counter(), Counter()
        for _ in range(trials):
            M, blk, k = fam(rng)
            w = st.weights(rng, M.m, rng.choice(["generic", "ties"]))
            p = {b: ZERO for b in range(k)}
            for r in range(k):
                for _ in range(r + 1):
                    v = {e: w[e] - p[blk[e]] for e in range(M.m)}
                    th = theta_map(M, v)
                    entries = [(th[B], frozenset(blk[e] for e in B)) for B in M.bases]
                    res = update(entries, k, r)
                    if res is None:
                        break
                    a, tau = res
                    N0 = [B for B in M.bases if th[B] == 0]
                    wit = [B for B in M.bases if th[B] == tau and len({blk[e] for e in B}) >= r + 1]
                    dtau[min(len(B - B0) for B in wit for B0 in N0)] += 1
                    for b in range(k):
                        c = [th[B] for B in M.bases if len({blk[e] for e in B} - {b}) >= r]
                        if not c:
                            continue
                        lam = min(c)
                        if 0 < lam < tau:
                            wl = [B for B in M.bases if th[B] == lam
                                  and len({blk[e] for e in B} - {b}) >= r]
                            dlam[min(len(B - B0) for B in wl for B0 in N0)] += 1
                    p = {b: p[b] + a[b] for b in range(k)}
        print(f"{name:13s} tau-witness distance {dict(sorted(dtau.items()))}   "
              f"lam-witness distance {dict(sorted(dlam.items()))}", flush=True)


if __name__ == "__main__":
    main()
