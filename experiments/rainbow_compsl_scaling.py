"""Fixed combinatorial structure, finer and finer offsets: do stages get longer?

w_e = base_e + h * j_e with base_e a random integer in [0, 6] and j_e a random
integer in [0, 3].  For each random instance the number of applications of the
component-wise single-linkage update is measured at h = 1/4, 1/16, 1/64, 1/256.
Growth as h shrinks, with m fixed, means the update is only pseudo-polynomial.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_compsl_ladder import count_apps


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 67
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    hs = [Fraction(1, 4), Fraction(1, 16), Fraction(1, 64), Fraction(1, 256)]
    growth = []
    for i in range(trials):
        gen = [st.uniform, rp.rainbow_tree, rp.binary_rainbow, st.binary5][i % 4]
        M, blk, k = gen(rng)
        base = {e: rng.randint(0, 6) for e in range(M.m)}
        off = {e: rng.randint(0, 3) for e in range(M.m)}
        counts = []
        for h in hs:
            w = {e: Fraction(base[e]) + h * off[e] for e in range(M.m)}
            apps, ok = count_apps(M, blk, k, w, "comp-SL", cap=300)
            assert ok
            counts.append(apps)
        growth.append(counts)
        if counts[-1] > counts[0] + 2:
            print("growing:", counts, "m =", M.m, "k =", k, flush=True)
    print("max apps at each h:", [max(c[j] for c in growth) for j in range(len(hs))])
    print("instances whose count rises from h=1/4 to h=1/256:",
          sum(1 for c in growth if c[-1] > c[0]), "of", len(growth))


if __name__ == "__main__":
    main()
