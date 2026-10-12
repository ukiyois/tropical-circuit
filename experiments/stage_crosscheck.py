"""Cross-check stage_core.py against the referee implementation (referee_phase2a/core.py)
on random states: nu0, S0, tau, lambda, the update vector a, and stage lengths.
Also reproduces the two long stages of rainbow_posl_longstage.py."""
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import core as ref  # noqa: E402
import stage_core as sc  # noqa: E402


def to_sc(Mref):
    return sc.from_rank_table(Mref.m, Mref.R)


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    checked = mism = 0
    for _ in range(trials):
        kind, Mr = ref.random_matroid(rng)
        k = Mr.k
        if k < 2:
            continue
        blk = ref.rand_blocks(Mr, k, rng)
        if blk is None:
            continue
        M = to_sc(Mr)
        v = ref.rand_values(Mr.m, rng, rng.choice(["ties", "ties5", "spaced", "mixed"]))
        N0, _ = ref.opt_bases(Mr, v)
        A, nu = ref.avoidable(N0, blk, k)
        nu2, S2 = sc.state(M, blk, k, v)
        if (nu, A) != (nu2, S2):
            mism += 1
            print("state mismatch", kind, blk, v, nu, A, nu2, S2)
            continue
        if nu >= k:
            continue
        tau, lam, a, _ = ref.posl_update(Mr, blk, k, v, nu)
        tau2, lam2, a2, _ = sc.update(M, blk, k, v, nu)
        lam_ok = all((lam[b] == lam2[b]) or (lam[b] >= tau and lam2[b] >= tau2) for b in range(k))
        if tau != tau2 or not lam_ok or [a[b] for b in range(k)] != a2:
            mism += 1
            print("update mismatch", kind, blk, v, tau, lam, a, "|", tau2, lam2, a2)
        checked += 1
    print(f"states checked {checked}, mismatches {mism}")
    ex = [([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)], [0, 1, 1, 1, 2, 0], [3, 1, 0, 3, 3, 2]),
          ([(2, 3), (1, 0), (0, 3), (1, 0), (2, 1), (3, 0), (0, 2), (2, 0), (3, 0)],
           [1, 0, 1, 2, 0, 1, 1, 1, 1], [5, 9, 6, 12, 10, 9, 3, 2, 4])]
    for edges, colors, w in ex:
        M = sc.graphic(4, edges)
        lens, v = sc.run_schedule(M, colors, M.k, w)
        print("stage lengths", lens, "Psi", sc.psi_from_v(M, colors, M.k, w, v),
              "Opt", sc.opt_rainbow(M, colors, M.k, w))


if __name__ == "__main__":
    main()
