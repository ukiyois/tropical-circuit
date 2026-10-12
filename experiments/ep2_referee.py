"""Phase 2e: cross-check of the instances cited in docs/phase2e-epoch-rho2-2026-10-12.md
with the independent referee implementation (referee_phase2a/core.py: rank tables,
base enumeration, posl_update by a scan of all breakpoints).

For each instance the whole schedule from p = 0 is run by both implementations; the
sequences of states v (exact Fractions), the epoch decomposition (stage r, S0, number of
updates) and the stage lengths must agree exactly.  The potentials of the note are then
evaluated on the referee's states (by ep2_phi / ep2_psi code) and printed.
Usage: python ep2_referee.py
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import core as ref  # noqa: E402
import stage_core as sc  # noqa: E402
from stage_search import build  # noqa: E402
from ep_referee import ref_matroid  # noqa: E402
from ep2_common import epoch_states, P1  # noqa: E402
from ep2_phi import phi  # noqa: E402

INSTANCES = {
    "R6a/R7 (low linking, Phi constant at update 1)":
        ('graphic', (5, [(0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 2), (0, 4), (1, 2), (3, 4), (3, 4)]),
         [0, 1, 2, 0, 3, 3, 3, 1, 3, 0, 0], [0, 10, 100, 0, 10, 100, 11, 1000, 50, 45, 60]),
    "R6b (halving ladder of B0 plus a top anchor, L = 4)":
        ('graphic', (5, [(3, 0), (2, 0), (1, 0), (1, 0), (2, 1), (2, 0), (2, 0), (2, 0), (2, 0), (1, 4), (1, 4),
                         (4, 2)]),
         [1, 1, 0, 2, 0, 1, 1, 1, 1, 3, 2, 1], [0, 0, 16, 16, 17, 8, 4, 2, 1, 64, 64, 1600]),
    "R9 (Phi constant at a top-linking update, one gate)":
        ('graphic', (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (0, 1), (1, 3), (2, 3), (0, 1), (4, 1),
                         (0, 2)]),
         [1, 2, 0, 0, 3, 3, 2, 1, 0, 0, 3, 2], [100, 200, 96, 40, 100, 200, 104, 210, 102, 150, 1000, 5000]),
    "R8 minimized (Q fails by 1, m = 9)":
        ('graphic', (6, [(0, 4), (4, 2), (2, 5), (1, 0), (4, 2), (0, 3), (3, 1), (4, 3), (3, 5)]),
         [2, 4, 4, 1, 3, 1, 1, 1, 0], [2, 5, 8, 5, 5, 3, 6, 1, 8]),
    "R8a (counterexample to Q)":
        ('graphic', (6, [(3, 1), (0, 4), (4, 2), (2, 5), (1, 0), (5, 3), (4, 2), (4, 3), (0, 3), (3, 1), (4, 3),
                         (3, 5)]),
         [3, 2, 4, 4, 1, 4, 3, 2, 1, 1, 1, 0],
         [1281482, 133, 11648, 17729, 10126, 17727, 32915, 4, 3019, 6032, 1, 4212010]),
    "R8b (counterexample to Q)":
        ('graphic', (6, [(1, 3), (3, 4), (5, 2), (1, 4), (5, 0), (0, 4), (2, 0), (5, 1), (2, 0), (3, 4), (2, 0),
                         (5, 2)]),
         [0, 0, 1, 3, 4, 4, 4, 3, 0, 2, 1, 2],
         [479687, 466508, 458311, 679, 173546, 252769, 3835886, 75534, 3630001, 810749, 1917939, 662535]),
    "Theorem E.5 example (B0d R4 instance, hypotheses (H1'), (H2) hold)":
        ('graphic', (5, [(1, 3), (4, 3), (4, 0), (3, 4), (1, 0), (1, 3), (2, 4), (4, 2), (2, 3), (1, 0)]),
         [3, 1, 0, 1, 0, 2, 1, 1, 1, 3],
         [57302, 365, 210758, 9121, 210695, 256960, 14357, 3887, 489, 60190]),
}


def ref_run(Mr, blk, k, w, cap=300):
    v = [Fraction(x) for x in w]
    states, epochs = [list(v)], []
    for r in range(1, k):
        cur, n = None, 0
        while True:
            N0, _ = ref.opt_bases(Mr, v)
            A, nu = ref.avoidable(N0, blk, k)
            if nu > r or A != cur:
                if cur is not None:
                    epochs.append((r, sorted(cur), n))
                if nu > r:
                    break
                cur, n = A, 0
            tau, lam, a, _ = ref.posl_update(Mr, blk, k, v, r)
            v = [v[e] - a[blk[e]] for e in range(Mr.m)]
            states.append(list(v))
            n += 1
            if len(states) > cap:
                raise RuntimeError("cap")
    return states, epochs


def mine_run(d):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    v = list(w)
    states, epochs = [list(v)], []
    for r in range(1, k):
        cur, n = None, 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != cur:
                if cur is not None:
                    epochs.append((r, sorted(cur), n))
                if nu > r:
                    break
                cur, n = S, 0
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v = sc.shift(v, blk, a)
            states.append(list(v))
            n += 1
    return states, epochs


def main():
    bad = 0
    for name, d in INSTANCES.items():
        _, _, blk, w = d
        Mr = ref_matroid(d)
        k = Mr.k
        st_ref, ep_ref = ref_run(Mr, blk, k, w)
        st_mine, ep_mine = mine_run(d)
        same = ep_ref == ep_mine and len(st_ref) == len(st_mine) and all(
            [Fraction(x) for x in a] == b for a, b in zip(st_mine, st_ref))
        bad += not same
        print(("OK  " if same else "DIFF"), name)
        print("    epochs (r, S0, n):", ep_mine)
        for rec in epoch_states(d):
            if rec["rho"] >= 2:
                sts = rec["states"]
                n = len(sts) - 1
                print("    rho", rec["rho"], "stage", rec["r"], "n", n, "P1", P1(rec, sts[0]),
                      "Phi on the states of the epoch", [phi(rec, v) for v in sts[:n]])
    print("mismatches:", bad)


if __name__ == "__main__":
    main()
