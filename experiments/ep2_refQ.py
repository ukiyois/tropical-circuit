"""Phase 2e: independent recomputation (referee_phase2a/core.py only) of the count of
Conjecture Q of B0d on given instances: repeats + case (IV) updates against the raised
non-anchors below the top raised value.  Everything (states, S0, nu, the base B*, the first
event delta, the PO-SL clusters, the linking pair, the cases of Lemma B.1) is computed
with the referee's rank tables and base enumeration; nothing from stage_core is used.
Usage: python ep2_refQ.py          (instances listed below)
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "referee_phase2a"))
import core as ref  # noqa: E402

INSTANCES = {
    "R8 minimized (Q fails by 1, m = 9)":
        ('graphic', (6, [(0, 4), (4, 2), (2, 5), (1, 0), (4, 2), (0, 3), (3, 1), (4, 3), (3, 5)]),
         [2, 4, 4, 1, 3, 1, 1, 1, 0], [2, 5, 8, 5, 5, 3, 6, 1, 8]),
    "R8a (Q fails by 1, search graphic 6/12)":
        ('graphic', (6, [(3, 1), (0, 4), (4, 2), (2, 5), (1, 0), (5, 3), (4, 2), (4, 3), (0, 3), (3, 1), (4, 3),
                         (3, 5)]),
         [3, 2, 4, 4, 1, 4, 3, 2, 1, 1, 1, 0],
         [1281482, 133, 11648, 17729, 10126, 17727, 32915, 4, 3019, 6032, 1, 4212010]),
    "R8b (Q fails by 1, search graphic 6/12)":
        ('graphic', (6, [(1, 3), (3, 4), (5, 2), (1, 4), (5, 0), (0, 4), (2, 0), (5, 1), (2, 0), (3, 4), (2, 0),
                         (5, 2)]),
         [0, 0, 1, 3, 4, 4, 4, 3, 0, 2, 1, 2],
         [479687, 466508, 458311, 679, 173546, 252769, 3835886, 75534, 3630001, 810749, 1917939, 662535]),
}


def elems(x):
    return ref.elems(x)


def run(d):
    kind, data, blk, w = d
    n_v, edges = data
    M = ref.graphic(n_v, edges)
    k, m = M.k, M.m
    v = [Fraction(x) for x in w]
    out = []
    for r in range(1, k):
        cur = None
        while True:
            N0, _ = ref.opt_bases(M, v)
            A, nu = ref.avoidable(N0, blk, k)
            if cur is not None and (nu > r or A != cur):
                out.append(rec)
                cur = None
            if nu > r:
                break
            if cur is None:
                cur = A
                Bs = min(B for B in N0 if len(ref.blocks_of(B, blk)) == r)
                R = [e for e in range(m) if blk[e] in A]
                U = [e for e in range(m) if blk[e] not in A]
                rho = len(A) - (k - r)
                tops = {}
                for h in R:
                    if Bs >> h & 1:
                        tops[M.comp[h]] = max(tops.get(M.comp[h], v[h]), v[h])
                budget = sum(1 for x in R if not (Bs >> x & 1) and M.comp[x] in tops and v[x] < tops[M.comp[x]])
                rec = {"r": r, "rho": rho, "n": 0, "budget": budget, "log": [], "B": sorted(elems(Bs))}
                seen = set()
            # first event delta
            delta = None
            for t in ref.breakpoints(v, m):
                At, nut = ref.avoidable(ref.N_posl(M, v, t), blk, k)
                if nut > r or At != A:
                    delta = t
                    break
            tau, lam, a, _ = ref.posl_update(M, blk, k, v, r)
            v2 = [v[e] - a[blk[e]] for e in range(m)]
            rec["n"] += 1
            N1, _ = ref.opt_bases(M, v2)
            A1, nu1 = ref.avoidable(N1, blk, k)
            if nu1 == r and A1 == A:          # not the last update of the epoch
                u, _ = ref.u_posl(M, v, delta)
                pair = None
                for y in sorted(R, key=lambda e: (v[e], e)):
                    if Bs >> y & 1 or u[y] == ref.INF:
                        continue
                    for g in elems(Bs):
                        if g in R or u[g] != u[y] or M.comp[g] != M.comp[y]:
                            continue
                        if M.R[(Bs & ~(1 << g)) | (1 << y)] == k and v[g] < v[y]:
                            pair = (y, g)
                            break
                    if pair:
                        break
                y, g = pair
                C = [e for e in range(m) if u[e] == u[y] and M.comp[e] == M.comp[y]]
                z2 = min((e for e in C if e in R and v[e] > v[g]), key=lambda e: (v[e], -(Bs >> e & 1), e))
                z1 = max((e for e in C if e in U and v[e] < v[z2]), key=lambda e: (v[e], -e))
                if any(h in R and Bs >> h & 1 and v[h] == v[z2] for h in C):
                    tag = "rep" if z1 in seen else "first"
                    seen.add(z1)
                    rec["log"].append(("I", tag, "z1", z1, "level", v[z2] + 0))
                else:
                    rec["log"].append(("IV", "z2", z2, "g", g))
            v = v2
    return out


def main():
    for name, d in INSTANCES.items():
        print(name)
        for rec in run(d):
            if rec["rho"] < 2:
                continue
            reps = sum(1 for e in rec["log"] if e[0] == "I" and e[1] == "rep")
            ivs = sum(1 for e in rec["log"] if e[0] == "IV")
            print("   stage", rec["r"], "rho", rec["rho"], "n", rec["n"], "B*", rec["B"],
                  "repeats", reps, "IV", ivs, "budget", rec["budget"],
                  "Q slack", reps + ivs - rec["budget"])
            for e in rec["log"]:
                print("      ", e)


if __name__ == "__main__":
    main()
