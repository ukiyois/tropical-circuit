"""Phase 2e: what makes Phi drop (instrumentation of ep2_phi.py on logged epochs).

For every update that is not last, per component K with raised anchors: the gap
occupancy before/after, newly pending gaps, filled pending gaps, elements passing T,
and the change of Phi_K; also whether tau = delta (rigid motion of U).
Usage: python ep2_phi_events.py SPEC [maxprint]
"""
import sys
from collections import Counter

from ep2_common import sources, epoch_states, raised_anchor_values
from ep2_phi import phi


def gaps(rec, v):
    """per component: (positions rho_0..rho_L, occupancy counts N_0..N_{L+1}, lowest gap)"""
    M, R, U = rec["M"], rec["R"], rec["U"]
    out = {}
    for c, s in raised_anchor_values(rec, v).items():
        a, T = s[0], s[-1]
        pos = sorted({v[x] for x in R if M.comp[x] == c and a <= v[x] <= T})
        N = [0] * (len(pos) + 1)
        for z in U:
            if M.comp[z] != c:
                continue
            i = sum(1 for p in pos if p <= v[z])
            N[i] += 1
        out[c] = (pos, N)
    return out


def phiK(pos, N):
    L = len(pos) - 1
    occ = [i for i in range(len(N)) if N[i] > 0]
    if not occ or occ[0] > L:
        return 0
    j = occ[0]
    return N[j] + sum(max(N[i], 1) for i in range(j + 1, L + 1))


def main():
    spec = sys.argv[1]
    maxp = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    cnt = Counter()
    shown = 0
    for d in sources(spec):
        for rec in epoch_states(d, want_delta=True):
            if rec["rho"] < 2:
                continue
            sts = rec["states"]
            n = len(sts) - 1
            for i in range(n - 1):
                v, v2 = sts[i], sts[i + 1]
                rigid = rec["delta"][i] == rec["tau"][i]
                cnt["rigid" if rigid else "nonrigid"] += 1
                g1, g2 = gaps(rec, v), gaps(rec, v2)
                tot = 0
                kinds = []
                for c in g1:
                    pos, N = g1[c]
                    _, N2 = g2[c]
                    L = len(pos) - 1
                    d1, d2 = phiK(pos, N), phiK(pos, N2)
                    tot += d2 - d1
                    low1 = min([i for i in range(len(N)) if N[i]], default=L + 1)
                    low2 = min([i for i in range(len(N2)) if N2[i]], default=L + 1)
                    newpend = [j for j in range(1, L + 1) if N[j] > 0 and N2[j] == 0 and low2 < j]
                    filled = [j for j in range(1, L + 1) if N[j] == 0 and low1 < j and N2[j] > 0]
                    passT = (sum(N[:L + 1]) - sum(N2[:L + 1]))
                    kinds.append((c, d2 - d1, "newpend", newpend, "filled", filled, "passT", passT,
                                  "low", low1, low2, "L", L))
                    if newpend:
                        cnt["newpend_events"] += 1
                    if d2 - d1 > 0:
                        cnt["comp_increase"] += 1
                cnt["dPhi=%d" % tot] += 1
                if (not rigid or any(k[3] for k in kinds)) and shown < maxp:
                    shown += 1
                    print("upd", i + 1, "rigid" if rigid else "NONRIGID", "dPhi", tot, kinds)
    print(dict(cnt))


if __name__ == "__main__":
    main()
