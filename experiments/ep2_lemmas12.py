"""Phase 2e, checks of Lemma E.1 (first event = first linking) and Lemma E.2 (conveyor).

E.1: at every update of every epoch with rho >= 1, delta (first_event) equals the least level t
     at which some D-pair (y, g) has y in PO_t and u_t(g) = u_t(y).
     False variant E1F: the least level at which some D-pair has y in PO_t (cluster condition
     dropped).
E.2: at every update, for every cluster C at scale delta of a component, every unraised z of
     that component with min_C <= v_z < max_C crosses every raised x with v_z < v_x <= c+
     (c+ = least value of C above v_z).
     False variant E2F: the same up to the second value of C above v_z.
Usage: python ep2_lemmas12.py SPEC [SPEC ...]
"""
import sys
from collections import Counter

import stage_core as sc
from ep2_common import sources, epoch_states


def first_linking(M, Bs, R, v, levels, need_cluster=True):
    for t in levels:
        u = sc.posl_u(M, v, t)
        for y in R:
            if Bs >> y & 1 or u[y] > M.m:
                continue
            for g in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
                if g in R:
                    continue
                if not need_cluster or u[g] == u[y]:
                    return t
    return None


def main():
    cnt = Counter()
    for spec in sys.argv[1:]:
        for d in sources(spec):
            for rec in epoch_states(d):
                if rec["rho"] < 1:
                    continue
                M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
                sts = rec["states"]
                n = len(sts) - 1
                for i in range(n):
                    v, v2 = sts[i], sts[i + 1]
                    delta = rec["delta"][i]
                    levels = sc.levels_of(v)
                    cnt["E1_updates"] += 1
                    if first_linking(M, Bs, R, v, levels) != delta:
                        cnt["E1_FAIL"] += 1
                    if first_linking(M, Bs, R, v, levels, need_cluster=False) != delta:
                        cnt["E1F_fail"] += 1
                    u = sc.posl_u(M, v, delta)
                    clusters = {}
                    for e in range(M.m):
                        if u[e] <= M.m:
                            clusters.setdefault((M.comp[e], u[e]), []).append(e)
                    bad = badF = False
                    for (c, lab), C in clusters.items():
                        vals = sorted({v[e] for e in C})
                        for z in U:
                            if M.comp[z] != c or not (vals[0] <= v[z] < vals[-1]):
                                continue
                            above = [x for x in vals if x > v[z]]
                            cplus = above[0]
                            cplus2 = above[1] if len(above) > 1 else above[0]
                            for x in R:
                                if M.comp[x] != c or not v[z] < v[x]:
                                    continue
                                crossed = v2[x] <= v2[z]
                                if v[x] <= cplus:
                                    cnt["E2_pairs"] += 1
                                    if not crossed:
                                        bad = True
                                if v[x] <= cplus2 and not crossed:
                                    badF = True
                    cnt["E2_FAIL"] += bad
                    cnt["E2F_fail_updates"] += badF
    print(dict(sorted(cnt.items())))


if __name__ == "__main__":
    main()
