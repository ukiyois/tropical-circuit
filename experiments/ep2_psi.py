"""Phase 2e, Theorem E.5 and Lemma E.4 (docs/phase2e-epoch-rho2-2026-10-12.md, Sections 2, 3).

Lemma E.4 (scales after a linking): at an update t that is not last, with linking pair
(y, g) and a raised anchor h of C(B*, y) with v_y - delta <= v_h <= v_y,
    sum of delta_i over the updates t < i <= n-2 (not last)  <  v_h - v_g   (at v^t).
False variant L4F: the same with (v_h - v_g)/2 on the right.

Theorem E.5: for a component K with raised anchors, a = least and T = largest
raised-anchor value, W = {z in U cap K : a <= v_z < T},
    Psi_K = #{z in U cap K : v_z < T} + iota_K,
    iota_K = 1 iff W is empty, some z in U cap K has v_z < a, and no earlier update of
             the epoch had its linking pair in K with v_g >= a  (type b),
    Psi_K = #{z in U cap K : v_z < T}                          (type a: one raised value).
Type b: two raised values, (H2) no raised non-anchor of K with value in (a, T),
(H1') no raised non-anchor of K with value a has an unraised element in its circuit.
Checks on every epoch whose components with raised anchors are all of type a or b:
  C1  Psi_K(v') <= Psi_K(v) for every K and every update;
  C2  Psi_K(v') <= Psi_K(v) - 1 at every update that is not last with linking pair in K;
  C3  n <= 1 + sum_K Psi_K(v^0) <= 1 + P1(v^0).
False variants (must fail somewhere): V1 Psi without iota (on type b components);
V3 Psi applied to components violating (H2), counted per epoch.
Usage: python ep2_psi.py SPEC [SPEC ...]
"""
import sys
from collections import Counter
from fractions import Fraction

import stage_core as sc
from ep2_common import sources, epoch_states, P1, raised_anchor_values
from ep2_trace import linking_pairs


def comp_type(rec, v, c):
    M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
    vals = raised_anchor_values(rec, v)[c]
    if len(vals) == 1:
        return "a"
    if len(vals) > 2:
        return "c"
    a, T = vals
    for x in R:
        if M.comp[x] != c or Bs >> x & 1:
            continue
        if a < v[x] < T:
            return "c2"     # violates (H2)
        if v[x] == a and any(f in U for f in sc.bits(M.fund_circuit(Bs, x) & ~(1 << x))):
            return "c1"     # violates (H1')
    return "b"


def psi(rec, v, c, typ, high_seen, variant=None):
    M, U = rec["M"], rec["U"]
    vals = raised_anchor_values(rec, v)[c]
    a, T = vals[0], vals[-1]
    Uc = [v[z] for z in U if M.comp[z] == c]
    p = sum(1 for x in Uc if x < T)
    if typ != "a" and variant != "V1" and not high_seen:
        if not any(a <= x < T for x in Uc) and any(x < a for x in Uc):
            p += 1
    return p


def main():
    cnt = Counter()
    bad = []
    for spec in sys.argv[1:]:
        for d in sources(spec):
            for rec in epoch_states(d):
                if rec["rho"] < 1:
                    continue
                M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
                sts = rec["states"]
                n = len(sts) - 1
                v0 = sts[0]
                dl = rec["delta"]
                # Lemma E.4 on every epoch
                for t in range(n - 1):
                    v = sts[t]
                    lp, _ = linking_pairs(M, Bs, R, v, dl[t])
                    later = sum(dl[t + 1:n - 1])
                    for (y, g) in lp:
                        for h in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
                            if h in R and Bs >> h & 1 and v[y] - dl[t] <= v[h] <= v[y]:
                                cnt["L4_checked"] += 1
                                if not later < v[h] - v[g]:
                                    cnt["L4_FAIL"] += 1
                                    bad.append(("L4", d, rec["r"], t + 1))
                                if not later < Fraction(v[h] - v[g], 2):
                                    cnt["L4F_fail"] += 1
                comps = sorted(raised_anchor_values(rec, v0))
                types = {c: comp_type(rec, v0, c) for c in comps}
                good = all(t in ("a", "b") for t in types.values())
                has_c2 = any(t == "c2" for t in types.values())
                cnt["epochs_ab" if good else ("epochs_c2" if has_c2 else "epochs_other")] += 1
                if good and any(t == "b" for t in types.values()):
                    cnt["epochs_with_b"] += 1
                if not good and not has_c2:
                    continue
                tt = {c: ("b" if t in ("b", "c2") else t) for c, t in types.items()}
                high = {c: False for c in comps}
                v3fail = False
                for i in range(n):
                    v, v2 = sts[i], sts[i + 1]
                    last = i == n - 1
                    lp, _ = linking_pairs(M, Bs, R, v, dl[i]) if not last else ([], None)
                    cl = M.comp[lp[0][1]] if lp else None
                    newhigh = dict(high)
                    if lp:
                        g = lp[0][1]
                        if tt[cl] == "b" and v[g] >= raised_anchor_values(rec, v)[cl][0]:
                            newhigh[cl] = True
                    for c in comps:
                        p1 = psi(rec, v, c, tt[c], high[c])
                        p2 = psi(rec, v2, c, tt[c], newhigh[c])
                        if good and p2 > p1:
                            cnt["C1_FAIL"] += 1
                            bad.append(("C1", d, rec["r"], i + 1))
                        if last or c != cl:
                            continue
                        if p1 - p2 < 1:
                            if types[c] == "c2":
                                v3fail = True
                            else:
                                cnt["C2_FAIL"] += 1
                                bad.append(("C2", d, rec["r"], i + 1))
                        if good:
                            cnt["C2_checked"] += 1
                            if tt[c] == "b":
                                cnt["C2_checked_b"] += 1
                                q1 = psi(rec, v, c, "b", high[c], "V1")
                                q2 = psi(rec, v2, c, "b", newhigh[c], "V1")
                                if q1 - q2 < 1:
                                    cnt["V1_fail_updates"] += 1
                    high = newhigh
                if v3fail:
                    cnt["V3_fail_epochs"] += 1
                if good:
                    s0 = sum(psi(rec, v0, c, types[c], False) for c in comps)
                    if n > 1 + s0:
                        cnt["C3_FAIL"] += 1
                        bad.append(("C3", d, rec["r"]))
                    if s0 > P1(rec, v0):
                        cnt["C3_P1_FAIL"] += 1
                    if n == 1 + s0:
                        cnt["C3_tight"] += 1
    print(dict(sorted(cnt.items())))
    for b in bad[:6]:
        print("FAIL", b)


if __name__ == "__main__":
    main()
