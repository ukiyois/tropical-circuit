"""Phase 2e, Lemma E.3 (repeat anchor): if z is the designated element z1 of case (I) updates
i < j with levels l_i < l_j (values of the raised anchors passed, read at the state of update
j), then at update j the linking anchor g satisfies l_i <= v_g <= v_z, and l_j is the least
raised-anchor value of K(z) above v_g.
False variants: F1 v_z - v_g <= delta at update j (designee within delta of the anchor);
F2 v_g >= l_j - delta at update j.
Usage: python ep2_repeat_anchor.py SPEC [SPEC ...]
"""
import sys
from collections import Counter

from ep2_common import sources, epoch_states, raised_anchor_values
from ep_cases2 import classify


def main():
    cnt = Counter()
    for spec in sys.argv[1:]:
        for d in sources(spec):
            for rec in epoch_states(d):
                if rec["rho"] < 2:
                    continue
                M, Bs = rec["M"], rec["B"]
                sts = rec["states"]
                n = len(sts) - 1
                hist = {}
                for t in range(n - 1):
                    v = sts[t]
                    c = classify(M, rec["blk"], rec["k"], v, rec["r"], rec["S"], Bs, rec["delta"][t])
                    if c[0] != "I":
                        continue
                    h, z, g = c[1], c[2], c[3]
                    if z in hist:
                        for (hi, gi) in hist[z]:
                            cnt["pairs"] += 1
                            li, lj = v[hi], v[h]
                            vals = [x for x in raised_anchor_values(rec, v)[M.comp[z]] if x > v[g]]
                            ok = li < lj and li <= v[g] <= v[z] and vals and min(vals) == lj
                            if not ok:
                                cnt["FAIL"] += 1
                                print("FAIL", d, rec["r"], t + 1)
                            dl = rec["delta"][t]
                            if not v[z] - v[g] <= dl:
                                cnt["F1_fail"] += 1
                            if not v[g] >= lj - dl:
                                cnt["F2_fail"] += 1
                    hist.setdefault(z, []).append((h, g))
    print(dict(cnt))


if __name__ == "__main__":
    main()
