"""Phase 2e: where is the linking raised non-anchor y?  For every update that is not
last (epochs with rho >= 2), every linking D-pair (y, g) at scale delta: the values
of the raised anchors of C(B*, y) within delta below y, compared with the raised-anchor
values of the component (top value T_K or lower), and whether unraised elements lie
strictly between that anchor value and T_K.
Usage: python ep2_linkpos.py SPEC [maxprint]
"""
import sys
from collections import Counter

import stage_core as sc
from ep2_common import sources, epoch_states, raised_anchor_values
from ep2_trace import linking_pairs


def main():
    spec = sys.argv[1]
    maxp = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    cnt = Counter()
    shown = 0
    for d in sources(spec):
        for rec in epoch_states(d, want_delta=True):
            if rec["rho"] < 2:
                continue
            M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
            sts = rec["states"]
            n = len(sts) - 1
            for i in range(n - 1):
                v = sts[i]
                delta = rec["delta"][i]
                vals = raised_anchor_values(rec, v)
                lp, u = linking_pairs(M, Bs, R, v, delta)
                kinds = set()
                for (y, g) in lp:
                    c = M.comp[y]
                    hs = [h for h in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y))
                          if h in R and v[y] - delta <= v[h] <= v[y]]
                    top = vals[c][-1]
                    if any(v[h] == top for h in hs):
                        kinds.add("top")
                    else:
                        hv = max(v[h] for h in hs)
                        mid = [z for z in U if M.comp[z] == c and hv < v[z] < top]
                        kinds.add("low+mid" if mid else "low")
                key = "/".join(sorted(kinds))
                cnt[key] += 1
                if "low+mid" in kinds and shown < maxp:
                    shown += 1
                    print("low+mid", d, "stage", rec["r"], "update", i + 1)
    print(dict(cnt))


if __name__ == "__main__":
    main()
