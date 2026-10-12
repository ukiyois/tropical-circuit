"""Phase 2e: which epochs with rho >= 2 are covered by Theorem E.5, and Conjecture P on each group.

Groups (ep2_psi.comp_type of the components with raised anchors, at the first state):
  covered      all components of type a or b;
  3+values     some component with three or more raised-anchor values;
  gate         some component violating (H2) (a raised element strictly between a_K and T_K);
  lowtwin      otherwise (some component violating only (H1')).
Per group: number of epochs, number with n = 1 + P1(v^0), largest n - 1 - P1(v^0), and the
number of epochs with a component of type b.
Usage: python ep2_coverage.py SPEC [SPEC ...]
"""
import sys
from collections import Counter

from ep2_common import sources, epoch_states, raised_anchor_values, P1
from ep2_psi import comp_type


def main():
    cnt = Counter()
    worst = {}
    for spec in sys.argv[1:]:
        for d in sources(spec):
            for rec in epoch_states(d, want_delta=False):
                if rec["rho"] < 2:
                    continue
                v0 = rec["states"][0]
                ts = [comp_type(rec, v0, c) for c in raised_anchor_values(rec, v0)]
                n = len(rec["states"]) - 1
                if all(t in ("a", "b") for t in ts):
                    key = "covered"
                    cnt["covered_with_b"] += "b" in ts
                elif "c" in ts:
                    key = "3+values"
                elif "c2" in ts:
                    key = "gate"
                else:
                    key = "lowtwin"
                cnt[key] += 1
                cnt[key + "_tight"] += n == 1 + P1(rec, v0)
                worst[key] = max(worst.get(key, -99), n - 1 - P1(rec, v0))
    print(dict(sorted(cnt.items())))
    print("largest n - 1 - P1 per group:", worst)


if __name__ == "__main__":
    main()
