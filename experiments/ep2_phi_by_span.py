"""Phase 2e: the gap potential Phi (ep2_phi.py) at updates whose linking pairs reach the top
raised value (some linking pair with v_y >= T_K, "Tspan") and at updates whose linking pairs
are all low.  Counts updates and failures of "Phi drops by at least 1", split also by
epochs with three or more raised values in a component.
Usage: python ep2_phi_by_span.py SPEC [SPEC ...]
"""
import sys

from collections import Counter
from ep2_common import sources, epoch_states, raised_anchor_values
from ep2_trace import linking_pairs
from ep2_phi import phi
cnt = Counter()
for spec in sys.argv[1:]:
    for d in sources(spec):
        for rec in epoch_states(d):
            if rec["rho"] < 1: continue
            M, Bs, R = rec["M"], rec["B"], rec["R"]
            sts = rec["states"]; n = len(sts) - 1
            v0 = sts[0]
            vals0 = raised_anchor_values(rec, v0)
            nvals = max(len(s) for s in vals0.values())
            for i in range(n - 1):
                v = sts[i]
                lp, _ = linking_pairs(M, Bs, R, v, rec["delta"][i])
                vals = raised_anchor_values(rec, v)
                span = any(v[y] >= vals[M.comp[y]][-1] for (y, g) in lp)
                ok = phi(rec, v) - phi(rec, sts[i + 1]) >= 1
                key = ("Tspan" if span else "low") + ("_s>=3" if nvals >= 3 else "")
                cnt[key] += 1
                if not ok: cnt[key + "_FAIL"] += 1
print(dict(sorted(cnt.items())))
