"""Phase 2d helper (see docs/phase2d-epoch-2026-10-12.md): twins.  Run from experiments/."""
import ast, glob, sys

import stage_core as sc
from stage_search import build, has_rainbow
from ep_common import epochs
tot = {"raised": 0, "twin": 0, "eps": 0}
ex = []
for f in glob.glob("stage_logs/*.txt") + glob.glob("ep_logs/search_*.txt"):
    for line in open(f):
        if "desc" not in line: continue
        d = ast.literal_eval(line[line.index("desc ") + 5:].strip())
        M = build(d); _, _, blk, w = d; k = M.k
        if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k): continue
        try: eps, _ = epochs(M, blk, k, list(w), cap=800)
        except RuntimeError: continue
        for e in eps:
            if e["rho"] == 0: continue
            tot["eps"] += 1
            Bs = e["B"]; S = set(e["S"]); v = e["v0"]
            for h in range(M.m):
                if blk[h] in S and Bs >> h & 1:
                    tot["raised"] += 1
                    tw = [x for x in range(M.m) if blk[x] in S and not Bs >> x & 1 and v[x] == v[h] and (M.fund_circuit(Bs, x) >> h & 1)]
                    if tw: tot["twin"] += 1
                    elif len(ex) < 3: ex.append((d, e["r"], h))
print(tot); print(ex)
