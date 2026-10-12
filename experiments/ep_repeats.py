"""Phase 2d helper (see docs/phase2d-epoch-2026-10-12.md): repeats.  Run from experiments/."""
import ast, glob, sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_cases2 import classify
shown = 0
def run(d):
    global shown
    M = build(d); _, _, blk, w = d; k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k): return
    v = list(w)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r: continue
        Scur = None; steps = 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if Scur is not None and rho >= 2 and any(e[0] in ("rep", "IV") for e in log) and shown < 12:
                    shown += 1
                    Rn = sorted((v0[x], x) for x in R if not (Bs >> x & 1))
                    Ra = sorted((v0[x], x) for x in R if (Bs >> x & 1))
                    print("raised anchors", Ra, "raised non-anchors", Rn)
                    for e in log: print("   ", e)
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]; rho = len(S) - (k - r)
                v0 = list(v); T = 0; log = []; prev = {}; crossed = {}
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            steps += 1
            if steps > 800: return
            newc = [(x, z) for x in R for z in range(M.m) if z not in R and M.comp[x] == M.comp[z] and v[z] < v[x] and v2[z] >= v2[x] and not (Bs >> x & 1)]
            if rho >= 2 and D_of(M, Bs, set(R), v2) > 0:
                c = classify(M, blk, k, v, r, S, Bs, delta)
                if c[0] == "I":
                    z1 = c[2]; lev = v0[c[1]]
                    tag = "rep" if z1 in prev else "first"
                    log.append((tag, "z1", z1, "level", lev, "prev", prev.get(z1), "g", c[3], "Rnonanch passed", sorted({x for x, z in newc})))
                    prev[z1] = lev
                else:
                    log.append(("IV", "z2", c[1], "g", c[2], "Rnonanch passed", sorted({x for x, z in newc})))
            elif rho >= 2:
                log.append(("last", sorted({x for x, z in newc})))
            v = v2
for f in glob.glob("stage_logs/*.txt"):
    for line in open(f):
        if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
