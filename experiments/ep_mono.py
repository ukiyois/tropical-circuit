"""Phase 2d helper (see docs/phase2d-epoch-2026-10-12.md): mono.  Run from experiments/."""
import ast, glob, random, sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_cases2 import classify
st = {"epochs": 0, "nonmono": 0, "iv_repeat": 0, "iv": 0}
def run(d):
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
                if Scur is not None and rho >= 2:
                    st["epochs"] += 1
                    if any(seq[i] > seq[i+1] for i in range(len(seq)-1)): st["nonmono"] += 1
                    st["iv_repeat"] += len(ivs) - len(set(ivs)); st["iv"] += len(ivs)
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]; rho = len(S) - (k - r)
                v0 = list(v); seq = []; ivs = []
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            steps += 1
            if steps > 800: return
            if rho >= 2 and D_of(M, Bs, set(R), v2) > 0:
                c = classify(M, blk, k, v, r, S, Bs, delta)
                if c[0] == "I": seq.append(v0[c[1]])
                else:
                    g = c[2]
                    h2s = [b for b in c[3] if b in R and v[b] <= v[g]]
                    seq.append(min(v0[b] for b in h2s) if h2s else -1); ivs.append(c[1])
            v = v2
for f in glob.glob("stage_logs/*.txt") + glob.glob("ep_logs/search_*.txt"):
    for line in open(f):
        if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
rng = random.Random(9)
for _ in range(400):
    kind = rng.choice(["graphic", "graphic", "binary"]); n = rng.randint(5, 7); m = rng.randint(n + 2, 13)
    run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])))
print(st)
