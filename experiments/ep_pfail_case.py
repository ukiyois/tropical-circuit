"""Phase 2d helper (see docs/phase2d-epoch-2026-10-12.md): pfail_case.  Run from experiments/."""
import ast, glob, random, sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_potential import tops, potential
from ep_cases2 import classify
cases = {}
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
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]; U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r); crossed = set()
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            steps += 1
            if steps > 800: return
            if rho >= 1:
                Tb = tops(M, Bs, R, v, 1); Ta = tops(M, Bs, R, v2, 1)
                b = potential(M, Bs, R, U, v, Tb, crossed, 1)
                nc = set(crossed)
                for x in R:
                    for z in U:
                        if M.comp[x] == M.comp[z] and v[z] < v[x] and v2[z] >= v2[x]: nc.add(x)
                af = potential(M, Bs, R, U, v2, Ta, nc, 1)
                if D_of(M, Bs, set(R), v2) > 0 and not af < b:
                    c = classify(M, blk, k, v, r, S, Bs, delta)[0]
                    cases[c] = cases.get(c, 0) + 1
                crossed = nc
            v = v2
for f in glob.glob("stage_logs/*.txt") + glob.glob("ep_logs/*.txt"):
    for line in open(f):
        if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
rng = random.Random(3)
for _ in range(400):
    kind = rng.choice(["graphic", "graphic", "binary"]); n = rng.randint(4, 7); m = rng.randint(n + 2, 13)
    run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])))
print("cases of P1 failures:", cases)
