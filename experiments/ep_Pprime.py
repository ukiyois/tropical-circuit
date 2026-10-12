"""Conjecture P': #(non-last updates in which no unraised element passes the top
raised value T_K of its component) <= #{x in R - B* : v^0_x < T^0_{K(x)}}.
P' implies P.  Usage: python ep_Pprime.py "glob" | random count seed"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, D_of
st = {"epochs": 0, "fail": 0, "maxslack": -99, "eq": 0}
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
                if Scur is not None and rho >= 1:
                    st["epochs"] += 1
                    sl = lower - budget
                    st["maxslack"] = max(st["maxslack"], sl); st["eq"] += sl == 0
                    if sl > 0: st["fail"] += 1; print("FAIL", d, r)
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]; U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r)
                tops = {}
                for h in R:
                    if Bs >> h & 1: tops[M.comp[h]] = max(tops.get(M.comp[h], v[h]), v[h])
                topel = {c: next(h for h in R if Bs >> h & 1 and M.comp[h] == c and v[h] == t) for c, t in tops.items()}
                budget = sum(1 for x in R if not (Bs >> x & 1) and M.comp[x] in tops and v[x] < tops[M.comp[x]])
                lower = 0
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            steps += 1
            if steps > 800: return
            if rho >= 1 and D_of(M, Bs, set(R), v2) > 0:
                passes_top = any(M.comp[z] in topel and v[z] < v[topel[M.comp[z]]] and v2[z] >= v2[topel[M.comp[z]]] for z in U)
                if not passes_top: lower += 1
            v = v2
if sys.argv[1] == "random":
    rng = random.Random(int(sys.argv[3]))
    for _ in range(int(sys.argv[2])):
        kind = rng.choice(["graphic", "graphic", "binary"]); n = rng.randint(4, 7); m = rng.randint(n + 2, 13)
        run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])))
else:
    for f in glob.glob(sys.argv[1]):
        for line in open(f):
            if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
print(st)
