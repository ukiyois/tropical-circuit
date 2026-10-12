"""Conjecture P for every choice of B*: n <= 1 + min over minimum bases B* of v^0
meeting r blocks of P1(B*).  Usage: python ep_P1_allB.py "glob" """
import ast, glob, sys
import stage_core as sc
from stage_search import build, has_rainbow
from ep_common import epochs

def P1(M, blk, S, v, Bs):
    top = {}
    for h in range(M.m):
        if blk[h] in S and Bs >> h & 1:
            top[M.comp[h]] = max(top.get(M.comp[h], v[h]), v[h])
    return sum(1 for e in range(M.m) if not (blk[e] in S and Bs >> e & 1) and M.comp[e] in top and v[e] < top[M.comp[e]])

st = {"epochs": 0, "fail": 0, "maxslack": -99, "multiB": 0}
for f in glob.glob(sys.argv[1]):
    for line in open(f):
        if "desc" not in line: continue
        d = ast.literal_eval(line[line.index("desc ") + 5:].strip())
        M = build(d); _, _, blk, w = d; k = M.k
        if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k): continue
        try: eps, _ = epochs(M, blk, k, list(w), cap=800)
        except RuntimeError: continue
        bases = sc.all_bases(M)
        for e in eps:
            if e["rho"] < 1: continue
            v = e["v0"]; S = set(e["S"])
            b0 = min(sum(v[x] for x in sc.bits(B)) for B in bases)
            cands = [B for B in bases if sum(v[x] for x in sc.bits(B)) == b0 and len({blk[x] for x in sc.bits(B)}) == e["r"]]
            vals = [P1(M, blk, S, v, B) for B in cands]
            st["epochs"] += 1
            st["multiB"] += len(set(vals)) > 1
            sl = e["n"] - 1 - min(vals)
            st["maxslack"] = max(st["maxslack"], sl)
            if sl > 0:
                st["fail"] += 1; print("FAIL", d, e["r"], e["n"], vals)
print(st)
