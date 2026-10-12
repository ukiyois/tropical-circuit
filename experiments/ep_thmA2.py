"""Theorem A' check: for epochs in which all raised anchors of each component share
one value T_K, n <= 1 + #{z in U : K(z) has a raised anchor, v^0_z < T^0_K}.
False variant: n <= #{...} (no +1).  Usage: python ep_thmA2.py "glob" | random count seed"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from ep_common import epochs
st = {"applicable": 0, "rho>=2_applicable": 0, "fail": 0, "false_fail": 0}
def run(d):
    M = build(d); _, _, blk, w = d; k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k): return
    try: eps, _ = epochs(M, blk, k, list(w), cap=800)
    except RuntimeError: return
    for e in eps:
        if e["rho"] < 1: continue
        S = set(e["S"]); v = e["v0"]; Bs = e["B"]
        vals = {}
        for h in range(M.m):
            if blk[h] in S and Bs >> h & 1: vals.setdefault(M.comp[h], set()).add(v[h])
        if any(len(x) > 1 for x in vals.values()): continue
        st["applicable"] += 1
        st["rho>=2_applicable"] += e["rho"] >= 2
        T = {c: next(iter(x)) for c, x in vals.items()}
        cnt = sum(1 for z in range(M.m) if blk[z] not in S and M.comp[z] in T and v[z] < T[M.comp[z]])
        if e["n"] > 1 + cnt: st["fail"] += 1; print("FAIL", d, e["r"])
        if e["n"] > cnt: st["false_fail"] += 1
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
