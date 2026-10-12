"""Theorem A, sharp form: for rho = 1 epochs, n <= m - 2, and if |R| = 2 then
n <= #{z in U cap K(h): v_z < v_h}.  False variant (to show discrimination):
n <= m - 3.  Usage: python ep_sharpA.py "glob" | random count seed"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from ep_common import epochs
st = {"rho1": 0, "R2": 0, "fail_m2": 0, "fail_R2": 0, "false_m3": 0}
def run(d):
    M = build(d); _, _, blk, w = d; k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k): return
    try: eps, _ = epochs(M, blk, k, list(w), cap=800)
    except RuntimeError: return
    for e in eps:
        if e["rho"] != 1: continue
        st["rho1"] += 1
        if e["n"] > M.m - 2: st["fail_m2"] += 1; print("FAIL m-2", d, e["r"])
        if e["n"] > M.m - 3: st["false_m3"] += 1
        if e["R"] == 2:
            st["R2"] += 1
            S = set(e["S"]); v = e["v0"]; Bs = e["B"]
            h = next(x for x in range(M.m) if blk[x] in S and Bs >> x & 1)
            below = sum(1 for z in range(M.m) if blk[z] not in S and M.comp[z] == M.comp[h] and v[z] < v[h])
            if e["n"] > below: st["fail_R2"] += 1; print("FAIL R2", d, e["r"])
if sys.argv[1] == "random":
    rng = random.Random(int(sys.argv[3]))
    for _ in range(int(sys.argv[2])):
        kind = rng.choice(["graphic", "graphic", "binary"]); n = rng.randint(3, 7); m = rng.randint(n + 2, 13)
        run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])))
else:
    for f in glob.glob(sys.argv[1]):
        for line in open(f):
            if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
print(st)
