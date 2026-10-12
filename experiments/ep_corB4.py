"""Corollary B.4 check: for every epoch with rho >= 1,
  n <= 1 + sum_{z in U} #{distinct raised-anchor values of K(z) above v^0_z} + (2q - 2) rho (k - rho),
q = max over components of the number of distinct values of B* (first state, upper bound k).
Also counts the case (I) and case (IV) updates separately against their bounds:
  #I <= sum_z #{raised values above z}   (injective (element, value) passages)
  #IV <= (2q - 2) * #{(g, h2) pairs}.
False variant (rho = 1 bound for every rho): #I <= |U|.
Usage: python ep_corB4.py "glob" | random count seed"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_cases2 import classify
st = {"epochs": 0, "fail_total": 0, "fail_I": 0, "max_IV": 0, "slack_min": 10 ** 9, "false_I_le_U": 0}
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
                    bound = 1 + passes + (2 * q - 2) * rho * (k - rho)
                    if n > bound: st["fail_total"] += 1; print("FAIL total", d, r)
                    if nI > passes: st["fail_I"] += 1; print("FAIL I", d, r)
                    if nI > len(U): st["false_I_le_U"] += 1
                    st["max_IV"] = max(st["max_IV"], nIV)
                    st["slack_min"] = min(st["slack_min"], bound - n)
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]; U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r)
                vals = {}
                for h in R:
                    if Bs >> h & 1: vals.setdefault(M.comp[h], set()).add(v[h])
                passes = sum(sum(1 for a in vals.get(M.comp[z], ()) if v[z] < a) for z in U)
                q = max(len({v[e] for e in sc.bits(Bs) if M.comp[e] == c}) for c in range(M.ncomp))
                n = 0; nI = 0; nIV = 0
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            n += 1; steps += 1
            if steps > 800: return
            if rho >= 1 and D_of(M, Bs, set(R), v2) > 0:
                c = classify(M, blk, k, v, r, S, Bs, delta)
                if c[0] == "I": nI += 1
                else: nIV += 1
            v = v2
if sys.argv[1] == "random":
    rng = random.Random(int(sys.argv[3]))
    for _ in range(int(sys.argv[2])):
        kind = rng.choice(["graphic", "graphic", "binary"]); nn = rng.randint(4, 7); m = rng.randint(nn + 2, 13)
        run(random_desc(rng, kind, nn, m, rng.choice([3, 6, 12, 20])))
else:
    for f in glob.glob(sys.argv[1]):
        for line in open(f):
            if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
print(st)
