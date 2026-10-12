"""Conjecture Q (phase 2d note, Section 5): per epoch with rho >= 1,
   #repeats + #case IV <= #{x in R - B* : v_x < T_{K(x)}}   (values at the first state),
where a repeat is a case (I) update whose z1 was the z1 of an earlier case (I) update of
the epoch, and T_K is the largest raised-anchor value of K.  Also reports the slack.
Usage: python ep_conjQ.py "glob" | random count seed"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_cases2 import classify

def run(d, st, bad):
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
                    val = rep + iv - budget
                    st["maxslack"] = max(st["maxslack"], val)
                    key = "eq" if val == 0 else ("lt" if val < 0 else "gt")
                    st[key + "_rho" + str(min(rho, 3))] = st.get(key + "_rho" + str(min(rho, 3)), 0) + 1
                    if val > 0:
                        st["fail"] += 1
                        if len(bad) < 4: bad.append((d, r))
                if nu > r: break
                Scur = S; Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]
                rho = len(S) - (k - r)
                top = {}
                for h in R:
                    if Bs >> h & 1: top[M.comp[h]] = max(top.get(M.comp[h], v[h]), v[h])
                budget = sum(1 for x in R if not (Bs >> x & 1) and M.comp[x] in top and v[x] < top[M.comp[x]])
                seen = set(); rep = 0; iv = 0
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r); v2 = sc.shift(v, blk, a)
            steps += 1
            if steps > 800: return
            if rho >= 1 and D_of(M, Bs, set(R), v2) > 0:
                c = classify(M, blk, k, v, r, S, Bs, delta)
                if c[0] == "I":
                    if c[2] in seen: rep += 1
                    seen.add(c[2])
                else:
                    iv += 1
            v = v2

st = {"epochs": 0, "fail": 0, "maxslack": -99}; bad = []
if sys.argv[1] == "random":
    rng = random.Random(int(sys.argv[3]))
    for _ in range(int(sys.argv[2])):
        kind = rng.choice(["graphic", "graphic", "binary"]); n = rng.randint(4, 7); m = rng.randint(n + 2, 13)
        run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])), st, bad)
else:
    for f in glob.glob(sys.argv[1]):
        for line in open(f):
            if "desc" in line: run(ast.literal_eval(line[line.index("desc ") + 5:].strip()), st, bad)
print(st)
for b in bad: print("FAIL", b)
