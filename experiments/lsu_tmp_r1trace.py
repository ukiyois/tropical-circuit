import random
import stage_core as sc, lsu_trace as tr, ls_core as lc
from lsu_rankone import instance
rng = random.Random(19000)
found = 0
while found < 2:
    k, parts, blk, w = instance(rng)
    if k < 5: continue
    M = sc.partition(parts)
    t = tr.trace(M, blk, k, w, cap=200)
    if len(t) >= k - 1:
        found += 1
        print("k", k, "T", len(t))
        # print reduced-cost matrix d at each state
        def dmat(v):
            mu = {c: min(v[e] for e in range(len(v)) if parts[e] == c) for c in range(k)}
            d = [["." for c in range(k)] for b in range(k)]
            for e in range(len(v)):
                b, c = blk[e], parts[e]
                val = v[e] - mu[c]
                if d[b][c] == "." or val < d[b][c]: d[b][c] = val
            return d
        for j, s in enumerate(t):
            print(" state", j, "nu0", s["nu0"], "S0", sorted(s["S0"]), "tau", s["tau"], "a", s["a"], "mismatch", s["mismatch"])
            for row in dmat(s["v"]): print("    ", row)
            print("    pieces:", [(c0, c1, nu, sorted(A)) for c0, c1, nu, A in s["pcs"]])
        print(" final"); [print("    ", row) for row in dmat(t[-1]["v2"])]
