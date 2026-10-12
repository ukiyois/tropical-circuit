"""Common tools for the phase 2d epoch study (exact integer arithmetic, stage_core).

epochs(M, blk, k, w): run the PO-SL schedule from p = 0 and return one record per
epoch: stage r, S0, rho, |R|, |U|, the number n of updates, the minimum base B*
fixed at the first state, and per update the crossing pairs.
"""
import stage_core as sc
from stage_epoch_check import base_meeting_r

BOUNDS = {
    # name: function of the epoch record -> bound on n
    "m": lambda e: e["m"],
    "m-k": lambda e: e["m"] - e["k"],
    "m-k+rho": lambda e: e["m"] - e["k"] + e["rho"],
    "m-k+rho-1": lambda e: e["m"] - e["k"] + e["rho"] - 1,
    "U": lambda e: e["U"],
    "U+rho": lambda e: e["U"] + e["rho"],
    "nonanchor+rho": lambda e: e["m"] - e["k"] + e["rho"],
    "K": lambda e: e["Kbound"],
    "m-rho-1": lambda e: e["m"] - e["rho"] - 1,
    "m-2": lambda e: e["m"] - 2,
    "maxUR+rho": lambda e: max(e["U"], e["R"]) + e["rho"],
    "m|rho>=2": lambda e: e["m"] if e["rho"] >= 2 else 10 ** 6,
    "U|rho>=2": lambda e: e["U"] if e["rho"] >= 2 else 10 ** 6,
    "P1+1": lambda e: e["P1"] + 1 if e["rho"] >= 1 else 10 ** 6,
    "P1+1|rho>=2": lambda e: e["P1"] + 1 if e["rho"] >= 2 else 10 ** 6,
    "P1+1|rho>=3": lambda e: e["P1"] + 1 if e["rho"] >= 3 else 10 ** 6,
    "m|rho>=3": lambda e: e["m"] if e["rho"] >= 3 else 10 ** 6,
}


def epochs(M, blk, k, w, cap=600, want_pairs=False):
    v = list(w)
    out = []
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        Scur, rec = None, None
        steps = 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if rec is not None:
                    out.append(rec)
                if nu > r:
                    break
                Scur = S
                Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]
                U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r)
                # Theorem 2.4 bound: sum_K rho_K |U cap K| + (k_K - rho_K) |R cap K|
                Kb = 0
                for c in range(M.ncomp):
                    kK = sum(1 for e in sc.bits(Bs) if M.comp[e] == c)
                    rK = sum(1 for e in sc.bits(Bs) if M.comp[e] == c and blk[e] in S)
                    UK = sum(1 for e in U if M.comp[e] == c)
                    RK = sum(1 for e in R if M.comp[e] == c)
                    Kb += rK * UK + (kK - rK) * RK
                # P1 of ep_potential: unraised elements and raised non-anchors below the
                # highest raised anchor of their component
                top = {}
                for h in R:
                    if Bs >> h & 1:
                        top[M.comp[h]] = max(top.get(M.comp[h], v[h]), v[h])
                P1 = sum(1 for e in range(M.m) if not (blk[e] in S and Bs >> e & 1)
                         and M.comp[e] in top and v[e] < top[M.comp[e]])
                rec = {"r": r, "S": sorted(S), "rho": rho, "R": len(R), "U": len(U), "n": 0,
                       "m": M.m, "k": k, "B": Bs, "Kbound": Kb, "v0": list(v), "pairs": [], "P1": P1}
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            if want_pairs:
                pr = [(x, z) for x in R for z in U if M.comp[x] == M.comp[z] and v[x] > v[z] and v2[x] <= v2[z]]
                rec["pairs"].append(pr)
            rec["n"] += 1
            v = v2
            steps += 1
            if steps > cap:
                raise RuntimeError("cap")
    return out, v
