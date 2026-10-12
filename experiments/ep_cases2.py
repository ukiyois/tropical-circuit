"""Case structure of non-last updates for rho >= 2 (phase 2d note, Section 3).

For each non-last update, with (y, g) the linking pair of Step 5 of
thm:potential (chosen by stage_epoch_cases.designated), z2 the lowest raised
element of the cluster above g, z1 the highest unraised element below z2:
  case I   a raised anchor h with v_h = v_{z2} passes z1     (record h, z1)
  case IV  z2 (raised non-anchor) passes g; its raised window anchor h2 <= g
Reports per epoch the sequence, the number of distinct z1 in case I, the number
of distinct z2 in case IV, and the reuse counts.
Usage: python ep_cases2.py source
"""
import ast
import glob
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_epoch_check import base_meeting_r, first_event, D_of


def classify(M, blk, k, v, r, S0, Bs, delta):
    R = {e for e in range(M.m) if blk[e] in S0}
    u = sc.posl_u(M, v, delta)
    pair = None
    for y in sorted(R, key=lambda e: v[e]):
        if Bs >> y & 1 or u[y] > M.m:
            continue
        for g in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
            if g not in R and u[g] == u[y] and M.comp[g] == M.comp[y] and v[g] < v[y]:
                pair = (y, g)
                break
        if pair:
            break
    y, g = pair
    C = [e for e in range(M.m) if u[e] == u[y] and M.comp[e] == M.comp[y]]
    z2 = min((e for e in C if e in R and v[e] > v[g]), key=lambda e: (v[e], -(Bs >> e & 1)))
    z1 = max((e for e in C if e not in R and v[e] < v[z2]), key=lambda e: v[e])
    hs = [h for h in C if h in R and (Bs >> h & 1) and v[h] == v[z2]]
    if hs:
        return ("I", hs[0], z1, g, y)
    win = [b for b in sc.bits(M.fund_circuit(Bs, z2) & ~(1 << z2)) if v[b] >= v[z2] - delta]
    return ("IV", z2, g, win, y)


def run(d, out):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return
    v = list(w)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        Scur, log = None, []
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if log and log[0][0] >= 2:
                    out.append((d, r, log))
                log = []
                if nu > r:
                    break
                Scur = S
                Bs = base_meeting_r(M, blk, k, v, r)
                R = {e for e in range(M.m) if blk[e] in S}
                rho = len(S) - (k - r)
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            D2 = D_of(M, Bs, R, v2)
            if D2 > 0:
                c = classify(M, blk, k, v, r, S, Bs, delta)
            else:
                c = ("last",)
            log.append((rho, c))
            v = v2


def main():
    out = []
    for f in glob.glob(sys.argv[1]):
        for line in open(f):
            if "desc" in line:
                run(ast.literal_eval(line[line.index("desc ") + 5:].strip()), out)
    tot = {"epochs": 0, "I": 0, "IV": 0, "reuseI": 0, "reuseIV": 0}
    for d, r, log in out:
        tot["epochs"] += 1
        zI = [c[2] for _, c in log if c[0] == "I"]
        zIV = [c[1] for _, c in log if c[0] == "IV"]
        tot["I"] += len(zI)
        tot["IV"] += len(zIV)
        tot["reuseI"] += len(zI) - len(set(zI))
        tot["reuseIV"] += len(zIV) - len(set(zIV))
        if len(zI) != len(set(zI)) or len(zIV) != len(set(zIV)) or len(log) >= 6:
            print("epoch r", r, "rho", log[0][0], "n", len(log), [c[:3] for _, c in log])
    print(tot)


if __name__ == "__main__":
    main()
