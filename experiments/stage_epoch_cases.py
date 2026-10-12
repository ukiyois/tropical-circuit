"""Instrument the case analysis of Theorem 2.4 at every update of every epoch:
case i   z2 in B* (raised anchor) passes z1;
case ii  z2 not in B*, unraised anchor b below z2 within delta (ends the epoch);
case iii raised anchor b at the value of z2 passes z1;
case iv  z2 passes g, the raised anchor b of z2 lies at or below g.
Reports per epoch: the cases, whether the unraised element passed by a raised
anchor (cases i, iii) repeats, and whether cases ii, iv occur before the last update.
Usage: python stage_epoch_cases.py"""
import ast
import glob

import stage_core as sc
from stage_search import build
from stage_epoch_check import base_meeting_r, first_event


def designated(M, blk, k, v, r, S0, Bs):
    R = {e for e in range(M.m) if blk[e] in S0}
    delta = first_event(M, blk, k, v, r, S0)
    u = sc.posl_u(M, v, delta)
    N = sc.MinBase(M, u)
    # Step 5: y in R - B*, g in B* - R, g in C(B*, y), same cluster, v_g < v_y
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
    z2 = min((e for e in C if e in R and v[e] > v[g]), key=lambda e: v[e])
    z1 = max((e for e in C if e not in R and v[e] < v[z2]), key=lambda e: v[e])
    if Bs >> z2 & 1:
        return "i", (z2, z1)
    b = next(b for b in sc.bits(M.fund_circuit(Bs, z2) & ~(1 << z2)) if v[z2] - delta <= v[b] <= v[z2])
    if b not in R:
        return "ii", (z2, b)
    if v[b] == v[z2]:
        return "iii", (b, z1)
    return "iv", (z2, g)


def main():
    found = []
    for f in glob.glob("stage_logs/exp_*.txt") + glob.glob("stage_logs/hill_*.txt"):
        for line in open(f):
            if line.startswith("score"):
                found.append(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
    stats = {"epochs": 0, "updates": 0, "repeat_anchor_z": 0, "ii_iv_not_last": 0}
    cases = {}
    for d in found:
        M = build(d)
        _, _, blk, w = d
        k = M.k
        v = list(w)
        for r in range(1, k):
            nu, S = sc.state(M, blk, k, v)
            if nu > r:
                continue
            Scur, Bs, log = None, None, []
            while True:
                nu, S = sc.state(M, blk, k, v)
                if nu > r or S != Scur:
                    if log:
                        stats["epochs"] += 1
                        zs = [p[1] for c, p in log if c in ("i", "iii")]
                        if len(zs) != len(set(zs)):
                            stats["repeat_anchor_z"] += 1
                        for idx, (c, p) in enumerate(log):
                            if c in ("ii", "iv") and idx < len(log) - 1:
                                stats["ii_iv_not_last"] += 1
                    log = []
                    if nu > r:
                        break
                    Scur, Bs = S, base_meeting_r(M, blk, k, v, r)
                c, p = designated(M, blk, k, v, r, S, Bs)
                cases[c] = cases.get(c, 0) + 1
                log.append((c, p))
                stats["updates"] += 1
                tau, lam, a, _ = sc.update(M, blk, k, v, r)
                v = sc.shift(v, blk, a)
    print(stats, "cases", cases)


if __name__ == "__main__":
    main()
