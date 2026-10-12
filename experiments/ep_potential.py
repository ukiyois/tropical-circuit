"""Empirical test of candidate potentials for epochs with rho >= 1 (phase 2d, Section 5).

For an epoch with B* fixed, R-frame values, and for each component K let
T_K = the largest value of a raised anchor of K (if any).  Candidates:
  P1  #{z in U : K(z) has raised anchors, v_z < T_{K(z)}}
      + #{x in R - B* : v_x < T_{K(x)}, no unraised element has crossed x so far}
  P2  same as P1 but T_K = value of the highest raised anchor of K that lies
      in C(B*, y) for some y in R - B* with C(B*, y) cap U nonempty
  P3  #{z in U : v_z < T_{K(z)}} + #{x in R - B* : v_x < T_{K(x)}, some z in U cap K(x) has v_z < v_x}
Check: P strictly decreases at every update that is not last; report the max
of n - (P(v^0) + 1) over epochs (P(v^0) + 1 would be the bound).
Usage: python ep_potential.py "glob" | random count seed
"""
import ast
import glob
import random
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, D_of


def tops(M, Bs, R, v, mode):
    T = {}
    for h in R:
        if not (Bs >> h & 1):
            continue
        if mode == 2:
            ok = False
            for y in R:
                if Bs >> y & 1:
                    continue
                C = M.fund_circuit(Bs, y)
                if C >> h & 1 and any(not (g in R) for g in sc.bits(C & ~(1 << y))):
                    ok = True
                    break
            if not ok:
                continue
        c = M.comp[h]
        T[c] = max(T.get(c, v[h]), v[h])
    return T


def potential(M, Bs, R, U, v, T, crossed, mode):
    p = 0
    for z in U:
        c = M.comp[z]
        if c in T and v[z] < T[c]:
            p += 1
    for x in R:
        if Bs >> x & 1:
            continue
        c = M.comp[x]
        if c not in T or not v[x] < T[c]:
            continue
        if mode in (1, 2):
            if x not in crossed:
                p += 1
        elif mode == 4:
            if x not in crossed:
                p += 1
            if any(M.comp[g] == c and (Bs >> g & 1) and v[g] < v[x] for g in U):
                p += 1
        else:
            if any(M.comp[z] == c and v[z] < v[x] for z in U):
                p += 1
    return p


def run(d, st, bad):
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
        Scur = None
        steps = 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if Scur is not None and rho >= 1:
                    st["epochs"] += 1
                    for mode in (1, 2, 3, 4):
                        st[f"slack{mode}"] = max(st[f"slack{mode}"], n - (P0[mode] + 1))
                if nu > r:
                    break
                Scur, n = S, 0
                Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]
                U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r)
                Ts = {mode: tops(M, Bs, R, v, 1 if mode in (3, 4) else mode) for mode in (1, 2, 3, 4)}
                Ts[3] = Ts[1]
                crossed = set()
                P0 = {mode: potential(M, Bs, R, U, v, Ts[mode], crossed, mode) for mode in (1, 2, 3, 4)}
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            n += 1
            steps += 1
            if steps > 800:
                return
            if rho >= 1:
                Tb = {mode: tops(M, Bs, R, v, 1 if mode in (3, 4) else mode) for mode in (1, 2, 3, 4)}
                Ta = {mode: tops(M, Bs, R, v2, 1 if mode in (3, 4) else mode) for mode in (1, 2, 3, 4)}
                before = {mode: potential(M, Bs, R, U, v, Tb[mode], crossed, mode) for mode in (1, 2, 3, 4)}
                newcross = set(crossed)
                for x in R:
                    for z in U:
                        if M.comp[x] == M.comp[z] and v[z] < v[x] and v2[z] >= v2[x]:
                            newcross.add(x)
                after = {mode: potential(M, Bs, R, U, v2, Ta[mode], newcross, mode) for mode in (1, 2, 3, 4)}
                last = D_of(M, Bs, set(R), v2) == 0
                if not last:
                    st["nonlast"] += 1
                    for mode in (1, 2, 3, 4):
                        if not after[mode] < before[mode]:
                            st[f"fail{mode}"] += 1
                            if len(bad[mode]) < 3:
                                bad[mode].append((d, r, n))
                crossed = newcross
            v = v2


def main():
    st = {"epochs": 0, "nonlast": 0, "fail1": 0, "fail2": 0, "fail3": 0, "fail4": 0,
          "slack1": -99, "slack2": -99, "slack3": -99, "slack4": -99}
    bad = {1: [], 2: [], 3: [], 4: []}
    if sys.argv[1] == "random":
        rng = random.Random(int(sys.argv[3]))
        for _ in range(int(sys.argv[2])):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(4, 7)
            m = rng.randint(n + 2, 13)
            run(random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20])), st, bad)
    else:
        for f in glob.glob(sys.argv[1]):
            for line in open(f):
                if "desc" in line:
                    run(ast.literal_eval(line[line.index("desc ") + 5:].strip()), st, bad)
    print(st)
    for mode in (1, 2, 3, 4):
        for b in bad[mode]:
            print("FAIL", mode, b)


if __name__ == "__main__":
    main()
