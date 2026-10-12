"""Random-instance checks along whole schedules (phase 2d note).

Every epoch of the PO-SL schedule from p = 0 is followed with B* fixed at its
first state.  At every update that is not last (D(v') > 0):
  A1   D(v) > delta                                         (Lemma A.1)
  A2   every y in (R - B*) cap PO_delta has a window anchor, all in R   (Lemma A.2)
  DI   dichotomy (Lemma B.1): with (y, g), z2, z1 as in ep_cases2.classify, either
       (I)  a raised anchor h with v_h = v_{z2} exists and v'_h <= v'_{z1}, or
       (IV) z2 notin B*, some raised anchor h2 in C(B*, z2) has
            v_{z2} - delta <= v_{h2} <= v_g, and v'_{z2} <= v'_g.
Per epoch with rho = 1:
  TA   n <= 1 + #{z in U cap K(h) : v_z < v_h at the first state}   (Theorem A)
  FA   n <= #{...}  (false variant, no +1)
Usage: python ep_check_random.py count seed [nmin nmax mmax]
       python ep_check_random.py "glob of log files"
"""
import random
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of


def check_desc(d, st, bad):
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
        Scur, n, steps = None, 0, 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if Scur is not None and rho == 1:
                    st["epochs_rho1"] += 1
                    if not n <= 1 + below:
                        st["fail_TA"] += 1
                        bad.append(("TA", d, r))
                    if not n <= below:
                        st["fail_FA"] += 1
                if nu > r:
                    break
                Scur, n = S, 0
                Bs = base_meeting_r(M, blk, k, v, r)
                R = {e for e in range(M.m) if blk[e] in S}
                rho = len(S) - (k - r)
                if rho == 1:
                    h = next(e for e in R if Bs >> e & 1)
                    below = sum(1 for z in range(M.m) if z not in R and M.comp[z] == M.comp[h] and v[z] < v[h])
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            D, D2 = D_of(M, Bs, R, v), D_of(M, Bs, R, v2)
            n += 1
            steps += 1
            if steps > 800:
                return
            if D2 > 0 and rho >= 1:
                st["nonlast"] += 1
                if not D > delta:
                    st["fail_A1"] += 1
                    bad.append(("A1", d, r))
                po = set(sc.po_set(M, v, delta))
                for y in R:
                    if Bs >> y & 1 or y not in po:
                        continue
                    win = [b for b in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)) if v[b] >= v[y] - delta]
                    if not win or any(b not in R for b in win):
                        st["fail_A2"] += 1
                        bad.append(("A2", d, r))
                        break
                # dichotomy
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
                z2 = min((e for e in C if e in R and v[e] > v[g]), key=lambda e: v[e])
                z1 = max((e for e in C if e not in R and v[e] < v[z2]), key=lambda e: v[e])
                hs = [hh for hh in R if (Bs >> hh & 1) and M.comp[hh] == M.comp[z2] and v[hh] == v[z2]]
                okI = any(v2[hh] <= v2[z1] for hh in hs)
                okIV = False
                if not (Bs >> z2 & 1):
                    for h2 in sc.bits(M.fund_circuit(Bs, z2) & ~(1 << z2)):
                        if h2 in R and v[z2] - delta <= v[h2] <= v[g] and v2[z2] <= v2[g]:
                            okIV = True
                st["case_I"] += okI
                st["case_IV"] += (not okI) and okIV
                if not (okI or okIV):
                    st["fail_DI"] += 1
                    bad.append(("DI", d, r))
            v = v2


def main():
    if not sys.argv[1].isdigit():
        import ast
        import glob
        st = {"inst": 0, "nonlast": 0, "epochs_rho1": 0, "case_I": 0, "case_IV": 0,
              "fail_A1": 0, "fail_A2": 0, "fail_DI": 0, "fail_TA": 0, "fail_FA": 0}
        bad = []
        for f in glob.glob(sys.argv[1]):
            for line in open(f):
                if "desc" in line:
                    st["inst"] += 1
                    check_desc(ast.literal_eval(line[line.index("desc ") + 5:].strip()), st, bad)
        print(st)
        for b in bad[:5]:
            print("BAD", b)
        return
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 7
    mmax = int(sys.argv[5]) if len(sys.argv) > 5 else 13
    rng = random.Random(seed)
    st = {"inst": 0, "nonlast": 0, "epochs_rho1": 0, "case_I": 0, "case_IV": 0,
          "fail_A1": 0, "fail_A2": 0, "fail_DI": 0, "fail_TA": 0, "fail_FA": 0}
    bad = []
    for _ in range(count):
        kind = rng.choice(["graphic", "graphic", "binary"])
        n = rng.randint(nmin, nmax)
        m = rng.randint(n + 2, mmax)
        d = random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20]))
        st["inst"] += 1
        check_desc(d, st, bad)
    print(st)
    for b in bad[:5]:
        print("BAD", b)


if __name__ == "__main__":
    main()
