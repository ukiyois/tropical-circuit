"""Phase 2e tracer (docs/phase2e-epoch-rho2-2026-10-12.md): epochs with rho >= 2 in the R-frame.

Per update of an epoch: delta, tau, D, the rise of each unraised block, and for each
component holding a raised anchor the sorted R-frame positions with tags
  RA raised anchor, RN raised non-anchor, UA unraised anchor, UN unraised non-anchor,
  a trailing '.' if the element is in PO_delta, and the cluster label at scale delta;
the linking D-pairs at scale delta, the case of Lemma B.1, and the crossings.
Usage: python ep2_trace.py "<descriptor literal>" [stage]
"""
import ast
import sys

import stage_core as sc
from stage_search import build
from stage_epoch_check import base_meeting_r, first_event, D_of
from ep_cases2 import classify


def tags(M, Bs, R, e):
    return ("R" if e in R else "U") + ("A" if Bs >> e & 1 else "N")


def linking_pairs(M, Bs, R, v, t):
    u = sc.posl_u(M, v, t)
    out = []
    for y in R:
        if Bs >> y & 1 or u[y] > M.m:
            continue
        for g in sc.bits(M.fund_circuit(Bs, y) & ~(1 << y)):
            if g not in R and u[g] == u[y]:
                out.append((y, g))
    return out, u


def trace(d, only=None, out=sys.stdout, minrho=2):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    v = list(w)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        Scur = None
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if nu > r:
                    break
                Scur = S
                Bs = base_meeting_r(M, blk, k, v, r)
                R = {e for e in range(M.m) if blk[e] in S}
                rho = len(S) - (k - r)
                shift = 0
                n = 0
                show = rho >= minrho and (only is None or only == r)
                if show:
                    print(f"== stage {r} S0={sorted(S)} rho={rho} B*={sc.bits(Bs)}", file=out)
                    comps = sorted({M.comp[h] for h in R if Bs >> h & 1})
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            n += 1
            if show:
                D = D_of(M, Bs, R, v)
                D2 = D_of(M, Bs, R, v2)
                lp, u = linking_pairs(M, Bs, R, v, delta)
                rises = {b: tau - a[b] for b in range(k) if b not in S}
                print(f" upd {n}: D={D} delta={delta} tau={tau} D'={D2} rises={rises}", file=out)
                for c in comps:
                    el = sorted((e for e in range(M.m) if M.comp[e] == c), key=lambda e: (v[e], e))
                    cells = []
                    for e in el:
                        po = "." if u[e] <= M.m else ""
                        cl = f"[{u[e]}]" if u[e] <= M.m else ""
                        cells.append(f"{e}{tags(M, Bs, R, e)}{po}{cl}@{v[e] + shift}")
                    print("   comp", c, " ".join(cells), file=out)
                print("   linking", lp, file=out)
                if D2 > 0:
                    print("   case", classify(M, blk, k, v, r, S, Bs, delta), file=out)
                else:
                    print("   last", file=out)
                cr = [(x, z) for x in R for z in range(M.m) if z not in R and M.comp[x] == M.comp[z]
                      and v[x] > v[z] and v2[x] <= v2[z]]
                print("   cross", cr, file=out)
            shift += tau
            v = v2


if __name__ == "__main__":
    d = ast.literal_eval(sys.argv[1])
    only = int(sys.argv[2]) if len(sys.argv) > 2 else None
    trace(d, only)
