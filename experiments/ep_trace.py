"""Epoch tracer in the R-frame (raised elements fixed, unraised ones rising).

For every epoch of every stage of an instance, print per update:
  delta, tau, the rise Delta_z = tau - a_blk(z) of each unraised block,
  all crossing pairs (x in R, z in U, same component, v_x > v_z, v'_x <= v'_z),
  marked A when x or z lies in B*.
Positions are printed in the R-frame: p_e = v_e + T, T = sum of tau so far in the
epoch, so raised elements keep their position.
Usage: python ep_trace.py   (edit the instance list at the bottom)
"""
import sys

import stage_core as sc
from stage_epoch_check import base_meeting_r, first_event, D_of


def crossing_pairs(M, R, U, v, v2):
    out = []
    for x in R:
        for z in U:
            if M.comp[x] != M.comp[z]:
                continue
            if v[x] > v[z] and v2[x] <= v2[z]:
                out.append((x, z))
    return out


def trace_instance(M, blk, k, w, out=sys.stdout, only_r=None, verbose=True):
    v = list(w)
    res = []
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        Scur, Bs, T, n_ep, ep_info = None, None, 0, 0, None
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if ep_info is not None:
                    res.append(ep_info)
                if nu > r:
                    break
                Scur = S
                Bs = sc.base_meeting_r(M, blk, k, v, r) if hasattr(sc, "base_meeting_r") else base_meeting_r(M, blk, k, v, r)
                T = 0
                R = [e for e in range(M.m) if blk[e] in S]
                U = [e for e in range(M.m) if blk[e] not in S]
                rho = len(S) - (k - r)
                ep_info = {"r": r, "S": sorted(S), "rho": rho, "R": len(R), "U": len(U), "n": 0,
                           "anchor_cross": [], "B": sc.bits(Bs)}
                if verbose and (only_r is None or r == only_r):
                    print(f"== stage {r} epoch S0={sorted(S)} rho={rho} |R|={len(R)} |U|={len(U)} "
                          f"B*={sc.bits(Bs)}", file=out)
            delta = first_event(M, blk, k, v, r, S)
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            v2 = sc.shift(v, blk, a)
            pairs = crossing_pairs(M, R, U, v, v2)
            apairs = [(x, z) for (x, z) in pairs if (Bs >> x & 1) or (Bs >> z & 1)]
            ep_info["n"] += 1
            ep_info["anchor_cross"].append(apairs)
            if verbose and (only_r is None or r == only_r):
                D = D_of(M, Bs, set(R), v)
                order = sorted(range(M.m), key=lambda e: (M.comp[e], v[e] + T, e))
                cells = []
                for e in order:
                    tag = ("R" if e in R else "u") + ("*" if Bs >> e & 1 else "")
                    cells.append(f"{e}{tag}b{blk[e]}c{M.comp[e]}@{v[e] + T}")
                rises = {b: tau - a[b] for b in range(k) if b not in S}
                print(f" upd {ep_info['n']}: D={D} delta={delta} tau={tau} rises={rises}", file=out)
                print("   " + " ".join(cells), file=out)
                print(f"   cross: {pairs}  anchored: {apairs}", file=out)
            T += tau
            v = v2
    return res, v


if __name__ == "__main__":
    insts = [
        # B0 Conjecture 2.7 counterexample (k = 4)
        ("graphic", (5, [(2, 0), (3, 4), (2, 3), (1, 0), (1, 4), (0, 2), (3, 2), (2, 0), (2, 0), (0, 4)]),
         [1, 0, 3, 0, 2, 3, 2, 1, 2, 3],
         [36271, 3354, 34766, 7768, 72064, 32455, 22426, 34002, 17040, 35133]),
        # B0 max(|U|,|R|)+1 counterexample
        ("graphic", (5, [(1, 3), (3, 1), (2, 0), (2, 0), (0, 3), (1, 3), (4, 2), (2, 1), (4, 2), (0, 4)]),
         [0, 1, 2, 2, 1, 1, 2, 3, 2, 2],
         [335362, 233742, 26, 3789, 313619, 273680, 811, 1048576, 83842, 120224]),
    ]
    from stage_search import build
    for d in insts:
        M = build(d)
        print("#### instance", d)
        res, _ = trace_instance(M, d[2], M.k, d[3])
        print("epochs:", [(e["r"], e["rho"], e["U"], e["R"], e["n"]) for e in res])
