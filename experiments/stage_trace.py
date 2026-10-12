"""Trace a PO-SL stage update by update: values, raised set, tau, lambda, a,
the first event delta, and the clusters at delta."""
import sys

import stage_core as sc


def first_event(M, blk, k, v, r, S0):
    for t in sc.levels_of(v):
        N = sc.posl(M, v, t)
        nu, av, _ = sc.rainbow_av(N, blk, k)
        if nu > r or av != S0:
            return t, nu, av
    return None


def show(M, blk, k, v, r, comp=True):
    nu0, S0 = sc.state(M, blk, k, v)
    order = sorted(range(M.m), key=lambda e: (v[e], e))
    s = []
    for e in order:
        tag = "R" if blk[e] in S0 else "u"
        s.append(f"{e}:{v[e]}{tag}{blk[e]}c{M.comp[e]}")
    print("   values:", " ".join(s))
    return nu0, S0


def trace(M, blk, k, w, r=None, verbose=True):
    v = list(w)
    nu0, S0 = sc.state(M, blk, k, v)
    if r is None:
        r = nu0
    step = 0
    while True:
        nu0, S0 = sc.state(M, blk, k, v)
        if nu0 > r:
            print(f"stage {r} done after {step} updates; nu0 = {nu0}")
            return step, v
        print(f"update {step + 1}: nu0={nu0} S0={sorted(S0)}")
        show(M, blk, k, v, r)
        ev = first_event(M, blk, k, v, r, S0)
        tau, lam, a, info = sc.update(M, blk, k, v, r)
        print(f"   delta={ev[0]} (nu {ev[1]}, Av {sorted(ev[2])})  tau={tau}  "
              f"lam={ {b: lam[b] for b in range(k)} }  a={a}")
        u = sc.posl_u(M, v, ev[0])
        cl = {}
        for e in range(M.m):
            if u[e] <= M.m:
                cl.setdefault((M.comp[e], u[e]), []).append(e)
        print("   clusters at delta:", {key: sorted(val, key=lambda e: v[e]) for key, val in cl.items()})
        v = sc.shift(v, blk, a)
        step += 1


if __name__ == "__main__":
    ex = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    if ex == 1:
        edges, colors, w = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)], [0, 1, 1, 1, 2, 0], [3, 1, 0, 3, 3, 2]
    else:
        edges, colors, w = ([(2, 3), (1, 0), (0, 3), (1, 0), (2, 1), (3, 0), (0, 2), (2, 0), (3, 0)],
                            [1, 0, 1, 2, 0, 1, 1, 1, 1], [5, 9, 6, 12, 10, 9, 3, 2, 4])
    M = sc.graphic(4, edges)
    print("edges", list(enumerate(edges)))
    k = M.k
    v = list(w)
    nu0, S0 = sc.state(M, colors, k, v)
    # run earlier stages silently
    for r in range(1, k):
        nu0, S0 = sc.state(M, colors, k, v)
        if nu0 > r:
            continue
        if r < 2:
            c, v = sc.run_stage(M, colors, k, v, r)
            print(f"stage {r}: {c} updates (silent)")
            continue
        trace(M, colors, k, v, r)
