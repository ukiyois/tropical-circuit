"""Theorem 6 for OTHER families satisfying (F1)-(F4):
  compSL   single linkage on all non-loops of each component (no PO restriction)
  globSL   single linkage on the whole ground set (loops included, across components)
  hybrid   PO-SL for t < T0, all bases of M for t >= T0 (any T0 > 0)
  jump     N0(v) for t < T0, all bases of M for t >= T0, T0 <= min theta over non-optimal bases
For each family: verify (F1)-(F4) on the breakpoints, then the exact gain
(k-r) tau and that every base of N0(v) meeting r blocks stays optimal.
Also Theorem 8 for compSL (the proof of Steps 3-5 uses only the cluster
structure, so it should transfer)."""
import random
import sys
from core import *
import test_main as TM


def u_sl(M, v, t, restrict_po, per_comp, include_loops):
    po = set(po_set(M, v, t)) if restrict_po else set(range(M.m)) if include_loops else \
        {e for e in range(M.m) if M.R[1 << e] > 0}
    u = [INF] * M.m
    groups = {}
    for e in po:
        key = M.comp[e] if per_comp else 0
        groups.setdefault(key, []).append(e)
    for key, el in groups.items():
        el.sort(key=lambda e: v[e])
        lab = 0
        for i, e in enumerate(el):
            if i > 0 and v[e] - v[el[i - 1]] > t:
                lab += 1
            u[e] = lab
    return u


def fam_compsl(M, v, t):
    return opt_bases(M, u_sl(M, v, t, False, True, False))[0]


def fam_globsl(M, v, t):
    return opt_bases(M, u_sl(M, v, t, False, False, True))[0]


def make_hybrid(T0, inner):
    def fam(M, v, t):
        return frozenset(M.bases) if t >= T0 else inner(M, v, t)
    return fam


def update_family(M, blk, k, v, r, fam, extra):
    T = sorted(set(breakpoints(v, M.m)) | set(extra))
    tau = None
    lam = {b: INF for b in range(k)}
    Ns = {}
    for t in T:
        N = fam(M, v, t)
        Ns[t] = N
        A, nu = avoidable(N, blk, k)
        if nu > r:
            tau = t
            break
        for b in A:
            if lam[b] == INF:
                lam[b] = t
    a = {b: (F0 if tau is None or lam[b] == INF else max(tau - lam[b], F0)) for b in range(k)}
    return tau, lam, a, Ns, T


def check_family(M, blk, k, v, r, fam, extra, name, stats):
    T = sorted(set(breakpoints(v, M.m)) | set(extra))
    pts = []
    for i, t in enumerate(T):
        pts.append(t)
        if i + 1 < len(T):
            pts.append((t + T[i + 1]) / 2)
    pts.append(T[-1] + 1)
    Ns = {t: fam(M, v, t) for t in pts}
    N0, _ = opt_bases(M, v)
    ok = Ns[F0] == N0
    for i in range(len(pts) - 1):
        ok &= Ns[pts[i]] <= Ns[pts[i + 1]]
    th = {B: theta_local(M, v, B) for B in M.bases}
    for t in pts:
        for B in M.bases:
            if th[B] <= t and B not in Ns[t]:
                ok = False
    ok &= nu_of(Ns[pts[-1]], blk) == k
    if not ok:
        stats[name + "-notF"] += 1
        return
    stats[name + "-F"] += 1
    tau, lam, a, _, _ = update_family(M, blk, k, v, r, fam, extra)
    v2 = [v[e] - a[blk[e]] for e in range(M.m)]
    gain = sum(a.values(), F0) + beta(M, v2) - beta(M, v)
    if gain != (k - r) * tau:
        TM.fail(name + "-gain", (v, r, tau, a, gain))
    N0b, _ = opt_bases(M, v2)
    for B in N0:
        if len(blocks_of(B, blk)) == r and B not in N0b:
            TM.fail(name + "-Bstar", (v, r, B))
    return v2


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    rng = random.Random(seed)
    stats = {}
    for key in ["compSL", "globSL", "hybrid", "jump"]:
        stats[key + "-F"] = 0
        stats[key + "-notF"] = 0
    stats["compSL-T8"] = 0
    stats["compSL-T8-fail"] = 0
    done = 0
    while done < trials:
        kind, M = random_matroid(rng)
        if M.k == 0:
            continue
        k = M.k
        blk = rand_blocks(M, k, rng)
        if blk is None:
            continue
        v = rand_values(M.m, rng, rng.choice(["ties", "ties5", "spaced", "mixed", "generic"]))
        N0, _ = opt_bases(M, v)
        r = nu_of(N0, blk)
        if r >= k:
            continue
        done += 1
        check_family(M, blk, k, v, r, fam_compsl, [], "compSL", stats)
        check_family(M, blk, k, v, r, fam_globsl, [], "globSL", stats)
        T = breakpoints(v, M.m)
        T0 = rng.choice(T[1:] + [T[-1] / 3, T[1] / 2 if len(T) > 1 else F0 + 1])
        if T0 > 0:
            check_family(M, blk, k, v, r, make_hybrid(T0, N_posl), [T0], "hybrid", stats)
        thmin = min([theta_local(M, v, B) for B in M.bases if B not in N0], default=None)
        if thmin is not None and thmin > 0:
            T1 = thmin * Fraction(rng.randint(1, 4), 4)
            check_family(M, blk, k, v, r, make_hybrid(T1, lambda M_, v_, t_: N0), [T1], "jump", stats)
        # Theorem 8 strong form for compSL
        tau, lam, a, _, _ = update_family(M, blk, k, v, r, fam_compsl, [])
        S, _ = avoidable(N0, blk, k)
        v2 = [v[e] - a[blk[e]] for e in range(M.m)]
        C0 = TM.cross(blk, v, S, M.m)
        C1 = TM.cross(blk, v2, S, M.m)
        stats["compSL-T8"] += 1
        if not C0 < C1:
            stats["compSL-T8-fail"] += 1
    print("stats", stats)
    print("failures", len(TM.FAIL))


if __name__ == "__main__":
    main()
