"""Phase 2c core: the stage-r circuit block at ANY state, its path, the LS iteration.

Notation of greedy_intersection.tex, Section 4.  A state is v = w - p_blk.  During one
block application the family is N(t) = N_v(t), PO-SL at the state v where the block
starts.  The stage-r block computes
    a_b = int_0^inf [nu(N(t)) <= r] [b in Av(N(t))] dt.
Path:  a(s)_b = int_0^s (same integrand) dt,  v(s) = v - a(s)_blk,  L(s) = M^{v(s)}.
N(t) is constant on [l_i, l_{i+1}) for the levels l_i of sc.levels_of(v) (F5), so the
path is piecewise linear with direction -1_{E_A}, A = Av(N(l_i)), on each piece.

Exact arithmetic: integer weights give integer levels; midpoints are Fractions.
"""
from fractions import Fraction

import stage_core as sc


def pieces(M, blk, k, v, r, family=sc.posl):
    """The pieces [c0, c1) of N below tau_r: list of (c0, c1, nu, Av), and tau_r."""
    levels = sc.levels_of(v)
    out = []
    for i, t in enumerate(levels):
        N = family(M, v, t)
        nu, av, _ = sc.rainbow_av(N, blk, k)
        if nu > r:
            return out, t
        if i + 1 == len(levels):
            raise RuntimeError("family never exceeds r (F4 fails)")
        out.append((t, levels[i + 1], nu, av))
    raise RuntimeError("no levels")


def block(M, blk, k, v, r, family=sc.posl):
    """The stage-r block at v.  Returns (a, pcs, tau_r)."""
    pcs, tau = pieces(M, blk, k, v, r, family)
    a = [0] * k
    for c0, c1, nu, A in pcs:
        for b in A:
            a[b] += c1 - c0
    return a, pcs, tau


def shift(v, blk, a):
    return [v[e] - a[blk[e]] for e in range(len(v))]


def psi(M, blk, k, p, v):
    return sum(p) + sc.beta(M, v)


def nu_state(M, blk, k, v):
    N = sc.MinBase(M, v)
    nu, av, _ = sc.rainbow_av(N, blk, k)
    return nu, av


def path_intervals(M, blk, k, v, pcs):
    """Open intervals (s0, s1) of [0, tau] on which v(s) has a constant order, with
    the midpoint state; also the states at the piece ends.  Yields
    ('open', s0, s1, v_mid, piece_index) and ('end', c1, v_end, piece_index)."""
    cur = list(v)
    for idx, (c0, c1, nu, A) in enumerate(pcs):
        X = [e for e in range(len(v)) if blk[e] in A]
        Xs = set(X)
        ts = {c0, c1}
        if X:
            for e in X:
                for f in range(len(v)):
                    if f in Xs:
                        continue
                    d = cur[e] - cur[f]
                    if 0 < d < c1 - c0:
                        ts.add(c0 + d)
        ts = sorted(ts)
        for s0, s1 in zip(ts, ts[1:]):
            mid = Fraction(s0 + s1, 2)
            vm = [cur[e] - (mid - c0) if e in Xs else cur[e] for e in range(len(v))]
            yield ("open", s0, s1, vm, idx)
        cur = [cur[e] - (c1 - c0) if e in Xs else cur[e] for e in range(len(v))]
        yield ("end", c1, list(cur), idx)


def path_profile(M, blk, k, v, r, family=sc.posl):
    """Run one stage-r block with full path instrumentation.
    Returns dict: a, tau, pcs, nu0, nu_end, nu_min_open (min of nu(L(s)) over open
    intervals), first_drop (first open interval with nu(L) < nu0, or None),
    gain = Psi(p+a) - Psi(p), lower = int (k - nu(N)) ds."""
    nu0, S0 = nu_state(M, blk, k, v)
    a, pcs, tau = block(M, blk, k, v, r, family)
    numin = nu0
    first_drop = None
    ends = []
    seq = []
    for item in path_intervals(M, blk, k, v, pcs):
        if item[0] == "open":
            _, s0, s1, vm, idx = item
            nu, _ = nu_state(M, blk, k, vm)
            seq.append(nu)
            if nu < numin:
                numin = nu
            if nu < nu0 and first_drop is None:
                first_drop = (s0, s1, idx, nu)
        else:
            ends.append(item)
    v2 = shift(v, blk, a)
    nu_end, S_end = nu_state(M, blk, k, v2)
    gain = sum(a) + sc.beta(M, v2) - sc.beta(M, v)
    lower = sum((c1 - c0) * (k - nu) for c0, c1, nu, A in pcs)
    return {"a": a, "tau": tau, "pcs": pcs, "nu0": nu0, "S0": S0, "nu_end": nu_end,
            "S_end": S_end, "nu_min_open": numin, "first_drop": first_drop,
            "gain": gain, "lower": lower, "v2": v2, "nu_seq": seq}


def ls_iterate(M, blk, k, w, cap=1000, family=sc.posl, record=False):
    """Iterate the last-stage block from p = 0.  Returns (count, v, nus, ok_mono)."""
    v = list(w)
    nu, _ = nu_state(M, blk, k, v)
    nus = [nu]
    count = 0
    mono = True
    while nu < k:
        a, pcs, tau = block(M, blk, k, v, k - 1, family)
        if not any(a):
            raise RuntimeError("stuck: zero block at nu0 < k")
        v = shift(v, blk, a)
        count += 1
        nu2, _ = nu_state(M, blk, k, v)
        if nu2 < nu:
            mono = False
        nu = nu2
        nus.append(nu)
        if count > cap:
            raise RuntimeError("LS cap exceeded")
    return count, v, nus, mono


def regular(M, blk, k, w, cap=10_000):
    """The regular PO-SL schedule: stage lengths (active updates) and final v."""
    lens, v = sc.run_schedule(M, blk, k, w, cap=cap)
    return lens, v


def R_bound(k, m):
    return sum(min(r * (m * m // 4 + 1), 1 + (r - 1) * k * m) for r in range(1, k))


def psi_of_v(M, blk, k, w, v):
    return sc.psi_from_v(M, blk, k, w, v)
