"""Phase 2f core: LS runs with the potentials p_j recorded, and the dual optimum set.

Notation of greedy_intersection.tex, Section 4, and docs/phase2c (ls_core).
  P*  = { p : Psi(p) = Opt(w) } = { p : B is a minimum base of w - p_blk }
        for ANY optimal rainbow base B (weak duality, Lemma lem:duality).
  The minimum-base condition is a system of difference constraints
        p_{blk f} - p_{blk e} >= w_f - w_e     (e notin B, f in C(B, e) - e),
  so P* is a lattice; p0 = the least element of P* with p >= 0 is given by longest
  paths from a virtual source (Bellman-Ford), and min p0 = 0.
Exact arithmetic: ints / Fractions throughout.
"""
import itertools
import random

import stage_core as sc
import ls_core as lc


def all_bases(M):
    return [sc.mask_of(c) for c in itertools.combinations(range(M.m), M.k)
            if M.rank(sc.mask_of(c)) == M.k]


def opt_rainbow_base(M, blk, k, w, bases=None):
    bases = all_bases(M) if bases is None else bases
    best = None
    for B in bases:
        el = sc.bits(B)
        if len({blk[e] for e in el}) != k:
            continue
        val = sum(w[e] for e in el)
        if best is None or val < best[0]:
            best = (val, B)
    return best


def diff_constraints(M, blk, k, w, B):
    """Arcs (b, c, L): p_c >= p_b + L, from exchange pairs of B."""
    L = {}
    for e in range(M.m):
        if B >> e & 1 or M.rank(1 << e) == 0:
            continue
        for f in sc.bits(M.fund_circuit(B, e) & ~(1 << e)):
            b, c = blk[e], blk[f]
            d = w[f] - w[e]
            if (b, c) not in L or d > L[(b, c)]:
                L[(b, c)] = d
    return L


def least_dual(M, blk, k, w, B):
    """Least p >= 0 with B minimum for w - p_blk (None if infeasible)."""
    L = diff_constraints(M, blk, k, w, B)
    for (b, c), d in L.items():
        if b == c and d > 0:
            return None
    p = [0] * k
    for _ in range(k + 1):
        ch = False
        for (b, c), d in L.items():
            if p[b] + d > p[c]:
                p[c] = p[b] + d
                ch = True
        if not ch:
            return p
    return None  # positive cycle


def in_Pstar(M, blk, k, w, p, B):
    v = [w[e] - p[blk[e]] for e in range(M.m)]
    return sum(v[e] for e in sc.bits(B)) == sc.beta(M, v)


def ls_run(M, blk, k, w, cap=2000, family=sc.posl):
    """LS iteration from p = 0.  Returns list of dicts per state:
    p, v, nu, S0; and per block: a, pcs, tau."""
    v = list(w)
    p = [0] * k
    nu, S0 = lc.nu_state(M, blk, k, v)
    states = [{"p": list(p), "v": list(v), "nu": nu, "S0": S0}]
    blocks = []
    while nu < k:
        a, pcs, tau = lc.block(M, blk, k, v, k - 1, family)
        if not any(a):
            raise RuntimeError("zero block at nu0 < k")
        v = lc.shift(v, blk, a)
        p = [p[b] + a[b] for b in range(k)]
        nu, S0 = lc.nu_state(M, blk, k, v)
        states.append({"p": list(p), "v": list(v), "nu": nu, "S0": S0})
        blocks.append({"a": a, "pcs": pcs, "tau": tau})
        if len(blocks) > cap:
            raise RuntimeError("LS cap exceeded")
    return states, blocks


# ------------------------------------------------------------ instances
def rand_instance(rng, kmin=3, kmax=6, mmax=11):
    """A random matroid with blocks and a rainbow base, and weights."""
    from ls_mono_random import random_matroid, has_rainbow_base
    from ls_search_drop import rmat, rweights
    while True:
        kind, M = (rmat(rng) if rng.random() < 0.5 else random_matroid(rng))
        k = M.k
        if k < kmin or k > kmax or M.m > mmax:
            continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k):
            continue
        w = rweights(rng, M.m)
        return kind, M, blk, k, w


def describe(M):
    if hasattr(M, "edges"):
        return ("graphic", M.nv, M.edges)
    if hasattr(M, "cols"):
        return ("binary", M.cols)
    return (M.name,)
