"""Does the single-linkage update need more applications when gaps get finer?

Adversarial padding: take an instance and add loops (elements of rank 0, in
existing blocks) whose values fill the gaps between the real values at spacing
h.  Loops never enter a base, so Opt and Psi are unchanged, but they chain the
clusters of single linkage.  If the number of applications per stage grows as
h shrinks, the family is only pseudo-polynomial; a component-wise variant,
which clusters each connected component of M separately (loops are their own
components), is run alongside.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_matroidal_families import clusters

ZERO = Fraction(0)


def components(M):
    comp = {}
    cid = 0
    for e in range(M.m):
        if e in comp:
            continue
        if M.rank([e]) == 0:
            comp[e] = ("loop", e)
            continue
        comp[e] = cid
        for f in range(M.m):
            if f != e and f not in comp and M.rank([f]) == 1:
                # e, f on a common circuit iff r({e,f}) + r(E-{e,f}) ... use bases: some base contains
                # exactly one of them and swapping gives another base
                if any(e in B and f not in B and (B - {e}) | {f} in M.bases_set for B in M.bases):
                    comp[f] = cid
        cid += 1
    # merge transitively
    changed = True
    while changed:
        changed = False
        for e in range(M.m):
            for f in range(M.m):
                if comp[e] != comp[f] and not isinstance(comp[e], tuple) and not isinstance(comp[f], tuple):
                    if any(e in B and f not in B and (B - {e}) | {f} in M.bases_set for B in M.bases):
                        lo, hi = sorted([comp[e], comp[f]])
                        for x in comp:
                            if comp[x] == hi:
                                comp[x] = lo
                        changed = True
    return comp


def theta_family(M, v, comp=None):
    levels = sorted({ZERO} | {abs(v[e] - v[f]) for e in v for f in v})
    out = {}
    for t in levels:
        if comp is None:
            u = clusters(v, t)
        else:
            u = {}
            for c in set(comp.values()):
                part = {e: v[e] for e in v if comp[e] == c}
                lab = clusters(part, t)
                for e in part:
                    u[e] = lab[e]
        b = rp.beta(M, u)
        for B in M.bases:
            if B not in out and rp.weight(u, B) == b:
                out[B] = t
    return out


def run(M, blk, k, w, comp=None, cap=200):
    p = {b: ZERO for b in range(k)}
    worst = 0
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_family(M, v, comp)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
            used += 1
        worst = max(worst, used)
    return rp.psi(M, blk, w, p), worst


def padded(base_inst, h):
    M0, blk0, k, w0 = base_inst
    vals = sorted(set(w0.values()))
    fill = []
    for lo, hi in zip(vals, vals[1:]):
        x = lo + h
        while x < hi:
            fill.append(x)
            x += h
    m0 = M0.m
    m = m0 + len(fill)
    rank0 = M0._rank

    def rank(S):
        return rank0(frozenset(e for e in S if e < m0))
    M = rp.Matroid(m, rank)
    M.bases_set = set(M.bases)
    blk = dict(blk0)
    w = dict(w0)
    for i, x in enumerate(fill):
        blk[m0 + i] = i % k
        w[m0 + i] = x
    return M, blk, k, w


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 43
    rng = random.Random(seed)
    for trial in range(6):
        M0, blk0, k = rp.bipartite(rng) if trial % 2 == 0 else rp.rainbow_tree(rng)
        w0 = {e: Fraction(rng.randint(0, 6)) for e in range(M0.m)}
        target = rp.opt(M0, blk0, k, w0)
        row = []
        for h in [Fraction(1), Fraction(1, 2), Fraction(1, 4)]:
            M, blk, k2, w = padded((M0, blk0, k, w0), h)
            if M.m > 15:
                break
            comp = components(M)
            v1, a1 = run(M, blk, k2, w)
            v2, a2 = run(M, blk, k2, w, comp)
            row.append(f"h={h}: m={M.m} SL apps {a1} ({'ok' if v1 == target else 'WRONG'})"
                       f" | comp-SL apps {a2} ({'ok' if v2 == target else 'WRONG'})")
        print(f"instance {trial} (k={k}):", " ; ".join(row), flush=True)


if __name__ == "__main__":
    main()
