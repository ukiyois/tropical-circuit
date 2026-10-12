"""Explicit small witnesses.
 1. U_{1,3}, v = (0,0,1): PO with '<=' and single linkage with '< t' both break (F1).
 2. M(K4): smallest-weight item-3 application (nu0 stays r, S unchanged), with
    the Step 3/4 witnesses, showing C grows only through the non-strict pair.
 3. M(K4): an item-3 application where the STRICT version of C does not grow.
 4. lam_b read as 'a base meeting AT MOST r blocks avoids b' breaks the gain.
"""
import itertools
from core import *
from test_readings import N_variant, lam_atmost
from exhaustive import rgs


def show_v(v):
    return [str(x) for x in v]


def ex1():
    M = uniform(1, 3)
    v = [Fraction(0), Fraction(0), Fraction(1)]
    N0 = opt_bases(M, v)[0]
    a = N_variant(M, v, F0, weak_po=True)
    b = N_variant(M, v, F0, strict_link=True)
    print("1. U_{1,3}, v=(0,0,1): N0 =", sorted(map(elems, N0)),
          "| PO with <= gives N(0) =", sorted(map(elems, a)),
          "| linkage '< t' gives N(0) =", sorted(map(elems, b)), "| as written:", sorted(map(elems, N_posl(M, v, F0))))


def cross(blk, v, S, m, strict=False):
    ES = [e for e in range(m) if blk[e] in S]
    rest = [e for e in range(m) if blk[e] not in S]
    if strict:
        return {(y, g) for y in ES for g in rest if v[y] < v[g]}
    return {(y, g) for y in ES for g in rest if v[y] <= v[g]}


def ex23():
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    M = graphic(4, edges)
    k = M.k
    best = None
    strict_ex = None
    for blk in rgs(6, 3):
        if not has_rainbow(M, blk, k):
            continue
        for vv in itertools.product(range(4), repeat=6):
            if min(vv) != 0:
                continue
            v = [Fraction(x) for x in vv]
            N0, _ = opt_bases(M, v)
            r = nu_of(N0, blk)
            if r >= k:
                continue
            tau, lam, a, _ = posl_update(M, blk, k, v, r)
            v2 = [v[e] - a[blk[e]] for e in range(M.m)]
            N0b, _ = opt_bases(M, v2)
            S, _ = avoidable(N0, blk, k)
            if nu_of(N0b, blk) != r or avoidable(N0b, blk, k)[0] != S:
                continue
            key = (sum(vv), vv)
            if best is None or key < best[0]:
                best = (key, blk, v, r, tau, a, v2, S)
            if strict_ex is None and not cross(blk, v, S, 6, True) < cross(blk, v2, S, 6, True):
                strict_ex = (blk, v, r, tau, a, v2, S)
    _, blk, v, r, tau, a, v2, S = best
    print("2. M(K4) edges", edges)
    print("   blocks", blk, " v", show_v(v), " r", r, " S", sorted(S), " tau", tau,
          " a", {b: str(x) for b, x in a.items()}, " v'", show_v(v2))
    C0, C1 = cross(blk, v, S, 6), cross(blk, v2, S, 6)
    print("   N0(v)  =", sorted(map(elems, opt_bases(M, v)[0])))
    print("   N0(v') =", sorted(map(elems, opt_bases(M, v2)[0])))
    print("   C(v,S) =", sorted(C0), " C(v',S) =", sorted(C1), " new:", sorted(C1 - C0))
    if strict_ex:
        blk, v, r, tau, a, v2, S = strict_ex
        C0s, C1s = cross(blk, v, S, 6, True), cross(blk, v2, S, 6, True)
        C0, C1 = cross(blk, v, S, 6), cross(blk, v2, S, 6)
        print("3. strict C fails: blocks", blk, " v", show_v(v), " r", r, " S", sorted(S), " tau", tau,
              " a", {b: str(x) for b, x in a.items()}, " v'", show_v(v2))
        print("   strict: C(v,S) =", sorted(C0s), " C(v',S) =", sorted(C1s),
              "| non-strict new pairs:", sorted(C1 - C0))


def ex4():
    import random
    rng = random.Random(11)
    best = None
    for k in (2, 3):
        for m in range(k + 1, 7):
            M = uniform(k, m)
            for blk in rgs(m, k):
                if not has_rainbow(M, blk, k):
                    continue
                for vv in itertools.product(range(3), repeat=m):
                    if min(vv) != 0:
                        continue
                    v = [Fraction(x) for x in vv]
                    N0, _ = opt_bases(M, v)
                    r = nu_of(N0, blk)
                    if r >= k:
                        continue
                    tau2, a2 = lam_atmost(M, blk, k, v, r)
                    v3 = [v[e] - a2[blk[e]] for e in range(m)]
                    gain = sum(a2.values(), F0) + beta(M, v3) - beta(M, v)
                    if gain != (k - r) * tau2:
                        tau, lam, a, _ = posl_update(M, blk, k, v, r)
                        print(f"4. U_{{{k},{m}}} blocks {blk} v {show_v(v)} r {r}: 'at most r' reading gives "
                              f"a={ {b: str(x) for b, x in a2.items()} }, gain {gain} != (k-r)tau = {(k - r) * tau2};"
                              f" as written a={ {b: str(x) for b, x in a.items()} }")
                        return


if __name__ == "__main__":
    ex1()
    ex23()
    ex4()
