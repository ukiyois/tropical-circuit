"""Applications per stage for three matroidal families on adversarial inputs.

Families (all contain the possibly-optimal bases, so every update is valid):
  comp-SL : single linkage inside each connected component;
  element : merge [v_e, v_f] for e, f in one component, 0 < v_f - v_e <= t,
            f possibly optimal (computable from the threshold relation);
  exact   : merge only exchange pairs of possibly optimal bases (brute force).
Inputs: one connected component with many elements and finely spaced values
(uniform U_{k,m}, binary matroids with many parallel-ish columns, and graphic
multigraphs), where interval merging drags many bystanders.
Reported per family: optimal runs, the largest number of applications in a
stage minus (r+1), and the largest ratio of applications to r+1.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map
from rainbow_rpim import components, exchange_pairs, theta_rpim
from rainbow_matroidal_families import clusters

ZERO = Fraction(0)


def theta_compsl(M, v, comp):
    levels = sorted({ZERO} | {abs(v[e] - v[f]) for e in v for f in v})
    out = {}
    for t in levels:
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


def run(M, blk, k, w, kind, comp, pairs, cap=60):
    p = {b: ZERO for b in range(k)}
    excess, ratio = 0, Fraction(0)
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            if kind == "comp-SL":
                th = theta_compsl(M, v, comp)
            else:
                th = theta_rpim(M, v, comp, theta_map(M, v), pairs, kind)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            p = {b: p[b] + res[0][b] for b in range(k)}
            used += 1
        excess = max(excess, used - (r + 1))
        ratio = max(ratio, Fraction(used, r + 1))
    return rp.psi(M, blk, w, p), excess, ratio


def uniform_fine(rng):
    k = rng.randint(2, 4)
    m = rng.randint(k + 4, 11)
    blk = {e: (e if e < k else rng.randrange(k)) for e in range(m)}
    M = rp.Matroid(m, lambda S, k=k: min(len(S), k))
    vals = rng.sample(range(0, 4 * m), m)
    w = {e: Fraction(vals[e], 4) for e in range(m)}
    return M, blk, k, w


def binary_dense(rng):
    while True:
        k = rng.randint(3, 4)
        m = rng.randint(k + 4, 11)
        cols = [rng.randrange(1, 1 << k) for _ in range(m)]
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(m)}
        M = rp.Matroid(m, rp.gf2_rank_fn(cols))
        if M.k == k and rp.opt(M, blk, k, {e: 0 for e in range(m)}) is not None:
            w = {e: Fraction(rng.randint(0, 4 * m), 4) for e in range(m)}
            return M, blk, k, w


def graphic_multi(rng):
    while True:
        n = rng.randint(4, 5)
        k = n - 1
        edges = [tuple(sorted(rng.sample(range(n), 2))) for _ in range(rng.randint(k + 4, 11))]
        blk = {e: (e if e < k else rng.randrange(k)) for e in range(len(edges))}
        M = rp.Matroid(len(edges), rp.graphic_rank_fn(n, edges))
        if M.k == k and rp.opt(M, blk, k, {e: 0 for e in range(len(edges))}) is not None:
            w = {e: Fraction(rng.randint(0, 4 * len(edges)), 4) for e in range(len(edges))}
            return M, blk, k, w


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    rng = random.Random(seed)
    for name, gen in [("uniform fine", uniform_fine), ("binary dense", binary_dense),
                      ("graphic multi", graphic_multi)]:
        insts = [gen(rng) for _ in range(trials)]
        for kind in ("comp-SL", "element", "exact"):
            ok, worst_ex, worst_ratio = 0, 0, Fraction(0)
            for M, blk, k, w in insts:
                comp = components(M)
                pairs = {B: exchange_pairs(M, B) for B in M.bases} if kind == "exact" else None
                val, ex, ratio = run(M, blk, k, w, kind, comp, pairs)
                ok += (val == rp.opt(M, blk, k, w))
                worst_ex = max(worst_ex, ex)
                worst_ratio = max(worst_ratio, ratio)
            print(f"{name:14s} {kind:8s} optimal {ok}/{trials}  max(apps - (r+1)) {worst_ex}  "
                  f"max apps/(r+1) {float(worst_ratio):.2f}", flush=True)


if __name__ == "__main__":
    main()
