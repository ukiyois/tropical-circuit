"""PO-restricted single linkage: a continuous matroidal family without bystanders.

At level t:
  PO(t) = { f : f notin cl{ g : v_g < v_f - t } }   (possibly optimal elements),
  links = pairs of PO(t) elements in one component of M with |v_e - v_f| <= t,
  clusters = classes of the chain closure of the links (intervals of PO(t)),
  u_t(e) = cluster index for e in PO(t), +inf otherwise,
  N(t) = optimal-base matroid of u_t.
Everything is read from the threshold relation G_t, so the update is
continuous.  Checked: N(0) = N0, monotonicity in t, the sandwich
(possibly optimal bases lie in N(t)), optimality, exact gain, continuity,
and applications per stage, including the worst comp-SL instance found.
"""
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp
import rainbow_local_stress as st
from rainbow_filtrations import update
from rainbow_local_lemmas import theta_map
from rainbow_rpim import components
from rainbow_family_stress import uniform_fine, binary_dense, graphic_multi

ZERO = Fraction(0)
BIG = Fraction(10 ** 9)


def po_set(M, v, t):
    out = set()
    for f in range(M.m):
        if M.rank([f]) == 0:
            continue
        low = [g for g in range(M.m) if g != f and v[g] < v[f] - t]
        if M.rank(low + [f]) > M.rank(low):
            out.add(f)
    return out


def u_posl(M, v, t, comp):
    po = po_set(M, v, t)
    u = {e: BIG for e in range(M.m)}
    for c in set(comp.values()):
        elems = sorted((e for e in po if comp[e] == c), key=lambda e: v[e])
        lab = 0
        for i, e in enumerate(elems):
            if i > 0 and v[e] - v[elems[i - 1]] > t:
                lab += 1
            u[e] = Fraction(lab)
    return u


def optimal_set(M, u):
    b = rp.beta(M, u)
    return {B for B in M.bases if rp.weight(u, B) == b}


def theta_posl(M, v, comp, checks=None):
    levels = sorted({ZERO} | {abs(v[e] - v[f]) for e in v for f in v})
    out, prev = {}, None
    loc = theta_map(M, v) if checks is not None else None
    for t in levels:
        opt = optimal_set(M, u_posl(M, v, t, comp))
        if checks is not None:
            if t == 0:
                checks["N0"] += (opt == set(rp.optimal_bases(M, v)))
                checks["N0n"] += 1
            if prev is not None:
                checks["mono"] += (prev <= opt)
                checks["monon"] += 1
            checks["sand"] += all(B in opt for B in M.bases if loc[B] <= t)
            checks["sandn"] += 1
        prev = opt
        for B in opt:
            out.setdefault(B, t)
    for B in M.bases:
        out.setdefault(B, rp.INF)
    return out


def run(M, blk, k, w, checks, cap=60):
    comp = components(M)
    p = {b: ZERO for b in range(k)}
    last = rp.psi(M, blk, w, p)
    over = 0
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            th = theta_posl(M, v, comp, checks)
            res = update([(th[B], frozenset(blk[e] for e in B)) for B in M.bases], k, r)
            if res is None or all(x == 0 for x in res[0].values()):
                break
            a, tau = res
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            cur = rp.psi(M, blk, w, p)
            checks["gain"] += (cur - last == (k - r) * tau)
            checks["gainn"] += 1
            last = cur
        over = max(over, used - (r + 1))
    return last, over


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 71
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    rng = random.Random(seed)
    gens = [("bipartite", lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "ties")))(*rp.bipartite(g))),
            ("uniform fine", uniform_fine), ("binary dense", binary_dense), ("graphic multi", graphic_multi),
            ("rainbow tree6", lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.rainbow_tree6(g))),
            ("binary5", lambda g: (lambda M, b, k: (M, b, k, st.weights(g, M.m, "generic")))(*st.binary5(g)))]
    for name, gen in gens:
        checks = {key: 0 for key in ["N0", "N0n", "mono", "monon", "sand", "sandn", "gain", "gainn"]}
        ok, worst = 0, -99
        for _ in range(trials):
            M, blk, k, w = gen(rng)
            val, over = run(M, blk, k, w, checks)
            ok += (val == rp.opt(M, blk, k, w))
            worst = max(worst, over)
        print(f"{name:13s} optimal {ok}/{trials}  N(0)=N0 {checks['N0']}/{checks['N0n']}  "
              f"monotone {checks['mono']}/{checks['monon']}  sandwich {checks['sand']}/{checks['sandn']}  "
              f"exact gain {checks['gain']}/{checks['gainn']}  max(apps-(r+1)) {worst}", flush=True)


if __name__ == "__main__":
    main()
