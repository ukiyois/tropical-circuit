"""Phase 2a: which filtration of bases makes the threshold-integral update work?

Same setting as rainbow_prototype.py (partition matroid of blocks + matroid M,
Lagrangian Psi(p) = sum p + beta(w - p[blk])).  A filtration assigns to every
base B of M an entry level theta(B) >= 0, with theta(B) = 0 exactly for the
v-optimal bases, and the update is

  tau   = min { theta(B) : B meets >= r+1 blocks }
  lam_b = min { theta(B) : B meets >= r blocks other than b }
  a_b   = (tau - lam_b)_+ ,   p <- p + a.

Filtrations compared:
  closure  theta(B) = max_{e in B} rho_e if B is vhat-optimal, else inf
           (the restriction family M^vhat | {rho <= t} of rainbow_prototype.py)
  local    theta(B) = max { v_f - v_e : e notin B, f in C(B, e) }_+
           (B is t-locally optimal: no single exchange gains more than t)
  excess   theta(B) = v(B) - beta(v)

For bipartite matching all three coincide with the threshold graphs {D <= t}.
"""
import itertools
import random
import sys
from fractions import Fraction

import rainbow_prototype as rp

ZERO = Fraction(0)
INF = rp.INF


def fundamental_circuit(M, B, e):
    """C(B, e): the f in B with B - f + e a base, together with e."""
    return [f for f in B if M.rank((B - {f}) | {e}) == M.k]


def thetas(M, blk, v, kind):
    b0 = rp.beta(M, v)
    out = []
    if kind == "closure":
        rho, entries = rp.reduced(M, blk, v)
        lvl = {B: thr for thr, S, B in entries}
        for B in M.bases:
            out.append((lvl.get(B, INF), frozenset(blk[e] for e in B)))
    elif kind == "local":
        for B in M.bases:
            th = ZERO
            for e in range(M.m):
                if e in B or M.rank([e]) == 0:
                    continue
                for f in fundamental_circuit(M, B, e):
                    th = max(th, v[f] - v[e])
            out.append((th, frozenset(blk[e] for e in B)))
    elif kind == "excess":
        for B in M.bases:
            out.append((rp.weight(v, B) - b0, frozenset(blk[e] for e in B)))
    return out


def update(entries, k, r):
    nu0 = max(len(S) for th, S in entries if th == 0)
    if nu0 != r:
        return None
    big = [th for th, S in entries if len(S) >= r + 1]
    tau = min(big) if big else INF
    if tau == INF:
        return None
    a = {}
    for b in range(k):
        c = [th for th, S in entries if len(S - {b}) >= r]
        lam = min(c) if c else INF
        a[b] = max(tau - lam, ZERO) if lam != INF else ZERO
    return a, tau


def run(M, blk, k, w, kind, cap=30):
    p = {b: ZERO for b in range(k)}
    last = rp.psi(M, blk, w, p)
    st = {"apps": [], "eq": 0, "gt": 0, "lt": 0, "dec": 0, "stall": False, "dead": False}
    for r in range(k):
        used = 0
        while used < cap:
            v = {e: w[e] - p[blk[e]] for e in range(M.m)}
            res = update(thetas(M, blk, v, kind), k, r)
            if res is None:
                break
            a, tau = res
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            cur = rp.psi(M, blk, w, p)
            gain, target = cur - last, (k - r) * tau
            st["eq" if gain == target else ("gt" if gain > target else "lt")] += 1
            st["dec"] += (gain < 0)
            last = cur
        st["stall"] |= (used == cap)
        st["apps"].append(used)
    return last, p, st


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    fams = [("bipartite", rp.bipartite), ("arborescence", rp.arborescence),
            ("rainbow tree", rp.rainbow_tree), ("binary", rp.binary_rainbow)]
    kinds = ["closure", "local", "excess"]
    for name, fam in fams:
        inst = []
        for _ in range(trials):
            M, blk, k = fam(rng)
            inst.append((M, blk, k, rp.random_weights(rng, M.m)))
        for kind in kinds:
            ok = 0
            agg = {"eq": 0, "gt": 0, "lt": 0, "dec": 0, "stall": 0}
            worst = 0
            ex = None
            for M, blk, k, w in inst:
                val, p, st = run(M, blk, k, w, kind)
                target = rp.opt(M, blk, k, w)
                ok += (val == target)
                for key in ("eq", "gt", "lt", "dec"):
                    agg[key] += st[key]
                agg["stall"] += st["stall"]
                worst = max(worst, max(st["apps"]))
                if val != target and ex is None:
                    ex = (k, st["apps"], str(val), str(target))
            print(f"{name:13s} {kind:8s} optimal {ok:4d}/{trials}  gain =,>,< (k-r)tau "
                  f"{agg['eq']},{agg['gt']},{agg['lt']}  Psi drops {agg['dec']}  "
                  f"stalls {agg['stall']}  max apps/stage {worst}  first fail {ex}")
        print()


if __name__ == "__main__":
    main()
