"""The Koenig property at the raised set (Theorem 2.6 of the phase2b note).

Lemma (colored exchange cycle).  Let P, Q be bases of a matroid with P, Q
disjoint after contracting their intersection, and colour the elements R / U
with |Q cap R| > |P cap R| on the symmetric difference.  In the digraph with
arcs p -> q when Q - q + p is a base (q in C(Q, p)) and q -> p when P - p + q is
a base (p in C(P, q)), restricted to (P - Q) cap U  and  (Q - P) cap R, there is
a directed cycle.

Theorem.  At a state with nu0 = r, S = S0, R = E_S, rho = |S| - (k - r), and B*
a minimum base meeting r blocks: every base B with |B cap R| > rho has
theta(B) >= D.

This script checks the lemma on all pairs of bases and all colourings of the
symmetric difference for small matroids (and the symmetric-exchange version,
which fails), and the theorem at random states.
Usage: python stage_konig.py
"""
import itertools
import random

import stage_core as sc


def has_cycle(nodes, arcs):
    color = {x: 0 for x in nodes}

    def dfs(x):
        color[x] = 1
        for y in arcs.get(x, ()):
            if y not in color:
                continue
            if color[y] == 1:
                return True
            if color[y] == 0 and dfs(y):
                return True
        color[x] = 2
        return False
    return any(color[x] == 0 and dfs(x) for x in nodes)


def lemma_check(M, max_pairs=400, rng=None):
    bases = sc.all_bases(M)
    pairs = [(P, Q) for P in bases for Q in bases if P != Q]
    if rng is not None and len(pairs) > max_pairs:
        pairs = rng.sample(pairs, max_pairs)
    stats = {"cases": 0, "cycle_fail": 0, "symexch_fail": 0}
    for P, Q in pairs:
        Pm, Qm = P & ~Q, Q & ~P
        sym = sc.bits(Pm | Qm)
        bArc = {p: [q for q in sc.bits(Qm) if M.rank((Q & ~(1 << q)) | (1 << p)) == M.k] for p in sc.bits(Pm)}
        sArc = {q: [p for p in sc.bits(Pm) if M.rank((P & ~(1 << p)) | (1 << q)) == M.k] for q in sc.bits(Qm)}
        for colours in itertools.product((0, 1), repeat=len(sym)):
            Rset = {x for x, c in zip(sym, colours) if c}
            if len([q for q in sc.bits(Qm) if q in Rset]) <= len([p for p in sc.bits(Pm) if p in Rset]):
                continue
            stats["cases"] += 1
            PU = [p for p in sc.bits(Pm) if p not in Rset]
            QR = [q for q in sc.bits(Qm) if q in Rset]
            nodes = set(PU) | set(QR)
            arcs = {p: [q for q in bArc[p] if q in Rset] for p in PU}
            arcs.update({q: [p for p in sArc[q] if p not in Rset] for q in QR})
            if not has_cycle(nodes, arcs):
                stats["cycle_fail"] += 1
            if not any(q in bArc[p] and p in sArc[q] for p in PU for q in QR):
                stats["symexch_fail"] += 1
    return stats


def theorem_check(rng, trials=3000):
    from stage_forced import analyse
    from stage_forced_random import rand_inst
    st = {"states": 0, "bases": 0, "fail": 0}
    for _ in range(trials // 20):
        kind, M = rand_inst(rng)
        k = M.k
        bases = sc.all_bases(M)
        for _ in range(20):
            blk = [i if i < k else rng.randrange(k) for i in range(M.m)]
            rng.shuffle(blk)
            if not any(len({blk[e] for e in sc.bits(B)}) == k for B in bases):
                continue
            v = [rng.randint(0, 6) for _ in range(M.m)]
            res = analyse(M, bases, blk, k, v)
            if res is None:
                continue
            r, S0, D, tauP = res
            Rm = sc.mask_of(e for e in range(M.m) if blk[e] in S0)
            rho = len(S0) - (k - r)
            st["states"] += 1
            for B in bases:
                if sc.popcount(B & Rm) > rho:
                    st["bases"] += 1
                    if sc.theta(M, v, B) < D:
                        st["fail"] += 1
    return st


if __name__ == "__main__":
    rng = random.Random(7)
    K4 = sc.graphic(4, [(1, 2), (2, 3), (3, 4 - 1), (1, 3), (1, 4 - 1), (2, 4 - 1)])
    zoo = [("MK4", sc.graphic(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])),
           ("U24", sc.uniform(2, 4)), ("U36", sc.uniform(3, 6)), ("U37", sc.uniform(3, 7)),
           ("F7", sc.gf2([1, 2, 4, 3, 5, 6, 7])), ("F7dual", sc.gf2([0b0111, 0b1011, 0b1101, 0b1110, 1, 2, 4])),
           ("K5-e", sc.graphic(5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)])),
           ("W4", sc.graphic(5, [(0, 1), (1, 2), (2, 3), (3, 0), (4, 0), (4, 1), (4, 2), (4, 3)]))]
    for name, M in zoo:
        print(name, "m", M.m, "k", M.k, lemma_check(M, rng=rng), flush=True)
    print("theorem at random states:", theorem_check(rng))
