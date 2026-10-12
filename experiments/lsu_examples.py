"""Recompute the instances quoted in docs/phase2f, Section 7 (graphic, explicit data).

P1  overshoot of the least dual optimum p0
P2  the order of the remaining offsets x_j = p* - p_j flips
P3  a pair leaves its final strict order after reaching it
P4  a non-final step puts no pair (one component, different blocks, v*_e != v*_f) into
    its final order (found by a seeded search over graphic instances, printed)
P5  a pair reverses its strict order twice or more
FV  T_LS = V + 2 with V = 3 distinct weight values
Usage: python lsu_examples.py"""
import random

import stage_core as sc
import ls_core as lc
import lsu_core as uc


def sgn(z):
    return (z > 0) - (z < 0)


def run(n, edges, blk, w):
    M = sc.graphic(n, edges)
    states, blocks = uc.ls_run(M, blk, M.k, w)
    return M, states, blocks


def p1():
    edges = [(4, 1), (2, 4), (1, 3), (5, 3), (1, 3), (1, 0), (4, 3), (0, 2), (4, 2), (5, 1), (3, 5)]
    blk = [4, 1, 1, 3, 1, 2, 0, 2, 2, 1, 3]
    w = [3, 3, 4, 1, 3, 5, 0, 3, 0, 2, 1]
    M, states, blocks = run(6, edges, blk, w)
    ob = uc.opt_rainbow_base(M, blk, M.k, w)
    p0 = uc.least_dual(M, blk, M.k, w, ob[1])
    print("P1 p_j:", [s["p"] for s in states], " p0:", p0,
          " overshoot:", any(s["p"][b] > p0[b] for s in states for b in range(M.k)))


def p2():
    edges = [(2, 4), (5, 1), (1, 3), (4, 5), (2, 5), (0, 3), (4, 2), (0, 2), (2, 1)]
    blk = [4, 3, 2, 0, 0, 3, 0, 1, 0]
    w = [3699, 0, 3488, 0, 0, 0, 12331, 3989, 4]
    M, states, blocks = run(6, edges, blk, w)
    pT = states[-1]["p"]
    xs = [[pT[b] - s["p"][b] for b in range(M.k)] for s in states]
    print("P2 offsets x_j:", xs)


def pair_seq(states, e, f):
    return [(s["v"][e], s["v"][f]) for s in states]


def p3():
    edges = [(3, 4), (3, 5), (2, 0), (4, 3), (4, 5), (5, 2), (1, 2), (1, 4)]
    blk = [4, 0, 4, 2, 1, 4, 2, 3]
    w = [4, 2, 2, 1, 5, 1, 2, 4]
    M, states, blocks = run(6, edges, blk, w)
    print("P3 pair (1,7):", pair_seq(states, 1, 7), " final order sign:",
          sgn(states[-1]["v"][1] - states[-1]["v"][7]))


def p4():
    rng = random.Random(777)
    while True:
        n = rng.randint(5, 6)
        m = rng.randint(n + 2, 10)
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        M = sc.graphic(n, edges)
        k = M.k
        blk = [rng.randrange(k) for _ in range(m)]
        if len(set(blk)) < k or sc.rainbow_av(M, blk, k)[0] < k:
            continue
        w = [rng.randint(0, 9) for _ in range(m)]
        states, blocks = uc.ls_run(M, blk, k, w)
        T = len(blocks)
        vs = [s["v"] for s in states]
        vstar = vs[-1]
        fin = [(e, f) for e in range(m) for f in range(e + 1, m)
               if M.comp[e] == M.comp[f] and blk[e] != blk[f] and vstar[e] != vstar[f]]
        for j in range(T - 1):
            if not any(sgn(vs[j][e] - vs[j][f]) != sgn(vstar[e] - vstar[f]) and
                       sgn(vs[j + 1][e] - vs[j + 1][f]) == sgn(vstar[e] - vstar[f]) for (e, f) in fin):
                print("P4 graphic n =", n, "edges", edges, "blocks", blk, "w", w, "step", j, "of", T)
                print("   v_j:", vs[j], " v_{j+1}:", vs[j + 1], " v*:", vstar)
                return


def p5():
    edges = [(3, 5), (4, 2), (3, 4), (1, 2), (3, 0), (0, 3), (4, 0), (4, 0), (2, 0), (4, 1), (5, 4), (5, 1)]
    blk = [2, 0, 0, 2, 0, 1, 4, 0, 3, 4, 3, 0]
    w = [4194, 7358, 3348, 6542, 3996, 9295, 3982, 6300, 4454, 3680, 606, 2679]
    M, states, blocks = run(6, edges, blk, w)
    print("P5 pair (0,9):", pair_seq(states, 0, 9))


def fv():
    edges = [(3, 6), (0, 3), (6, 0), (5, 2), (4, 3), (6, 4), (4, 2), (4, 3), (1, 0), (1, 0), (2, 0), (1, 2)]
    blk = [0, 3, 4, 5, 0, 1, 1, 2, 5, 5, 2, 2]
    w = [654984, 1025592, 1025592, 654984, 882058, 882058, 1025592, 1025592, 1025592, 882058, 654984, 1025592]
    M = sc.graphic(7, edges)
    T, vl, nus, mono = lc.ls_iterate(M, blk, M.k, w)
    print("FV k =", M.k, "V =", len(set(w)), "T_LS =", T, "nu0:", nus,
          "Psi=Opt:", sc.psi_from_v(M, blk, M.k, w, vl) == sc.opt_rainbow(M, blk, M.k, w))


if __name__ == "__main__":
    p1()
    p2()
    p3()
    p4()
    p5()
    fv()
