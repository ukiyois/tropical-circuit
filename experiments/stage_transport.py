"""B1 prototype: capacitated transportation as a rainbow problem, PO-SL schedule.

Sources i with supply a_i, sinks j with demand b_j, edges (i,j) with capacity
c_ij and cost w_ij, sum a = sum b = F.  Ground set: elements (i, j, s), one for
every edge (i,j) and every slot s = 1..a_i of source i; the block of (i,j,s) is
the slot (i,s), so k = F.  M is the laminar matroid
    |X cap {(i,j,s) : s}| <= c_ij,     |X cap {(i,j,s) : i, s}| <= b_j.
Rainbow bases of M are the integral feasible flows (with the slots labelled),
and Opt is the minimum cost of a flow.  The slots of a source are
interchangeable, so the PO-SL potentials stay equal on them.

Measured, for capacities scaled by U: the stage lengths of the static schedule,
the number of stages with at least one update (active stages), the total number
of updates, and the value against a direct min-cost-flow computation.
Usage: python stage_transport.py [seed] [Umax]
"""
import itertools
import random
import sys

import stage_core as sc


def build(a, b, cap, w):
    """cap, w: dicts (i,j) -> value.  Returns (M, blk, k, weights, elements)."""
    elems = []
    for (i, j) in sorted(cap):
        for s in range(a[i]):
            elems.append((i, j, s))
    slot_index = {}
    for i in range(len(a)):
        for s in range(a[i]):
            slot_index[(i, s)] = len(slot_index)
    blk = [slot_index[(i, s)] for (i, j, s) in elems]
    edge_of = [(i, j) for (i, j, s) in elems]
    sink_of = [j for (i, j, s) in elems]
    edges = sorted(cap)

    def rank(S):
        per_edge = {}
        per_sink = {}
        for e in sc.bits(S):
            per_edge[edge_of[e]] = per_edge.get(edge_of[e], 0) + 1
        for (i, j), c in per_edge.items():
            per_sink[j] = per_sink.get(j, 0) + min(c, cap[(i, j)])
        return sum(min(x, b[j]) for j, x in per_sink.items())
    M = sc.Matroid(len(elems), rank, "laminar")
    weights = [w[edge_of[e]] for e in range(len(elems))]
    return M, blk, len(slot_index), weights, elems


def min_cost_flow(a, b, cap, w):
    """Successive shortest paths (Bellman-Ford), exact integers.  Returns the cost."""
    p, q = len(a), len(b)
    n = p + q + 2
    S, T = p + q, p + q + 1
    graph = []

    def add(u, v, c, cost):
        graph.append([u, v, c, cost])
        graph.append([v, u, 0, -cost])
    for i in range(p):
        add(S, i, a[i], 0)
    for j in range(q):
        add(p + j, T, b[j], 0)
    for (i, j), c in cap.items():
        add(i, p + j, c, w[(i, j)])
    flow, cost = 0, 0
    F = sum(a)
    while flow < F:
        dist = [None] * n
        dist[S] = 0
        prev = [None] * n
        for _ in range(n):
            changed = False
            for idx, (u, v, c, cst) in enumerate(graph):
                if c > 0 and dist[u] is not None and (dist[v] is None or dist[u] + cst < dist[v]):
                    dist[v] = dist[u] + cst
                    prev[v] = idx
                    changed = True
            if not changed:
                break
        if dist[T] is None:
            return None
        push, v = F - flow, T
        while v != S:
            idx = prev[v]
            push = min(push, graph[idx][2])
            v = graph[idx][0]
        v = T
        while v != S:
            idx = prev[v]
            graph[idx][2] -= push
            graph[idx ^ 1][2] += push
            v = graph[idx][0]
        flow += push
        cost += push * dist[T]
    return cost


def schedule(M, blk, k, w):
    v = list(w)
    lens = []
    nu0, _ = sc.state(M, blk, k, v)
    start = nu0
    for r in range(1, k):
        if nu0 > r:
            lens.append(0)
            continue
        c, v = sc.run_stage(M, blk, k, v, r)
        lens.append(c)
        nu0, _ = sc.state(M, blk, k, v)
    return lens, v, start


def random_instance(rng, p=3, q=3, cmax=2, wmax=20):
    while True:
        a = [rng.randint(1, 2) for _ in range(p)]
        F = sum(a)
        b = [1] * q
        for _ in range(F - q):
            b[rng.randrange(q)] += 1
        cap = {(i, j): rng.randint(1, cmax) for i in range(p) for j in range(q)}
        w = {(i, j): rng.randint(0, wmax) for i in range(p) for j in range(q)}
        if min_cost_flow(a, b, cap, w) is not None:
            return a, b, cap, w


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    Umax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rng = random.Random(seed)
    a, b, cap, w = random_instance(rng)
    print("base instance: a", a, "b", b, "cap", cap, "w", w)
    for U in range(1, Umax + 1):
        aU, bU = [x * U for x in a], [x * U for x in b]
        capU = {e: c * U for e, c in cap.items()}
        M, blk, k, ww, elems = build(aU, bU, capU, w)
        lens, v, start = schedule(M, blk, k, ww)
        psi = sc.psi_from_v(M, blk, k, ww, v)
        opt = min_cost_flow(aU, bU, capU, w)
        active = sum(1 for x in lens if x > 0)
        print(f"U={U}: F={k} m={M.m} nu0(w)={start} max stage {max(lens)} active stages {active} "
              f"total updates {sum(lens)}  Psi={psi} Opt={opt}  lens(active)={[x for x in lens if x]}", flush=True)


if __name__ == "__main__":
    main()
