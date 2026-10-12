"""Search for a run in which every block is raised at some step (min_b p*_b > 0).
Graphic matroids that are disjoint unions of two graphs on 4 vertices (the class in
which lsu_observe.py found one such run), weights as in lsu_core.rand_instance.
Prints the first instance found with its trace.  Usage: python lsu_o2_search.py workers seconds"""
import random, sys, time
from multiprocessing import Pool
import stage_core as sc
import lsu_core as uc
import lsu_trace as tr
from ls_mono_random import has_rainbow_base
from ls_search_drop import rweights

def work(args):
    seed, budget = args
    rng = random.Random(seed); t0 = time.time(); runs = 0
    while time.time() - t0 < budget:
        ea = [tuple(rng.sample(range(4), 2)) for _ in range(rng.randint(4, 6))]
        eb = [tuple(x + 4 for x in rng.sample(range(4), 2)) for _ in range(rng.randint(4, 6))]
        M = sc.graphic(8, ea + eb); k = M.k
        if k < 3: continue
        blk = [rng.randrange(k) for _ in range(M.m)]
        if len(set(blk)) < k or not has_rainbow_base(M, blk, k): continue
        w = rweights(rng, M.m)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        runs += 1
        if blocks and min(states[-1]["p"]) > 0:
            return (runs, (ea + eb, blk, w, [s["p"] for s in states], [b["a"] for b in blocks]))
    return (runs, None)

if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(work, [(13000 + s, budget) for s in range(workers)])
    print("runs", sum(r for r, _ in res))
    for r, inst in res:
        if inst:
            edges, blk, w, ps, As = inst
            print("FOUND edges", edges, "blk", blk, "w", w)
            print("  p_j:", ps); print("  a_j:", As)
            M = sc.graphic(8, edges)
            tr.print_trace(tr.trace(M, blk, M.k, w))
            break
