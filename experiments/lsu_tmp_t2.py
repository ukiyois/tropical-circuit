import random
import stage_core as sc, ls_core as lc, lsu_trace as tr, lsu_core as uc
from ls_mono_random import sparse_paving
# reproduce H2 example by searching with same generator seeds is hard; build a fresh search for H2 failures
from lsu_blockconst import rand_x
rng = random.Random(5000)
found = 0
while found < 2:
    kind, M, blk, k, w0 = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
    x = rand_x(rng, k)
    w = [x[blk[e]] for e in range(M.m)]
    states, blocks = uc.ls_run(M, blk, k, w, cap=400)
    T = len(blocks)
    xs = [[x[b]-s["p"][b] for b in range(k)] for s in states]
    bad = [j for j in range(T-1) if len(set(xs[j+1])) >= len(set(xs[j]))]
    if bad and M.ncomp == 1 and T >= 3:
        found += 1
        print("instance", uc.describe(M), "blk", blk, "x", x, "k", k, "m", M.m, "T", T)
        for j, s in enumerate(xs): print("   x", j, s, "nu", states[j]["nu"], "S0", sorted(states[j]["S0"]))
        t = tr.trace(M, blk, k, w); tr.print_trace(t)
