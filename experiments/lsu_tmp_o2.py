import random
import lsu_core as uc, lsu_trace as tr, stage_core as sc
from ls_search_drop import rmat
# regenerate: find the sum instance by scanning seeds 12000..12003 with the same generator
target_blk = [3, 2, 4, 2, 1, 3, 2, 0, 3, 4, 0, 1]
target_w = [32, 129, 22, 128, 66, 129, 74, 64, 0, 0, 128, 2]
for seed in range(12000, 12004):
    rng = random.Random(seed)
    for it in range(400000):
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        if blk == target_blk and w == target_w:
            print("found seed", seed, "iter", it, "k", k, "m", M.m, "ncomp", M.ncomp, "comp", M.comp)
            t = tr.trace(M, blk, k, w); tr.print_trace(t)
            states, blocks = uc.ls_run(M, blk, k, w)
            print("p_T", states[-1]["p"])
            raise SystemExit
