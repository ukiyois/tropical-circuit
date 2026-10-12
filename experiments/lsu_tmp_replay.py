import random, sys, time
from multiprocessing import Pool
import lsu_core as uc
import stage_core as sc
target_blk = [3, 2, 4, 2, 1, 3, 2, 0, 3, 4, 0, 1]
target_w = [32, 129, 22, 128, 66, 129, 74, 64, 0, 0, 128, 2]

# monkeypatch direct_sum to record parts
orig = sc.direct_sum
def ds(M1, M2):
    M = orig(M1, M2); M.parts = (getattr(M1, 'edges', None), getattr(M2, 'edges', None), M1.m, M2.m, getattr(M1,'name',''), getattr(M2,'name',''))
    return M
sc.direct_sum = ds
import ls_search_drop, ls_mono_random
ls_search_drop.sc.direct_sum = ds
ls_mono_random.sc.direct_sum = ds

def work(seed):
    rng = random.Random(seed); t0 = time.time()
    for it in range(80000):
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        if blk == target_blk and w == target_w:
            return (seed, it, getattr(M, 'parts', None))
        if time.time() - t0 > 280: return (seed, it, 'timeout')
    return (seed, None, None)

if __name__ == "__main__":
    with Pool(4) as pool: print(pool.map(work, range(12000, 12004)))
