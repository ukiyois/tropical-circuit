"""Direct check of Proposition 4.1(2): N_{v_j}(t) = N'_{x_j}(t) for 0 <= t <= G_j.

Along LS runs (as in lsu_local.py), at every state with 2 G_j < gamma ("local") and every
level t <= G_j of v_j (the families are constant between levels), compare nu and Av of
the two matroids and the ranks of 16 random subsets of E.
False variant LOC2_F: the same comparison at states with 2 G_j >= gamma (non-local), for
levels t <= G_j; it must fail somewhere.
Usage: python lsu_local2.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc
from lsu_local import make_family, Wrap


def compare(M, Mp, fam, blk, k, v, xv, t, rng):
    N = sc.posl(M, v, t)
    Np = fam(Mp, xv, t)
    a = sc.rainbow_av(N, blk, k)[:2]
    b = sc.rainbow_av(Wrap(Np), blk, k)[:2]
    if a != b:
        return False
    for _ in range(16):
        S = rng.getrandbits(M.m)
        if N.rank(S) != Np.rank(S):
            return False
    return True


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "loc_levels": 0, "LOC2": 0, "nonloc_levels": 0, "LOC2_F": 0}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=6, mmax=10)
        states, blocks = uc.ls_run(M, blk, k, w, cap=300)
        if not blocks:
            continue
        st["runs"] += 1
        opt = sc.opt_rainbow(M, blk, k, w)
        pT = states[-1]["p"]
        vstar = states[-1]["v"]
        m = M.m
        gaps = [abs(vstar[e] - vstar[f]) for e in range(m) for f in range(m)
                if M.comp[e] == M.comp[f] and vstar[e] != vstar[f]]
        gamma = min(gaps) if gaps else None
        Mp = Wrap(sc.MinBase(M, vstar))
        fam = make_family([(M.comp[e], vstar[e]) for e in range(m)])
        for j, s in enumerate(states[:-1]):
            G = opt - (sum(s["p"]) + sc.beta(M, s["v"]))
            x = [pT[b] - s["p"][b] for b in range(k)]
            xv = [x[blk[e]] for e in range(m)]
            local = gamma is None or 2 * G < gamma
            for t in sc.levels_of(s["v"]):
                if t > G:
                    break
                ok = compare(M, Mp, fam, blk, k, s["v"], xv, t, rng)
                if local:
                    st["loc_levels"] += 1
                    if not ok:
                        st["LOC2"] += 1
                        ex.setdefault("LOC2", (uc.describe(M), blk, w, j, t))
                else:
                    st["nonloc_levels"] += 1
                    st["LOC2_F"] += not ok
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
