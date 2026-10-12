"""Theorem 1 check (k = 3): T_LS <= m, and T_LS <= m - 1 when nu(M^w) = 2.

Random rank-3 instances (graphic on 4 vertices, binary rank 3, uniform U_{3,m}, sums),
weights small / spread / exponential / ladder-like, plus the tight stage-2 instances of
docs/phase2d (Corollary A.3).  Checks at every run:
  THM      T_LS <= m, and T_LS <= m - 1 if nu(M^w) = 2
  STEP1    from nu0 = 1 one LS step gives nu0 >= 2         (2c, Corollary 3.3)
  REG      after the first step the LS steps are regular stage-2 updates (same vectors)
  OPT      Psi = Opt at the end (brute force)
False variants (must fail somewhere): F1 T_LS <= m - 2;  F2 T_LS <= 3 (a bound in k only).
Usage: python lsu_k3.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
from ls_mono_random import has_rainbow_base
from ls_search_drop import rweights

TIGHT = [  # docs/phase2d, Corollary A.3: stage 2 of m - 1 updates (k = 3)
    ("b", [4, 3, 3, 7, 7, 7, 1, 4, 2], [1, 1, 1, 1, 1, 1, 2, 1, 0],
     [7878, 418, 737, 2066, 3449, 65057, 526012, 3715, 1048576]),
    ("g", [(2, 1), (2, 3), (1, 2), (1, 0), (3, 1), (2, 0), (0, 2), (2, 1)], [1, 0, 1, 1, 2, 1, 1, 1],
     [6143, 188686, 3799, 94734, 421930, 1120, 1457, 54]),
    ("g", [(2, 3), (0, 1), (3, 0), (3, 0), (0, 1), (0, 2), (0, 3), (3, 1), (0, 3), (1, 0), (1, 3)],
     [0, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2],
     [242944, 652, 16002, 2, 121, 151842, 65, 38028, 75922, 8135, 356]),
]


def rmat3(rng):
    kind = rng.choice(["graphic", "graphic", "binary", "uniform", "sum"])
    if kind == "graphic":
        m = rng.randint(4, 11)
        return sc.graphic(4, [tuple(rng.sample(range(4), 2)) for _ in range(m)])
    if kind == "binary":
        return sc.gf2([rng.randint(1, 7) for _ in range(rng.randint(4, 11))])
    if kind == "uniform":
        return sc.uniform(3, rng.randint(4, 9))
    A = sc.uniform(1, rng.randint(2, 4))
    B = sc.graphic(3, [tuple(rng.sample(range(3), 2)) for _ in range(rng.randint(3, 6))])
    return sc.direct_sum(A, B)


def run_one(M, blk, w, st, ex, inst):
    k = M.k
    v = list(w)
    nu, _ = lc.nu_state(M, blk, k, v)
    nu_start = nu
    T = 0
    while nu < k:
        a, pcs, tau = lc.block(M, blk, k, v, k - 1)
        if nu == 2:
            tau2, lam, areg, info = sc.update(M, blk, k, v, 2)
            if list(areg) != list(a):
                st["REG"] += 1
                ex.setdefault("REG", inst)
        v2 = lc.shift(v, blk, a)
        nu2, _ = lc.nu_state(M, blk, k, v2)
        if nu == 1 and nu2 < 2:
            st["STEP1"] += 1
            ex.setdefault("STEP1", inst)
        v, nu = v2, nu2
        T += 1
        if T > 4 * M.m + 10:
            st["CAP"] += 1
            break
    st["runs"] += 1
    st["maxT_minus_m"] = max(st["maxT_minus_m"], T - M.m)
    if T > M.m or (nu_start == 2 and T > M.m - 1):
        st["THM"] += 1
        ex.setdefault("THM", inst)
    if T > M.m - 2:
        st["F1"] += 1
    if T > 3:
        st["F2"] += 1
    if sc.psi_from_v(M, blk, k, w, v) != sc.opt_rainbow(M, blk, k, w):
        st["OPT"] += 1
        ex.setdefault("OPT", inst)
    return T


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "THM": 0, "STEP1": 0, "REG": 0, "OPT": 0, "F1": 0, "F2": 0, "CAP": 0,
          "maxT_minus_m": -99}
    ex = {}
    while time.time() - t0 < budget:
        M = rmat3(rng)
        if M.k != 3:
            continue
        blk = [rng.randrange(3) for _ in range(M.m)]
        if len(set(blk)) < 3 or not has_rainbow_base(M, blk, 3):
            continue
        w = rweights(rng, M.m)
        run_one(M, blk, w, st, ex, (getattr(M, "edges", None), getattr(M, "cols", None), blk, w))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
    st0 = {"runs": 0, "THM": 0, "STEP1": 0, "REG": 0, "OPT": 0, "F1": 0, "F2": 0, "CAP": 0,
           "maxT_minus_m": -99}
    ex0 = {}
    for kind, data, blk, w in TIGHT:
        M = sc.graphic(4, data) if kind == "g" else sc.gf2(data)
        T = run_one(M, blk, w, st0, ex0, (kind, data, blk, w))
        print(f"tight instance {kind} m={M.m}: T_LS={T}", flush=True)
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot = dict(st0)
    exs = dict(ex0)
    for st, ex in res:
        for key, val in st.items():
            tot[key] = max(tot[key], val) if key.startswith("max") else tot[key] + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
