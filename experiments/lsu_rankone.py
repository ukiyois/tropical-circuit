"""LS iteration when every component of M has rank one (assignment problem in rainbow
form: partition matroid of columns, blocks = rows).  A perfect matching (rainbow base)
is planted, extra edges are random.  Records, per run, T_LS against k and nu(M^w), and per
step whether nu0 increases, whether the step is pure (one nu-level below tau) and whether
it has a mismatch.
Candidates: Tk1  T_LS <= k - 1;  CAND  T_LS <= k - nu(M^w);  STEP  every step increases nu0.
False variants: Tk2_false  T_LS <= k - 2;  FALSE  T_LS <= k - nu(M^w) - 1 (when nu(M^w) < k);  FSTEP  every step
increases nu0 by at least 2.
Usage: python lsu_rankone.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_trace as tr


def instance(rng):
    k = rng.randint(2, 7)
    perm = list(range(k))
    rng.shuffle(perm)
    parts, blk = [], []
    for c in range(k):
        parts.append(c)
        blk.append(perm[c])
        for _ in range(rng.randint(0, 4)):
            parts.append(c)
            blk.append(rng.randrange(k))
    style = rng.choice(["small", "spread", "exp"])
    if style == "small":
        w = [rng.randint(0, 5) for _ in parts]
    elif style == "spread":
        w = [rng.randint(0, 10 ** 6) for _ in parts]
    else:
        w = [rng.choice([0, 1 << rng.randint(0, 30), rng.randint(0, 1 << 30)]) for _ in parts]
    return k, parts, blk, w


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "steps": 0, "CAND": 0, "FALSE": 0, "STEP": 0, "FSTEP": 0, "OPT": 0,
          "pure_steps": 0, "mismatch_steps": 0, "maxT": 0, "Tk1": 0, "Tk2_false": 0,
          "max_T_minus_k": -99}
    ex = {}
    while time.time() - t0 < budget:
        k, parts, blk, w = instance(rng)
        M = sc.partition(parts)
        trace = tr.trace(M, blk, k, w, cap=200)
        st["runs"] += 1
        T = len(trace)
        st["maxT"] = max(st["maxT"], T)
        st["max_T_minus_k"] = max(st["max_T_minus_k"], T - k)
        if T > k - 1:
            st["Tk1"] += 1
            ex.setdefault("Tk1", (parts, blk, w, T))
        if T > k - 2:
            st["Tk2_false"] += 1
        nu_start = lc.nu_state(M, blk, k, w)[0]
        if T > k - nu_start:
            st["CAND"] += 1
            ex.setdefault("CAND", (parts, blk, w, T))
        if nu_start < k and T > k - nu_start - 1:
            st["FALSE"] += 1
        for s in trace:
            st["steps"] += 1
            if s["nu1"] <= s["nu0"]:
                st["STEP"] += 1
                ex.setdefault("STEP", (parts, blk, w))
            if s["nu1"] < s["nu0"] + 2 and s["nu1"] < k:
                st["FSTEP"] += 1
            st["pure_steps"] += len({nu for _, _, nu, _ in s["pcs"]}) == 1
            st["mismatch_steps"] += s["mismatch"]
        vl = trace[-1]["v2"] if trace else w
        if sc.psi_from_v(M, blk, k, w, vl) != sc.opt_rainbow(M, blk, k, w):
            st["OPT"] += 1
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 16000
    with Pool(workers) as pool:
        res = pool.map(work, [(seed0 + s, budget) for s in range(workers)])
    tot, exs = {}, {}
    for st, ex in res:
        for key, val in st.items():
            tot[key] = max(tot.get(key, val), val) if key.startswith("max") else tot.get(key, 0) + val
        for key, val in ex.items():
            exs.setdefault(key, val)
    print(tot, flush=True)
    for key, val in exs.items():
        print(key, val, flush=True)
