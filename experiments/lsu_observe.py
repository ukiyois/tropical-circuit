"""Observations and refuted potentials along LS runs (Section 7 of docs/phase2f).

Random instances (lsu_core.rand_instance: graphic, binary, uniform, paving, sums; k = 3..7,
m <= 12; weights small / spread / exponential / ladder), LS run from p = 0, p* = p_T.
Observations (counted failures; expected 0):
  O1  every block vector a_j has a zero entry
  O2  some block is never raised along the run (min_b p*_b = 0)
  O3  every block vector has an entry equal to tau_j (a fully raised block)
Their false variants (expected to fail):
  O1F the block of a least element of v_j (over non-loops) has a_{j,b} = 0
  O2F the block of a least element of w is never raised
  O3F one block is fully raised at every step of the run (runs with T >= 2)
Refuted candidate potentials (counted failures; nonzero shows the refutation):
  P1  p_j <= p0, the least element of P* cap {p >= 0}           (no overshoot)
  P2  the order of the remaining offsets x_j = p* - p_j is preserved (strict -> weak)
  P3  a pair e, f (one component, v*_e != v*_f) once in its final strict order stays so
  P4  every step except the last puts some such pair into its final order
  P5  every pair (one component, different blocks) reverses its strict order at most once
Usage: python lsu_observe.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import lsu_core as uc


def sgn(z):
    return (z > 0) - (z < 0)


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    keys = ["runs", "runs_T2", "steps", "O1", "O2", "O3", "O1F", "O2F", "O3F",
            "P1", "P2", "P3", "P4", "P5", "pairs", "max_reversals"]
    st = {key: 0 for key in keys}
    ex = {}
    while time.time() - t0 < budget:
        kind, M, blk, k, w = uc.rand_instance(rng, kmin=3, kmax=7, mmax=12)
        states, blocks = uc.ls_run(M, blk, k, w, cap=400)
        if not blocks:
            continue
        T = len(blocks)
        st["runs"] += 1
        inst = (uc.describe(M), blk, w)
        pT = states[-1]["p"]
        nonloop = [e for e in range(M.m) if M.rank(1 << e) > 0]
        # O2 / O2F
        if min(pT) > 0:
            st["O2"] += 1
            ex.setdefault("O2", inst)
        mn = min(w[e] for e in nonloop)
        if all(pT[blk[e]] > 0 for e in nonloop if w[e] == mn):
            st["O2F"] += 1
        full = []
        for j, bl in enumerate(blocks):
            st["steps"] += 1
            a, tau, v = bl["a"], bl["tau"], states[j]["v"]
            if min(a) > 0:
                st["O1"] += 1
                ex.setdefault("O1", (inst, j))
            mv = min(v[e] for e in nonloop)
            if all(a[blk[e]] > 0 for e in nonloop if v[e] == mv):
                st["O1F"] += 1
            f = {b for b in range(k) if a[b] == tau}
            if not f:
                st["O3"] += 1
                ex.setdefault("O3", (inst, j))
            full.append(f)
        if T >= 2:
            st["runs_T2"] += 1
            if not set.intersection(*full):
                st["O3F"] += 1
        # P1 no overshoot of the least dual optimum
        ob = uc.opt_rainbow_base(M, blk, k, w)
        p0 = uc.least_dual(M, blk, k, w, ob[1])
        if any(s["p"][b] > p0[b] for s in states for b in range(k)):
            st["P1"] += 1
            ex.setdefault("P1", (inst, p0, [s["p"] for s in states]))
        # P2 order of the remaining offsets
        xs = [[pT[b] - s["p"][b] for b in range(k)] for s in states]
        for j in range(T):
            x0, x1 = xs[j], xs[j + 1]
            if any(x0[b] > x0[c] and x1[b] < x1[c] for b in range(k) for c in range(k)):
                st["P2"] += 1
                ex.setdefault("P2", (inst, j, x0, x1))
        # P3, P4, P5 pairs
        vs = [s["v"] for s in states]
        vstar = vs[-1]
        pairs = [(e, f) for e in range(M.m) for f in range(e + 1, M.m)
                 if M.comp[e] == M.comp[f] and blk[e] != blk[f]]
        fin = [(e, f) for (e, f) in pairs if vstar[e] != vstar[f]]
        st["pairs"] += len(fin)
        for (e, f) in fin:
            d = sgn(vstar[e] - vstar[f])
            seen = False
            for v in vs:
                g = sgn(v[e] - v[f]) == d
                if g:
                    seen = True
                elif seen:
                    st["P3"] += 1
                    ex.setdefault("P3", (inst, (e, f), [(v[e], v[f]) for v in vs]))
                    break
        for j in range(T - 1):
            if not any(sgn(vs[j][e] - vs[j][f]) != sgn(vstar[e] - vstar[f]) and
                       sgn(vs[j + 1][e] - vs[j + 1][f]) == sgn(vstar[e] - vstar[f]) for (e, f) in fin):
                st["P4"] += 1
                ex.setdefault("P4", (inst, j))
        for (e, f) in pairs:
            strict = [sgn(v[e] - v[f]) for v in vs if v[e] != v[f]]
            rev = sum(1 for x, y in zip(strict, strict[1:]) if x != y)
            st["max_reversals"] = max(st["max_reversals"], rev)
            if rev > 1:
                st["P5"] += 1
                ex.setdefault("P5", (inst, (e, f), [(v[e], v[f]) for v in vs]))
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 12000
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
