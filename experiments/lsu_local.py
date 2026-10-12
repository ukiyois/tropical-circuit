"""Check of Lemma 2.1 (offsets), Lemma 2.2 (freezing), Proposition 2.4 (local regime).

Along LS runs from p = 0 (exact arithmetic), with p* = p_T, v* = w - p*_blk, x_j = p* - p_j,
G_j = Opt - Psi(p_j):
  OFF      0 <= x_{j,b} <= G_j and tau_j <= G_j - G_{j+1}
  FRZ      |v*_e - v*_f| > G_j (one component)  =>  sign(v_{i,e} - v_{i,f}) = sign(v*_e - v*_f), i >= j
  LOC      if G_j < gamma/2 (gamma = least nonzero |v*_e - v*_f| in one component): the LS block
           at v_j equals the block of the block-constant problem (M' = M^{v*}, x_j) with the
           family N' (PO-SL on M' with linkage classes K cap {v* = l}); and nu agrees.
False variants (must fail): FRZ_F  the freezing with threshold G_j / 4 instead of G_j;
  LOC_F  the same comparison at states with G_j >= gamma/2;
  LOC_C  the comparison at local states with the linkage classes replaced by the
         components of M' (standard PO-SL on M'), reported (it may or may not differ).
Usage: python lsu_local.py workers seconds [seed0]"""
import random
import sys
import time
from multiprocessing import Pool

import stage_core as sc
import ls_core as lc
import lsu_core as uc


def make_family(classes):
    """PO-SL-type family on a matroid Mp (with .m, .rank) with linkage classes `classes`
    (a list: class label of each element)."""
    def fam(Mp, v, t):
        m = Mp.m
        po = []
        for f in range(m):
            if Mp.rank(1 << f) == 0:
                continue
            low = 0
            for g in range(m):
                if v[g] < v[f] - t:
                    low |= 1 << g
            if Mp.rank(low | (1 << f)) > Mp.rank(low):
                po.append(f)
        u = [m + 1] * m
        groups = {}
        for f in po:
            groups.setdefault(classes[f], []).append(f)
        for el in groups.values():
            el.sort(key=lambda e: v[e])
            lab = 0
            for i, e in enumerate(el):
                if i > 0 and v[e] - v[el[i - 1]] > t:
                    lab += 1
                u[e] = lab
        return sc.MinBase(Mp, u)
    return fam


class Wrap:
    """MinBase(M, u) with the attributes ls_core expects (m, rank, indep)."""
    def __init__(self, MB):
        self.MB = MB
        self.m = MB.m

    def rank(self, A):
        return self.MB.rank(A)

    def indep(self, A):
        return self.MB.indep(A)


def comp_classes_of(Mp_wrap, m):
    """Components of the matroid Mp (by fundamental circuits of a greedy base)."""
    parent = list(range(m))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    B = 0
    for e in range(m):
        if Mp_wrap.rank(B | (1 << e)) > sc.popcount(B):
            B |= 1 << e
    k = sc.popcount(B)
    for e in range(m):
        if B >> e & 1 or Mp_wrap.rank(1 << e) == 0:
            continue
        for f in sc.bits(B):
            if Mp_wrap.rank((B & ~(1 << f)) | (1 << e)) == k:
                parent[find(e)] = find(f)
    return [find(e) for e in range(m)]


def sgn(z):
    return (z > 0) - (z < 0)


def work(args):
    seed, budget = args
    rng = random.Random(seed)
    t0 = time.time()
    st = {"runs": 0, "states": 0, "OFF": 0, "FRZ": 0, "FRZ_F": 0, "loc_states": 0, "LOC": 0,
          "nonloc_states": 0, "LOC_F": 0, "LOC_C": 0}
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
        T = len(blocks)
        G = [opt - (sum(s["p"]) + sc.beta(M, s["v"])) for s in states]
        inst = (uc.describe(M), blk, w)
        m = M.m
        pairs = [(e, f) for e in range(m) for f in range(m) if e < f and M.comp[e] == M.comp[f]]
        gaps = [abs(vstar[e] - vstar[f]) for (e, f) in pairs if vstar[e] != vstar[f]]
        gamma = min(gaps) if gaps else None
        Mp = Wrap(sc.MinBase(M, vstar))
        lam = [(M.comp[e], vstar[e]) for e in range(m)]
        fam = make_family(lam)
        famC = make_family(comp_classes_of(Mp, m))
        for j, s in enumerate(states):
            st["states"] += 1
            x = [pT[b] - s["p"][b] for b in range(k)]
            if min(x) < 0 or max(x) > G[j]:
                st["OFF"] += 1
                ex.setdefault("OFF", (inst, j))
            if j < T and blocks[j]["tau"] > G[j] - G[j + 1]:
                st["OFF"] += 1
                ex.setdefault("OFF_tau", (inst, j))
            for (e, f) in pairs:
                d = vstar[e] - vstar[f]
                for thr, key in ((G[j], "FRZ"), (G[j] / 4, "FRZ_F")):
                    if abs(d) > thr and any(sgn(states[i]["v"][e] - states[i]["v"][f]) != sgn(d)
                                            for i in range(j, T + 1)):
                        st[key] += 1
                        if key == "FRZ":
                            ex.setdefault("FRZ", (inst, j, e, f))
            if j == T:
                continue
            xv = [x[blk[e]] for e in range(m)]
            local = gamma is None or 2 * G[j] < gamma
            a_true = blocks[j]["a"]
            try:
                a_bc, _, _ = lc.block(Mp, blk, k, xv, k - 1, fam)
            except RuntimeError:
                a_bc = None
            same = a_bc is not None and list(a_bc) == list(a_true)
            if local:
                st["loc_states"] += 1
                nu_bc, _, _ = sc.rainbow_av(Wrap(sc.MinBase(Mp, xv)), blk, k)
                if not same or nu_bc != s["nu"]:
                    st["LOC"] += 1
                    ex.setdefault("LOC", (inst, j, a_true, a_bc))
                try:
                    a_c, _, _ = lc.block(Mp, blk, k, xv, k - 1, famC)
                except RuntimeError:
                    a_c = None
                if a_c is None or list(a_c) != list(a_true):
                    st["LOC_C"] += 1
                    ex.setdefault("LOC_C", (inst, j, a_true, a_c))
            else:
                st["nonloc_states"] += 1
                if not same:
                    st["LOC_F"] += 1
    return st, ex


if __name__ == "__main__":
    workers, budget = int(sys.argv[1]), float(sys.argv[2])
    seed0 = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
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
