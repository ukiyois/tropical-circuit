"""B1 (exploratory): the last-stage block on general matroids (uncompressed).

For a matroid M of rank k with k blocks, the circuit block of stage r = k - 1
computes, at any state v,
    eta_b = sum over levels l_i < tau of (l_{i+1} - l_i) [b in Av(N(l_i))],
tau the first level with nu(N(t)) = k (PO-SL family N).  Iterating it from
p = 0: does nu0 ever decrease, does Psi reach Opt, and how many updates?
Random graphic (4 to 6 vertices), binary (rank 3 to 4) and uniform matroids,
m <= 10, random blocks with a rainbow base, integer weights; Opt by brute force.
Usage: python b1_laststage_general.py workers trials"""
import random
import sys
from multiprocessing import Pool

import stage_core as sc


def last_block(M, blk, k, v):
    levels = sc.levels_of(v)
    eta = [0] * k
    for i in range(len(levels)):
        N = sc.posl(M, v, levels[i])
        nu, av, _ = sc.rainbow_av(N, blk, k)
        if nu >= k or i + 1 == len(levels):
            break
        gap = levels[i + 1] - levels[i]
        for b in av:
            eta[b] += gap
    return eta


def random_case(rng):
    kind = rng.choice(["graphic", "binary", "uniform"])
    if kind == "graphic":
        n = rng.randint(4, 6)
        m = rng.randint(n, min(10, n * (n - 1) // 2 + 2))
        edges = [tuple(rng.sample(range(n), 2)) for _ in range(m)]
        M = sc.graphic(n, edges)
    elif kind == "binary":
        r = rng.randint(3, 4)
        m = rng.randint(r + 1, 9)
        M = sc.gf2([rng.randint(1, (1 << r) - 1) for _ in range(m)])
    else:
        r = rng.randint(2, 4)
        m = rng.randint(r + 1, 8)
        M = sc.uniform(r, m)
    k = M.k
    if k < 2:
        return None
    blk = [rng.randrange(k) for _ in range(M.m)]
    if len(set(blk)) < k:
        return None
    bases = sc.all_bases(M)
    w = [rng.randint(0, rng.choice([6, 30, 1000])) for _ in range(M.m)]
    opt = sc.opt_rainbow(M, blk, k, w, bases)
    if opt is None:
        return None
    return kind, M, blk, k, w, opt


def run(args):
    seed, trials = args
    rng = random.Random(seed)
    st = {"cases": 0, "ok": 0, "nonmono": 0, "stuck": 0, "over": 0, "max_upd": 0,
          "reg_max": 0, "upd_sum": 0, "reg_sum": 0, "fails": []}
    done = 0
    while done < trials:
        case = random_case(rng)
        if case is None:
            continue
        kind, M, blk, k, w, opt = case
        done += 1
        st["cases"] += 1
        lens, vreg = sc.run_schedule(M, blk, k, w)
        st["reg_max"] = max(st["reg_max"], sum(lens))
        st["reg_sum"] += sum(lens)
        v = list(w)
        p = [0] * k
        nu_prev = sc.state(M, blk, k, v)[0]
        upd = 0
        bad = False
        while True:
            nu0 = sc.state(M, blk, k, v)[0]
            if nu0 < nu_prev:
                st["nonmono"] += 1
                bad = True
            nu_prev = nu0
            if nu0 >= k:
                break
            eta = last_block(M, blk, k, v)
            if not any(eta) or upd > 200:
                st["stuck"] += 1
                bad = True
                break
            v = [v[e] - eta[blk[e]] for e in range(M.m)]
            p = [p[b] + eta[b] for b in range(k)]
            upd += 1
        psi = sum(p) + sc.beta(M, v)
        st["over"] += psi > opt
        if not bad and psi == opt:
            st["ok"] += 1
        elif len(st["fails"]) < 3:
            st["fails"].append((kind, M.m, k, blk, w, getattr(M, "edges", None), getattr(M, "cols", None)))
        st["max_upd"] = max(st["max_upd"], upd)
        st["upd_sum"] += upd
    return st


if __name__ == "__main__":
    workers, trials = int(sys.argv[1]), int(sys.argv[2])
    with Pool(workers) as pool:
        res = pool.map(run, [(1300 + s, trials) for s in range(workers)])
    out = {}
    for d in res:
        for key, val in d.items():
            if key == "fails":
                out.setdefault("fails", []).extend(val)
            elif key in ("max_upd", "reg_max"):
                out[key] = max(out.get(key, val), val)
            else:
                out[key] = out.get(key, 0) + val
    fails = out.pop("fails")
    print(out, flush=True)
    for f in fails[:5]:
        print("FAIL", f, flush=True)
