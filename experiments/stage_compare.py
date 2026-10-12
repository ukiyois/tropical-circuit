"""Stage lengths of candidate families (stage_families.py) and of the exact family P_t
on the long-stage instances: halving ladders, the paper's examples, and the
instances found by hill climbing.  Uses scan=True (no monotonicity assumed).
Usage: python stage_compare.py"""
import stage_core as sc
import stage_families as SF
from stage_ladder import ladder

INSTANCES = []
for L in range(0, 7):
    e, b, w = ladder(L)
    INSTANCES.append((f"ladder L={L}", 4, e, b, w))
INSTANCES += [
    ("paper ex 4", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 3)], [0, 1, 1, 1, 2, 0], [3, 1, 0, 3, 3, 2]),
    ("paper ex 7", 4, [(2, 3), (1, 0), (0, 3), (1, 0), (2, 1), (3, 0), (0, 2), (2, 0), (3, 0)],
     [1, 0, 1, 2, 0, 1, 1, 1, 1], [5, 9, 6, 12, 10, 9, 3, 2, 4]),
    ("exp k3 m8", 4, [(3, 1), (0, 1), (3, 1), (1, 0), (2, 3), (2, 1), (1, 3), (0, 3)],
     [0, 0, 0, 0, 1, 2, 0, 0], [15523, 6, 23234, 46467, 92938, 269905, 1, 4]),
    ("exp k4 m9", 5, [(2, 3), (4, 2), (2, 1), (2, 0), (1, 4), (3, 0), (3, 2), (3, 2), (3, 1)],
     [3, 2, 2, 1, 3, 0, 3, 3, 3], [1, 1674, 673, 142624, 3417, 73020, 37674, 421, 4925]),
    ("hill k4 m10", 5, [(0, 3), (3, 4), (3, 2), (0, 1), (1, 2), (4, 1), (1, 2), (3, 1), (1, 4), (1, 3)],
     [3, 1, 0, 3, 0, 3, 2, 3, 3, 1], [2, 5, 9, 3, 8, 4, 12, 1, 6, 0]),
]


def run(M, blk, k, w, fam):
    v = list(w)
    lens = []
    for r in range(1, k):
        nu, _ = sc.state(M, blk, k, v)
        if nu > r:
            lens.append(0)
            continue
        c = 0
        while True:
            nu, _ = sc.state(M, blk, k, v)
            if nu > r:
                break
            tau, lam, a, _ = sc.update(M, blk, k, v, r, fam, scan=True)
            v = sc.shift(v, blk, a)
            c += 1
            if c > 200:
                raise RuntimeError("cap")
        lens.append(c)
    return lens, sc.psi_from_v(M, blk, k, w, v)


if __name__ == "__main__":
    fams = {name: SF.family(name) for name in ["posl", "clheight", "xlink", "xlink2", "xh"]}
    for name, n, e, b, w in INSTANCES:
        M = sc.graphic(n, e)
        k = M.k
        opt = sc.opt_rainbow(M, b, k, w)
        row = [name, f"m={M.m}", f"Opt={opt}"]
        for fname, fam in fams.items():
            lens, psi = run(M, b, k, w, fam)
            row.append(f"{fname}={lens}{'' if psi == opt else ' WRONG ' + str(psi)}")
        vv = list(w)
        ex = []
        for r in range(1, k):
            nu, _ = sc.state(M, b, k, vv)
            if nu > r:
                ex.append(0)
                continue
            c, vv = sc.run_stage_exact(M, b, k, vv, r)
            ex.append(c)
        row.append(f"exact={ex}")
        print("  ".join(row), flush=True)
