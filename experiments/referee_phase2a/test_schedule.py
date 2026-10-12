"""Static-schedule simulation of Corollary 9 with the PO-SL update, plus full
Theorem 6 / Theorem 8 checks at every application (reusing test_main checks),
plus: identity at nu0 > r, nu0 never drops, S never shrinks, stage length within
(r+1)(floor(m^2/4)+1), final Psi = Opt.  Also records the number of applications
per stage (claimed only <= bound; observed <= r+1 by the authors)."""
import random
import sys
from core import *
import test_main as TM


def run_instance(M, blk, k, w, stats, check=True):
    p = {b: F0 for b in range(k)}
    worst_excess = -99
    for r in range(k):
        bound = (r + 1) * (M.m * M.m // 4 + 1)
        used = 0
        while True:
            v = [w[e] - p[blk[e]] for e in range(M.m)]
            N0, _ = opt_bases(M, v)
            nu0 = nu_of(N0, blk)
            if nu0 > r:
                # application must be the identity: tau = 0
                tau, lam, a, _ = posl_update(M, blk, k, v, r)
                if tau != 0 or any(a.values()):
                    TM.fail("identity", (v, r))
                break
            if nu0 < r:
                TM.fail("stage-entry-nu0<r", (v, r, nu0))
                return
            if check:
                TM.check_thm6_thm8(M, blk, k, v, r, stats)
            tau, lam, a, _ = posl_update(M, blk, k, v, r)
            p = {b: p[b] + a[b] for b in range(k)}
            used += 1
            if used > bound:
                TM.fail("over-bound", (r, used, bound))
                return
            if used > 200:
                TM.fail("runaway", (r,))
                return
        stats["apps_hist"][(r, used)] = stats["apps_hist"].get((r, used), 0) + 1
        worst_excess = max(worst_excess, used - (r + 1))
    val = psi(M, blk, k, w, p)
    if val != opt_rainbow(M, blk, k, w):
        TM.fail("final-opt", (w, val))
    stats["runs"] += 1
    stats["worst_excess"] = max(stats["worst_excess"], worst_excess)


def gen_instance(rng):
    while True:
        kind, M = random_matroid(rng)
        if M.k < 2:
            continue
        blk = rand_blocks(M, M.k, rng)
        if blk is None:
            continue
        style = rng.choice(["ties", "ties5", "spaced", "mixed", "generic"])
        return kind, M, blk, M.k, rand_values(M.m, rng, style)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    stats = {key: 0 for key in ["F1", "F2", "F3", "F4", "rel", "T6", "T8", "T8-item3-cases", "S-grow",
                                "aug", "C-not-strict-anyway", "step3-choices", "compile", "runs"]}
    stats["apps_hist"] = {}
    stats["worst_excess"] = -99
    for _ in range(trials):
        kind, M, blk, k, w = gen_instance(rng)
        run_instance(M, blk, k, w, stats)
    h = stats.pop("apps_hist")
    print("stats", stats)
    over = {key: c for key, c in h.items() if key[1] > key[0] + 1}
    print("stages with more than r+1 applications:", over)
    print("failures", len(TM.FAIL))


if __name__ == "__main__":
    main()
