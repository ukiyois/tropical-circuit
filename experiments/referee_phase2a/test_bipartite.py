"""Proposition 7, last clause: for M the column partition matroid of a bipartite
support (blocks = rows), PO-SL N(t) has as bases exactly the sets with one edge
per column, all with D <= t, where D_ij = v_ij - min_i' v_i'j (the Lagrangian
slack, q_j = column minimum).  Also: the PO-SL update then equals the paper's
a_i = (tau - lambda_i)_+ computed from matchings of {D <= t}."""
import itertools
import random
import sys
from core import *


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    bad = 0
    n_checked = 0
    for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 400):
        n = rng.randint(2, 4)
        perm = list(range(n)); rng.shuffle(perm)
        E = sorted({(i, perm[i]) for i in range(n)} | {(i, j) for i in range(n) for j in range(n) if rng.random() < 0.5})
        m = len(E)
        if m > 11:
            continue
        col = [E[e][1] for e in range(m)]
        blk = [E[e][0] for e in range(m)]
        M = partition_matroid(col, {j: 1 for j in range(n)})
        v = rand_values(m, rng, rng.choice(["ties", "spaced", "generic"]))
        cmin = {j: min(v[e] for e in range(m) if col[e] == j) for j in range(n)}
        D = [v[e] - cmin[col[e]] for e in range(m)]
        for t in breakpoints(v, m):
            N = set(N_posl(M, v, t))
            want = {B for B in M.bases if all(D[e] <= t for e in elems(B))}
            n_checked += 1
            if N != want:
                bad += 1
        # update equals the paper's bottleneck formula on {D <= t}
        N0, _ = opt_bases(M, v)
        r = nu_of(N0, blk)
        if r < n:
            tau, lam, a, _ = posl_update(M, blk, n, v, r)
            # paper: tau = min over (r+1)-matchings of max D ; lambda_i = min over r-matchings avoiding i of max D
            def match_levels(size, avoid=None):
                best = INF
                for S in itertools.combinations(range(m), size):
                    rows = [blk[e] for e in S]
                    cols = [col[e] for e in S]
                    if len(set(rows)) < size or len(set(cols)) < size:
                        continue
                    if avoid is not None and avoid in rows:
                        continue
                    best = min(best, max([D[e] for e in S], default=F0))
                return best
            tau_p = match_levels(r + 1)
            if tau_p != tau:
                bad += 1
            for i in range(n):
                li = match_levels(r, i)
                ap = F0 if li == INF else max(tau_p - li, F0)
                if ap != a[i]:
                    bad += 1
    print("bipartite checks", n_checked, "mismatches", bad)


if __name__ == "__main__":
    main()
