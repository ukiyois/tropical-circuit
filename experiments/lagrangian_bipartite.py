"""Phase 2, step 2: drop the column potentials.

The paper keeps (p, q) with D = w - p - q >= 0.  For the generalization to
"partition matroid + general matroid" the second side has no block potentials,
so test the variant in which q is never stored:

    v      = w - p[row]                 (only p is state)
    D_ij   = v_ij - min_i' v_i'j        (slack relative to the column minimum)
    update p += a,  a_i = (tau - lambda_i)_+ from the threshold graphs of D
    answer Psi(p) = sum_i p_i + sum_j min_i (w_ij - p_i)   (Lagrangian dual)

Psi(p) <= Assign for every p (weak duality), so reaching Assign certifies
optimality.  Checked on random supports against brute force, together with
monotonicity of Psi along the schedule.
"""
import random
from fractions import Fraction

from assignment_gain import assign, bottleneck, nu_at, INF


def psi(n, E, W, p):
    cols = {}
    for (i, j) in E:
        cols.setdefault(j, []).append(W[(i, j)] - p[i])
    return sum(p.values()) + sum(min(vs) for vs in cols.values())


def slack(n, E, W, p):
    colmin = {}
    for (i, j) in E:
        v = W[(i, j)] - p[i]
        colmin[j] = v if j not in colmin else min(colmin[j], v)
    return {(i, j): W[(i, j)] - p[i] - colmin[j] for (i, j) in E}


def update_p(n, E, D, r):
    if nu_at(n, E, D, Fraction(0)) != r:
        return {i: Fraction(0) for i in range(n)}
    tau = bottleneck(n, E, D, r + 1)
    a = {}
    for i in range(n):
        lam = bottleneck(n, E, D, r, drop_row=i)
        a[i] = Fraction(0) if lam is INF else max(tau - lam, Fraction(0))
    return a


def run(n, E, W):
    p = {i: Fraction(0) for i in range(n)}
    last = psi(n, E, W, p)
    for r in range(n):
        for _ in range(r + 1):
            a = update_p(n, E, slack(n, E, W, p), r)
            p = {i: p[i] + a[i] for i in range(n)}
            cur = psi(n, E, W, p)
            assert cur >= last, ("Psi decreased", last, cur)
            last = cur
    return last


if __name__ == "__main__":
    rng = random.Random(11)
    ok = bad = 0
    for _ in range(2000):
        n = rng.randint(1, 5)
        perm = list(range(n)); rng.shuffle(perm)
        E = {(i, perm[i]) for i in range(n)}
        for i in range(n):
            for j in range(n):
                if rng.random() < 0.55:
                    E.add((i, j))
        pool = [Fraction(rng.randint(-4, 4)) for _ in range(3)]
        W = {e: (rng.choice(pool) if rng.random() < 0.4 else Fraction(rng.randint(-8, 8), rng.randint(1, 3)))
             for e in E}
        if run(n, E, W) == assign(n, E, W):
            ok += 1
        else:
            bad += 1
    print("q-free variant: optimal on", ok, "of", ok + bad, "random supports;", bad, "failures")
