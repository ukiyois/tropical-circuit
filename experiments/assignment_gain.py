"""Phase 2, step 1: the objective accounting of the paper's update.

Run the schedule U_0^1 U_1^2 ... U_{n-1}^n through the bottleneck form of
Proposition 4.3 (tau, lambda, mu), in exact rational arithmetic, and check:

  (1) the final z equals Assign_n(W) (brute force);
  (2) every active application raises z by exactly (n - r) * tau,
      the deficiency times the bottleneck threshold;
  (3) D stays >= 0 throughout.

(2) follows from Step 0 of Theorem 4.6, since sum a - sum c is the integral
of |S(G_t)| - |T(G_t)| = n - nu(G_t) = n - r over [0, tau).  It is the
accounting a matroid generalization must reproduce.
"""
import itertools
import random
from fractions import Fraction

INF = None


def max_matching(n, edges):
    match_r = [-1] * n
    adj = [[] for _ in range(n)]
    for (i, j) in edges:
        adj[i].append(j)

    def try_aug(i, seen):
        for j in adj[i]:
            if not seen[j]:
                seen[j] = True
                if match_r[j] == -1 or try_aug(match_r[j], seen):
                    match_r[j] = i
                    return True
        return False

    return sum(try_aug(i, [False] * n) for i in range(n))


def nu_at(n, E, D, t, drop_row=None):
    return max_matching(n, [(i, j) for (i, j) in E if D[(i, j)] <= t and i != drop_row])


def bottleneck(n, E, D, k, drop_row=None):
    """least sorted value t with a k-matching in {D <= t}, avoiding drop_row."""
    if k == 0:
        return Fraction(0)
    for t in sorted(set(D.values())):
        if nu_at(n, E, D, t, drop_row) >= k:
            return t
    return INF


def update(n, E, D, r):
    if nu_at(n, E, D, Fraction(0)) != r:
        return {i: Fraction(0) for i in range(n)}, {j: Fraction(0) for j in range(n)}, None
    tau = bottleneck(n, E, D, r + 1)
    lam = {i: bottleneck(n, E, D, r, drop_row=i) for i in range(n)}
    a = {i: (Fraction(0) if lam[i] is INF else max(tau - lam[i], Fraction(0))) for i in range(n)}
    mu = {}
    for j in range(n):
        cands = [max(lam[i], D[(i, jj)]) for (i, jj) in E if jj == j and lam[i] is not INF]
        mu[j] = min(cands) if cands else INF
    c = {j: (Fraction(0) if mu[j] is INF else max(tau - mu[j], Fraction(0))) for j in range(n)}
    return a, c, tau


def assign(n, E, W):
    best = None
    for perm in itertools.permutations(range(n)):
        if all((i, perm[i]) in E for i in range(n)):
            v = sum(W[(i, perm[i])] for i in range(n))
            best = v if best is None or v < best else best
    return best


def run(n, E, W):
    mu0 = min(W.values())
    D = {e: W[e] - mu0 for e in E}
    z = n * mu0
    for r in range(n):
        for _ in range(r + 1):
            a, c, tau = update(n, E, D, r)
            gain = sum(a.values()) - sum(c.values())
            if tau is not None:
                assert gain == (n - r) * tau, ("gain", gain, n, r, tau)
            z += gain
            D = {(i, j): D[(i, j)] - a[i] + c[j] for (i, j) in E}
            assert min(D.values()) >= 0, ("negative slack", D)
    return z


if __name__ == "__main__":
  rng = random.Random(4)
  checked = 0
  for _ in range(1500):
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
      assert run(n, E, W) == assign(n, E, W)
      checked += 1
  print("ok:", checked, "random supports; z == Assign, every active gain == (n-r)*tau, D >= 0")
