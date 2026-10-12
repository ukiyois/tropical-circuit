"""Check the matroid instance of the compiler before building a direction on it.

Claim:  for a matroid M on E with rank r, the max-weight basis value
    h(w) = max_B w(B)
equals  mu * r(E) + C_F(w - mu*1),  mu = min_e w_e,
where   C_F(D) = sum_k (s_{k+1} - s_k) * F(G_k),  F(S) = r(E \\ S),
        G_k = {e : D_e <= s_k},  s_0 = 0 <= s_1 <= ... <= s_m sorted D.

Tested on random binary matroids (GF(2) column matroids) against brute force
over all bases, with exact rational weights including ties and negatives.
"""
import itertools
import random
from fractions import Fraction


def gf2_rank(cols):
    basis = []
    for v in cols:
        x = v
        for b in basis:
            x = min(x, x ^ b)
        if x:
            basis.append(x)
    return len(basis)


def make_matroid(k, m, rng):
    cols = [rng.randrange(1, 1 << k) for _ in range(m)]
    def r(S):
        return gf2_rank([cols[e] for e in S])
    return r


def brute_max_basis(r, m, w):
    full = r(range(m))
    best = None
    for B in itertools.combinations(range(m), full):
        if r(B) == full:
            val = sum(w[e] for e in B)
            best = val if best is None or val > best else best
    return best


def compiled(r, m, w):
    mu = min(w)
    D = [x - mu for x in w]
    s = [Fraction(0)] + sorted(D)
    E = set(range(m))
    total = Fraction(0)
    for k in range(m):
        Gk = {e for e in range(m) if D[e] <= s[k]}
        F = r(sorted(E - Gk))
        total += (s[k + 1] - s[k]) * F
    return mu * r(range(m)) + total


rng = random.Random(20261011)
trials = 0
for _ in range(3000):
    k = rng.randint(1, 4)
    m = rng.randint(1, 8)
    r = make_matroid(k, m, rng)
    pool = [Fraction(rng.randint(-6, 6), rng.choice([1, 2, 3])) for _ in range(3)]
    w = [rng.choice(pool) if rng.random() < 0.35 else Fraction(rng.randint(-9, 9), rng.randint(1, 4))
         for _ in range(m)]
    a, b = brute_max_basis(r, m, w), compiled(r, m, w)
    assert a == b, (k, m, w, a, b)
    trials += 1
print("ok: compiled value == brute-force max-weight basis on", trials, "random binary matroids")
