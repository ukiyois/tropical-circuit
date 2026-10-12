"""Check the fixed-index dual for weighted matroid intersection.

Claim (Edmonds / Frank weight splitting), for w >= 0 integral:
    max { w(I) : I independent in M1 and M2 }
  = min { L1(w1) + L2(w2) : w1 + w2 = w, w1, w2 >= 0 integral },
where Li is the Lovasz extension of the rank function of Mi, i.e. the
greedy value max_{x in P(Mi)} <wi, x>.  The dual variables are indexed by
the ground set, independent of any current solution.
"""
import itertools
import random


def gf2_rank(cols):
    basis = []
    for v in cols:
        x = v
        for b in basis:
            x = min(x, x ^ b)
        if x:
            basis.append(x)
    return len(basis)


def matroid(kind, m, rng):
    if kind == "binary":
        k = rng.randint(1, 3)
        cols = [rng.randrange(1, 1 << k) for _ in range(m)]
        return lambda S: gf2_rank([cols[e] for e in S])
    blocks = [rng.randrange(rng.randint(1, 3)) for _ in range(m)]
    caps = {b: rng.randint(1, 2) for b in set(blocks)}
    def r(S):
        cnt = {}
        for e in S:
            cnt[blocks[e]] = cnt.get(blocks[e], 0) + 1
        return sum(min(c, caps[b]) for b, c in cnt.items())
    return r


def lovasz(r, u):
    order = sorted(range(len(u)), key=lambda e: -u[e])
    val, prev, S = 0, 0, []
    for e in order:
        S.append(e)
        cur = r(S)
        val += u[e] * (cur - prev)
        prev = cur
    return val


def primal(r1, r2, m, w):
    best = 0
    for size in range(m + 1):
        for I in itertools.combinations(range(m), size):
            if r1(I) == size and r2(I) == size:
                best = max(best, sum(w[e] for e in I))
    return best


def dual(r1, r2, m, w):
    best = None
    for w1 in itertools.product(*[range(x + 1) for x in w]):
        w2 = [w[e] - w1[e] for e in range(m)]
        val = lovasz(r1, list(w1)) + lovasz(r2, w2)
        best = val if best is None or val < best else best
    return best


rng = random.Random(7)
n = 0
for _ in range(1500):
    m = rng.randint(1, 5)
    r1 = matroid(rng.choice(["binary", "partition"]), m, rng)
    r2 = matroid(rng.choice(["binary", "partition"]), m, rng)
    w = [rng.randint(0, 3) for _ in range(m)]
    p, d = primal(r1, r2, m, w), dual(r1, r2, m, w)
    assert p == d, (m, w, p, d)
    n += 1
print("ok: primal == element-indexed splitting dual on", n, "random matroid pairs")
