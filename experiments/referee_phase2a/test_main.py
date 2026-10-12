"""Referee checks of Proposition 7 (F1-F4, relation-determined), Theorem 6,
Theorem 8 (items 1-3, Steps 1-5 for every admissible choice), and the
compilation identity a_b = C_{F_b}(D+), at ARBITRARY states v with nu0(v) = r < k
(not only schedule-reachable ones).  Exact rationals throughout."""
import random
import sys
from core import *

FAIL = []


def fail(tag, info):
    FAIL.append((tag, info))
    if len(FAIL) < 15:
        print("FAIL", tag, info, flush=True)


def check_prop7(M, blk, k, v, stats):
    T = breakpoints(v, M.m)
    pts = []
    for i, t in enumerate(T):
        pts.append(t)
        if i + 1 < len(T):
            pts.append((t + T[i + 1]) / 2)
    pts.append(T[-1] + 1)
    Ns = {t: N_posl(M, v, t) for t in pts}
    N0, _ = opt_bases(M, v)
    stats["F1"] += 1
    if Ns[F0] != N0:
        fail("F1", (v,))
    # piecewise constant + right continuous on breakpoints, monotone
    for i, t in enumerate(pts[:-1]):
        t2 = pts[i + 1]
        stats["F2"] += 1
        if not Ns[t] <= Ns[t2]:
            fail("F2", (v, t, t2))
    for i, t in enumerate(T[:-1]):
        mid = (t + T[i + 1]) / 2
        if Ns[t] != Ns[mid]:
            fail("pw-const", (v, t, mid))
    # F3
    th = {B: theta_local(M, v, B) for B in M.bases}
    for t in pts:
        stats["F3"] += 1
        for B in M.bases:
            if th[B] <= t and B not in Ns[t]:
                fail("F3", (v, t, B))
                break
    # F4 and top level = M
    top = Ns[pts[-1]]
    stats["F4"] += 1
    if set(top) != set(M.bases):
        fail("F4-top", (v,))
    # determined by G_t
    for t in T:
        G = {(e, f) for e in range(M.m) for f in range(M.m) if v[f] - v[e] <= t}
        stats["rel"] += 1
        if N_from_relation(M, G) != Ns[t]:
            fail("relation", (v, t))
    return Ns


def cross(blk, v, S, m):
    ES = [e for e in range(m) if blk[e] in S]
    rest = [e for e in range(m) if blk[e] not in S]
    return {(y, g) for y in ES for g in rest if v[y] <= v[g]}


def check_thm6_thm8(M, blk, k, v, r, stats):
    tau, lam, a, Ns = posl_update(M, blk, k, v, r)
    if tau is None:
        fail("tau-none", (v,))
        return
    v2 = [v[e] - a[blk[e]] for e in range(M.m)]
    b1 = beta(M, v)
    b2 = beta(M, v2)
    gain = sum(a.values(), F0) + b2 - b1
    stats["T6"] += 1
    if gain != (k - r) * tau:
        fail("T6-gain", (v, r, tau, a, gain))
    N0, _ = opt_bases(M, v)
    N0b, _ = opt_bases(M, v2)
    for B in N0:
        if len(blocks_of(B, blk)) == r and B not in N0b:
            fail("T6-Bstar", (v, r, B))
    nu2 = nu_of(N0b, blk)
    if nu2 < r:
        fail("T6-nu-drop", (v, r))
    # ---------------- Theorem 8
    S, nu0 = avoidable(N0, blk, k)
    assert nu0 == r
    C0 = cross(blk, v, S, M.m)
    C1 = cross(blk, v2, S, M.m)
    stats["T8"] += 1
    if not C0 <= C1:
        fail("T8-item2", (v, r))
    if nu2 == r:
        S2, _ = avoidable(N0b, blk, k)
        if not S <= S2:
            fail("T8-item1", (v, r, S, S2))
        if S2 == S:
            stats["T8-item3-cases"] += 1
            if not C0 < C1:
                fail("T8-item3", (v, r, S))
        elif S2 > S:
            stats["S-grow"] += 1
    else:
        stats["aug"] += 1
    if not C0 < C1:
        stats["C-not-strict-anyway"] += 1
    # ---------------- Steps 1-5 for every admissible choice
    T = breakpoints(v, M.m)
    delta = None
    for t in T:
        N = Ns.get(t)
        if N is None:
            N = N_posl(M, v, t)
        A, nu = avoidable(N, blk, k)
        if nu > r or A != S:
            delta = t
            break
    if delta is None or not (0 < delta <= tau):
        fail("T8-delta", (v, r, delta, tau))
        return
    for b in range(k):
        if b not in S and lam[b] < delta:
            fail("T8-lam", (v, r, b))
    Nd = Ns.get(delta) or N_posl(M, v, delta)
    ES = Emask(blk, S, M.m)
    rN0 = rank_from_bases(N0, ES)
    if rN0 != len(S) - (k - r):
        fail("T8-rN0", (v, r))
    rNd = rank_from_bases(Nd, ES)
    if not rNd > rN0:
        fail("T8-step2", (v, r, rNd, rN0))
    ud, clus = u_posl(M, v, delta)
    Ndset = set(Nd)
    found_any = False
    for B in N0:
        if popcount(B & ES) != rN0:
            continue
        # N(delta)-span of B cap E(S): y in E(S)-B not spanned
        BES = B & ES
        for y in elems(ES & ~B):
            # y spanned by BES in N(delta)?  rank via bases
            if rank_from_bases(Nd, BES | 1 << y) == popcount(BES):
                continue
            CN = [g for g in elems(B) if ((B & ~(1 << g)) | (1 << y)) in Ndset]
            for g in CN:
                if blk[g] in S:
                    continue
                found_any = True
                stats["step3-choices"] += 1
                if not (ud[y] == ud[g] and ud[y] != INF and M.comp[y] == M.comp[g]):
                    fail("T8-step3-cluster", (v, r, B, y, g))
                    continue
                CM = M.fund_circuit(B, y)
                if not CM >> g & 1:
                    fail("T8-step3-circuit-subset", (v, r, B, y, g))
                if not v[g] < v[y]:
                    fail("T8-step3-strict", (v, r, B, y, g))
                    continue
                cid = clus[y]
                members = [e for e in clus if clus[e] == cid]
                outS = [e for e in members if blk[e] not in S and v[e] < v[y]]
                alpha = max(v[e] for e in outS)
                inS = [e for e in members if blk[e] in S and v[e] > alpha]
                bet = min(v[e] for e in inS)
                if not (0 < bet - alpha <= delta):
                    fail("T8-step4", (v, r, alpha, bet, delta))
                z1s = [e for e in outS if v[e] == alpha]
                z2s = [e for e in inS if v[e] == bet]
                ok = any((z2, z1) in C1 and (z2, z1) not in C0 for z1 in z1s for z2 in z2s)
                if not ok:
                    fail("T8-step5", (v, r))
    if not found_any:
        fail("T8-step3-none", (v, r))
    # ---------------- compilation identity
    pairs = [(e, f) for e in range(M.m) for f in range(M.m) if e != f]
    D = {(e, f): max(v[f] - v[e], F0) for (e, f) in pairs}
    svals = sorted([F0] + list(D.values()))
    acomp = {b: F0 for b in range(k)}
    for i in range(len(svals) - 1):
        gap = svals[i + 1] - svals[i]
        if gap == 0:
            continue
        G = {pq for pq in pairs if D[pq] <= svals[i]}
        G |= {(e, e) for e in range(M.m)}
        N = N_from_relation(M, G)
        A, nu = avoidable(N, blk, k)
        if nu <= r:
            for b in A:
                acomp[b] += gap
    # observable at the full relation
    Gfull = set(pairs) | {(e, e) for e in range(M.m)}
    Nf = N_from_relation(M, Gfull)
    if nu_of(Nf, blk) <= r:
        fail("compile-full", (v, r))
    stats["compile"] += 1
    if acomp != a:
        fail("compile", (v, r, acomp, a))


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(seed)
    stats = {key: 0 for key in ["F1", "F2", "F3", "F4", "rel", "T6", "T8", "T8-item3-cases", "S-grow",
                                "aug", "C-not-strict-anyway", "step3-choices", "compile"]}
    kinds = {}
    done = 0
    while done < trials:
        kind, M = random_matroid(rng)
        if M.k == 0:
            continue
        k = M.k
        blk = rand_blocks(M, k, rng)
        if blk is None:
            continue
        style = rng.choice(["ties", "ties5", "spaced", "mixed", "generic"])
        v = rand_values(M.m, rng, style)
        N0, _ = opt_bases(M, v)
        r = nu_of(N0, blk)
        if r >= k:
            continue
        check_prop7(M, blk, k, v, stats)
        check_thm6_thm8(M, blk, k, v, r, stats)
        kinds[kind] = kinds.get(kind, 0) + 1
        done += 1
    print("instances", done, kinds)
    print("stats", stats)
    print("failures", len(FAIL))


if __name__ == "__main__":
    main()
