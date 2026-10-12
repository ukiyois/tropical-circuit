"""Charging schemes for epochs: does every epoch admit an injective charge of its
updates to elements?

For an epoch with updates 1..n and anchored crossing pairs A_i (x in R, z in U,
same component, x or z in B*, v_x > v_z before and v'_x <= v'_z after), test:
  (E)  a matching of the updates into elements, update i -> some element of a pair
       in A_i (both x and z allowed);
  (N)  update i -> the non-anchor of a pair in A_i, or the pair itself when both
       are anchors (items: non-anchor elements and anchor pairs);
  (Z)  update i -> the U-element z of a pair in A_i;
  (X)  update i -> the R-element x of a pair in A_i.
Reports the epochs where the maximum matching is smaller than n (Hall fails).
Usage: python ep_charge.py source [count]
  source = 'random' or a glob of log files with 'desc (...)' lines.
"""
import ast
import glob
import random
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from ep_common import epochs


def max_matching(n, cand):
    """cand[i] = list of hashable items; Kuhn's algorithm."""
    owner = {}

    def try_(i, seen):
        for it in cand[i]:
            if it in seen:
                continue
            seen.add(it)
            if it not in owner or try_(owner[it], seen):
                owner[it] = i
                return True
        return False
    size = 0
    for i in range(n):
        if try_(i, set()):
            size += 1
    return size


def schemes(e, M):
    Bs = e["B"]
    out = {}
    cands = {"E": [], "N": [], "Z": [], "X": []}
    for pr in e["pairs"]:
        A = [(x, z) for (x, z) in pr if (Bs >> x & 1) or (Bs >> z & 1)]
        cE, cN, cZ, cX = set(), set(), set(), set()
        for (x, z) in A:
            cE.add(x)
            cE.add(z)
            xa, za = Bs >> x & 1, Bs >> z & 1
            if xa and za:
                cN.add(("pair", x, z))
            elif xa:
                cN.add(z)
            else:
                cN.add(x)
            cZ.add(z)
            cX.add(x)
        cands["E"].append(sorted(cE, key=str))
        cands["N"].append(sorted(cN, key=str))
        cands["Z"].append(sorted(cZ, key=str))
        cands["X"].append(sorted(cX, key=str))
    for key, c in cands.items():
        out[key] = max_matching(len(c), c)
    return out


def run_desc(d, stats, bad, cap=600):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return
    try:
        eps, _ = epochs(M, blk, k, list(w), cap=cap, want_pairs=True)
    except RuntimeError:
        return
    for e in eps:
        stats["epochs"] += 1
        stats["maxn"] = max(stats["maxn"], e["n"])
        s = schemes(e, M)
        for key, val in s.items():
            if val < e["n"]:
                stats["fail_" + key] += 1
                if len(bad[key]) < 5:
                    bad[key].append((d, e["r"], e["n"], val))


def main():
    src = sys.argv[1]
    stats = {"epochs": 0, "maxn": 0, "fail_E": 0, "fail_N": 0, "fail_Z": 0, "fail_X": 0}
    bad = {"E": [], "N": [], "Z": [], "X": []}
    if src == "random":
        count = int(sys.argv[2]) if len(sys.argv) > 2 else 500
        rng = random.Random(77)
        for it in range(count):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(3, 6)
            m = rng.randint(n + 2, 12)
            d = random_desc(rng, kind, n, m, rng.choice([4, 10, 20]))
            run_desc(d, stats, bad)
    else:
        for f in glob.glob(src):
            for line in open(f):
                if "desc" in line:
                    d = ast.literal_eval(line[line.index("desc ") + 5:].strip())
                    run_desc(d, stats, bad)
    print(stats)
    for key, lst in bad.items():
        for item in lst:
            print("FAIL", key, item)


if __name__ == "__main__":
    main()
