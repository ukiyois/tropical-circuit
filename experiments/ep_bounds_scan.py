"""Scan epochs (from log files or random) and report max(n - bound) for candidate bounds.
Usage: python ep_bounds_scan.py source [count]"""
import ast, glob, random, sys
import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from ep_common import epochs

def feats(e, M):
    Bs = e["B"]; S = set(e["S"])
    blk = e["blk"]
    RB = sum(1 for x in range(M.m) if blk[x] in S and Bs >> x & 1)
    UB = sum(1 for x in range(M.m) if blk[x] not in S and Bs >> x & 1)
    return {"n": e["n"], "m": M.m, "k": e["k"], "rho": e["rho"], "U": e["U"], "R": e["R"],
            "RnB": e["R"] - RB, "UnB": e["U"] - UB, "UB": UB}

CANDS = {
    "m-2": lambda f: f["m"] - 2,
    "m-k+rho": lambda f: f["m"] - f["k"] + f["rho"],
    "U+RnB-1": lambda f: f["U"] + f["RnB"] - 1,
    "UnB+RnB+1": lambda f: f["UnB"] + f["RnB"] + 1,
    "UnB+R": lambda f: f["UnB"] + f["R"],
    "U+rho": lambda f: f["U"] + f["rho"],
    "max(U,R)+rho": lambda f: max(f["U"], f["R"]) + f["rho"],
}

def main():
    src = sys.argv[1]
    descs = []
    if src == "random":
        rng = random.Random(11)
        for _ in range(int(sys.argv[2])):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(3, 6); m = rng.randint(n + 2, 12)
            descs.append(random_desc(rng, kind, n, m, rng.choice([4, 10, 20])))
    else:
        for fn in glob.glob(src):
            for line in open(fn):
                if "desc" in line:
                    descs.append(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
    best = {c: (-999, None) for c in CANDS}
    cnt = 0
    for d in descs:
        M = build(d); _, _, blk, w = d; k = M.k
        if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
            continue
        try:
            eps, _ = epochs(M, blk, k, list(w), cap=800)
        except RuntimeError:
            continue
        for e in eps:
            e["blk"] = blk
            f = feats(e, M); cnt += 1
            for c, fn in CANDS.items():
                val = f["n"] - fn(f)
                if val > best[c][0]:
                    best[c] = (val, (f, d))
    print("epochs", cnt)
    for c, (val, info) in best.items():
        print(f"{c:16s} max(n - bound) = {val}   at {info[0] if info else None}")

if __name__ == "__main__":
    main()
