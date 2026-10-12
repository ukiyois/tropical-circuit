"""Scheme F: charge each update injectively to an element of E - (R cap B*) lying in one of
its crossing pairs (x in R, z in U, same component, v_x > v_z before, v'_x <= v'_z after;
anchored or not).  Hall's condition is tested by maximum matching.
Usage: python ep_charge2.py source [count]"""
import ast, glob, random, sys
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from ep_common import epochs
from ep_charge import max_matching

def main():
    src = sys.argv[1]
    descs = []
    if src == "random":
        rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 13)
        for _ in range(int(sys.argv[2])):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(3, 6); m = rng.randint(n + 2, 12)
            descs.append(random_desc(rng, kind, n, m, rng.choice([4, 10, 20])))
    else:
        for fn in glob.glob(src):
            for line in open(fn):
                if "desc" in line:
                    descs.append(ast.literal_eval(line[line.index("desc ") + 5:].strip()))
    st = {"epochs": 0, "failF": 0, "failF_anch": 0, "tightF": 0}
    for d in descs:
        M = build(d); _, _, blk, w = d; k = M.k
        if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
            continue
        try:
            eps, _ = epochs(M, blk, k, list(w), cap=800, want_pairs=True)
        except RuntimeError:
            continue
        for e in eps:
            st["epochs"] += 1
            Bs = e["B"]; S = set(e["S"])
            def ok(x):
                return not (blk[x] in S and Bs >> x & 1)
            cand = [sorted({u for (x, z) in pr for u in (x, z) if ok(u)}) for pr in e["pairs"]]
            mm = max_matching(len(cand), cand)
            if mm < e["n"]:
                st["failF"] += 1
                print("FAIL F", e["r"], e["n"], mm, d)
            # anchored-only version
            cand2 = [sorted({u for (x, z) in pr if (Bs >> x & 1) or (Bs >> z & 1) for u in (x, z) if ok(u)})
                     for pr in e["pairs"]]
            if max_matching(len(cand2), cand2) < e["n"]:
                st["failF_anch"] += 1
    print(st)

if __name__ == "__main__":
    main()
