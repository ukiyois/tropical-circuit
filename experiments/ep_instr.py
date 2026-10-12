"""Per-update instrumentation of epochs.

For every update of every epoch (schedule from p = 0):
  rigid    all unraised blocks rise by tau (a_b = 0 for b notin S0)
  case     the case of Theorem 2.4 (stage_epoch_cases.designated): i, ii, iii, iv
  pair     the designated pair (x, z)
Greedy online charging rules (an update is charged to an uncharged element of one
of its anchored crossing pairs, in a fixed priority; failure = all charged):
  G1  priority: U non-anchor, R non-anchor, R anchor, U anchor
  G2  priority: the designated pair's non-anchor, then the designated pair's other
      element, then any element of an anchored pair
Usage: python ep_instr.py source   (source as in ep_charge.py)
"""
import ast
import glob
import random
import sys

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r
from stage_epoch_cases import designated


def run(d, stats, bad):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return
    v = list(w)
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        Scur = None
        log = []
        steps = 0
        while True:
            nu, S = sc.state(M, blk, k, v)
            if nu > r or S != Scur:
                if log:
                    finish(log, stats, bad, d, r, Bs)
                log = []
                if nu > r:
                    break
                Scur = S
                Bs = base_meeting_r(M, blk, k, v, r)
                R = [e for e in range(M.m) if blk[e] in S]
                U = [e for e in range(M.m) if blk[e] not in S]
            try:
                c, pair = designated(M, blk, k, v, r, S, Bs)
            except Exception:
                c, pair = "?", None
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            rigid = all(a[b] == 0 for b in range(k) if b not in S)
            v2 = sc.shift(v, blk, a)
            pr = [(x, z) for x in R for z in U if M.comp[x] == M.comp[z] and v[x] > v[z] and v2[x] <= v2[z]
                  and ((Bs >> x & 1) or (Bs >> z & 1))]
            log.append({"case": c, "pair": pair, "rigid": rigid, "A": pr})
            v = v2
            steps += 1
            if steps > 800:
                return


def finish(log, stats, bad, d, r, Bs):
    stats["epochs"] += 1
    n = len(log)
    stats["updates"] += n
    stats["nonrigid"] += sum(1 for u in log if not u["rigid"])
    if any(not u["rigid"] for u in log) and n >= 4:
        stats["long_nonrigid_epochs"] += 1
    for u in log:
        stats["case_" + u["case"]] = stats.get("case_" + u["case"], 0) + 1
    # G1
    for rule in ("G1", "G2"):
        charged = set()
        ok = True
        for u in log:
            cands = []
            if rule == "G1":
                pri = []
                for (x, z) in u["A"]:
                    xa, za = Bs >> x & 1, Bs >> z & 1
                    if not za:
                        pri.append((0, z))
                    if not xa:
                        pri.append((1, x))
                    if xa:
                        pri.append((2, x))
                    if za:
                        pri.append((3, z))
                cands = [e for _, e in sorted(pri)]
            else:
                if u["pair"]:
                    x, z = u["pair"]
                    na = z if not (Bs >> z & 1) else x
                    cands = [na, x if na == z else z]
                for (x, z) in u["A"]:
                    cands += [x, z]
            pick = next((e for e in cands if e not in charged), None)
            if pick is None:
                ok = False
                break
            charged.add(pick)
        if not ok:
            stats["fail_" + rule] += 1
            if len(bad[rule]) < 4:
                bad[rule].append((d, r, n))


def main():
    src = sys.argv[1]
    stats = {"epochs": 0, "updates": 0, "nonrigid": 0, "long_nonrigid_epochs": 0, "fail_G1": 0, "fail_G2": 0}
    bad = {"G1": [], "G2": []}
    if src == "random":
        count = int(sys.argv[2]) if len(sys.argv) > 2 else 300
        rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
        for it in range(count):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(3, 6)
            m = rng.randint(n + 2, 12)
            run(random_desc(rng, kind, n, m, rng.choice([4, 10, 20])), stats, bad)
    else:
        for f in glob.glob(src):
            for line in open(f):
                if "desc" in line:
                    run(ast.literal_eval(line[line.index("desc ") + 5:].strip()), stats, bad)
    print(stats)
    for key, lst in bad.items():
        for item in lst:
            print("FAIL", key, item)


if __name__ == "__main__":
    main()
