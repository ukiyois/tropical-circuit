"""Phase 2e common tools (docs/phase2e-epoch-rho2-2026-10-12.md).  Exact integer arithmetic.

epoch_states(d): run the PO-SL schedule of the descriptor d from p = 0 and yield, per
epoch, a record with the stage r, S0, rho, B* (fixed at the first state), R, U and the
list of states v^0, ..., v^n of the epoch (v^n is the first state after it), together
with delta and tau of every update.

sources(spec): descriptors from a glob of log files (lines with 'desc ') or
'random:count:seed' (graphic and binary instances as in ep_conjQ.py).
"""
import ast
import glob
import random

import stage_core as sc
from stage_search import build, has_rainbow
from stage_search_exp import random_desc
from stage_epoch_check import base_meeting_r, first_event, D_of


def sources(spec):
    if spec.startswith("random:"):
        _, cnt, seed = spec.split(":")
        rng = random.Random(int(seed))
        for _ in range(int(cnt)):
            kind = rng.choice(["graphic", "graphic", "binary"])
            n = rng.randint(4, 7)
            m = rng.randint(n + 2, 13)
            yield random_desc(rng, kind, n, m, rng.choice([3, 6, 12, 20]))
        return
    for f in sorted(glob.glob(spec)):
        for line in open(f):
            if "desc " in line:
                yield ast.literal_eval(line[line.index("desc ") + 5:].strip())


def epoch_states(d, cap=800, want_delta=True):
    M = build(d)
    _, _, blk, w = d
    k = M.k
    if k < 2 or sorted(set(blk)) != list(range(k)) or not has_rainbow(M, blk, k):
        return
    v = list(w)
    steps = 0
    for r in range(1, k):
        nu, S = sc.state(M, blk, k, v)
        if nu > r:
            continue
        rec = None
        while True:
            nu, S = sc.state(M, blk, k, v)
            if rec is not None and (nu > r or S != rec["S"]):
                rec["states"].append(list(v))
                yield rec
                rec = None
            if nu > r:
                break
            if rec is None:
                Bs = base_meeting_r(M, blk, k, v, r)
                R = {e for e in range(M.m) if blk[e] in S}
                rec = {"d": d, "M": M, "blk": blk, "k": k, "r": r, "S": S,
                       "rho": len(S) - (k - r), "B": Bs, "R": R,
                       "U": {e for e in range(M.m) if e not in R},
                       "states": [], "delta": [], "tau": []}
            delta = first_event(M, blk, k, v, r, S) if want_delta else None
            tau, lam, a, _ = sc.update(M, blk, k, v, r)
            rec["states"].append(list(v))
            rec["delta"].append(delta)
            rec["tau"].append(tau)
            v = sc.shift(v, blk, a)
            steps += 1
            if steps > cap:
                return


def raised_anchor_values(rec, v):
    """per component: sorted distinct values of the raised anchors."""
    M, Bs, R = rec["M"], rec["B"], rec["R"]
    vals = {}
    for h in R:
        if Bs >> h & 1:
            vals.setdefault(M.comp[h], set()).add(v[h])
    return {c: sorted(s) for c, s in vals.items()}


def P1(rec, v):
    M, Bs, R = rec["M"], rec["B"], rec["R"]
    tops = {c: s[-1] for c, s in raised_anchor_values(rec, v).items()}
    return sum(1 for e in range(M.m) if not (e in R and Bs >> e & 1)
               and M.comp[e] in tops and v[e] < tops[M.comp[e]])
