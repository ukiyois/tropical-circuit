"""Phase 2e: the gap potential Phi (docs/phase2e-epoch-rho2-2026-10-12.md, Section 2).

For a state v of an epoch (B* fixed) and a component K with raised anchors, let
rho_0 < ... < rho_L be the distinct values of the raised elements of K lying in
[a_K, T_K] (a_K, T_K the least and largest raised-anchor values of K), and
G_i = [rho_{i-1}, rho_i).  A gap is *pending* if no unraised element of K lies in it
and some unraised element of K lies below rho_{i-1}.
    Phi(v) = sum_K ( #{z in U cap K : v_z < T_K} + #{pending gaps of K} ).
Checks per epoch with rho >= 1:  Phi(v^i) - Phi(v^{i+1}) >= 1 for i = 0..n-2,
Phi(v^0) <= P1(v^0), hence n <= 1 + Phi(v^0) <= 1 + P1(v^0).
Variants (expected to fail, to show the check discriminates):
  F0  Phi without the pending term (= #U below T)
  F1  pending gaps counted without the condition 'some unraised element below'
  F2  decrease by >= 2 at every update that is not last
  F3  only the raised anchor values as gap ends (no raised non-anchors)
Usage: python ep2_phi.py SPEC [SPEC ...]   (SPEC: glob of logs or random:count:seed)
"""
import sys

from ep2_common import sources, epoch_states, P1, raised_anchor_values


def phi(rec, v, variant=None):
    M, Bs, R, U = rec["M"], rec["B"], rec["R"], rec["U"]
    vals = raised_anchor_values(rec, v)
    tot = 0
    for c, s in vals.items():
        a, T = s[0], s[-1]
        Uc = [v[z] for z in U if M.comp[z] == c]
        tot += sum(1 for p in Uc if p < T)
        if variant == "F0":
            continue
        if variant == "F3":
            pos = sorted(set(s))
        else:
            pos = sorted({v[x] for x in R if M.comp[x] == c and a <= v[x] <= T})
        for i in range(1, len(pos)):
            lo, hi = pos[i - 1], pos[i]
            empty = not any(lo <= p < hi for p in Uc)
            below = any(p < lo for p in Uc)
            if empty and (below or variant == "F1"):
                tot += 1
    return tot


def main():
    st = {"epochs": 0, "updates": 0, "fail": 0, "P1fail": 0, "tight": 0,
          "F0": 0, "F1": 0, "F2": 0, "F3": 0}
    by_rho = {}
    bad = []
    for spec in sys.argv[1:]:
        for d in sources(spec):
            for rec in epoch_states(d, want_delta=False):
                if rec["rho"] < 1:
                    continue
                st["epochs"] += 1
                by_rho[rec["rho"]] = by_rho.get(rec["rho"], 0) + 1
                sts = rec["states"]
                n = len(sts) - 1
                ph = [phi(rec, v) for v in sts[:n]]
                okall = True
                for i in range(n - 1):
                    st["updates"] += 1
                    if ph[i] - ph[i + 1] < 1:
                        okall = False
                        st["fail"] += 1
                        if len(bad) < 5:
                            bad.append(("Phi", rec["d"], rec["r"], i + 1))
                if ph[0] > P1(rec, sts[0]):
                    st["P1fail"] += 1
                if n - 1 == ph[0]:
                    st["tight"] += 1
                for var in ("F0", "F1", "F3"):
                    pv = [phi(rec, v, var) for v in sts[:n]]
                    if any(pv[i] - pv[i + 1] < 1 for i in range(n - 1)):
                        st[var] += 1
                if any(ph[i] - ph[i + 1] < 2 for i in range(n - 1)):
                    st["F2"] += 1
    print(st, "epochs by rho", dict(sorted(by_rho.items())))
    for b in bad:
        print("FAIL", b)


if __name__ == "__main__":
    main()
