"""Lower bound: T_LS can exceed m + 2.  At a state with nu0 = k - 1 the LS block is the
regular update of stage k - 1, so T_LS(v) equals the length of the regular last stage from
v.  Instance: docs/phase2d, Section 6 (graphic, k = 7, m = 14, stage 6 of 20 updates).
Here w' := the state at which the regular schedule from w enters stage 6; LS from w'
(p = 0) is run and compared; Psi = Opt is checked for the run from w'.  Also the referee
implementation recomputes nu0 at w'.
Usage: python lsu_lower.py"""
import sys
import stage_core as sc
import ls_core as lc

edges = [(7, 5), (2, 4), (6, 4), (3, 6), (5, 3), (1, 4), (6, 4), (4, 6), (6, 5), (1, 3), (2, 1),
         (4, 7), (7, 0), (0, 4)]
blk = [6, 5, 0, 3, 1, 4, 1, 4, 1, 4, 2, 1, 6, 3]
w = [430261, 4251475, 2240075, 19124, 153712, 3840, 2342092, 1171454, 102834, 307393, 16777218,
     46321, 200643, 256338]
M = sc.graphic(8, edges)
k = M.k
print("k", k, "m", M.m)
v = list(w)
lens = []
for r in range(1, k):
    nu0, _ = sc.state(M, blk, k, v)
    if r == k - 1:
        w2 = list(v)
    if nu0 > r:
        lens.append(0)
        continue
    c, v = sc.run_stage(M, blk, k, v, r)
    lens.append(c)
print("regular stage lengths from w:", lens)
nu_w2, _ = sc.state(M, blk, k, w2)
print("w' (entry of stage", k - 1, "):", w2, "nu0(w') =", nu_w2)
T, vl, nus, mono = lc.ls_iterate(M, blk, k, w2, cap=500)
opt = sc.opt_rainbow(M, blk, k, w2)
print("T_LS(w') =", T, " m + 6 =", M.m + 6, " Psi=Opt:", sc.psi_from_v(M, blk, k, w2, vl) == opt,
      " nu0 seq:", nus)
sys.path.insert(0, "referee_phase2a")
import core as ref
from fractions import Fraction
Mr = ref.graphic(8, edges)
vr = [Fraction(x) for x in w2]
Tr = 0
while True:
    A, nu = ref.avoidable(ref.opt_bases(Mr, vr)[0], blk, k)
    if nu == k:
        break
    tau, lam, a, Ns = ref.posl_update(Mr, blk, k, vr, k - 1)
    vr = [vr[e] - a[blk[e]] for e in range(Mr.m)]
    Tr += 1
print("referee: updates of stage", k - 1, "from w' =", Tr, " final state equal:", vr == [Fraction(x) for x in vl])
