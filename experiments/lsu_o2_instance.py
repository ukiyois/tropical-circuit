"""The run of lsu_observe.py in which every block is raised at some step (O2 fails).
M = graphic on 8 vertices = disjoint union of A (vertices 0..3) and B (vertices 4..7);
k = 5, m = 12.  Prints the trace, p_T, and recomputes the run with the referee
implementation (referee_phase2a/core.py, the stage-(k-1) block via posl_update at every
state, valid at nu0 = k - 1 only, so the referee is used only for nu0 and the final Psi).
Usage: python lsu_o2_instance.py"""
import sys
from fractions import Fraction
import stage_core as sc
import lsu_core as uc
import lsu_trace as tr
A = [(1, 2), (3, 2), (1, 3), (3, 1), (3, 1), (1, 2)]
B = [(0, 2), (2, 3), (1, 2), (0, 3), (1, 0), (3, 2)]
edges = A + [(x + 4, y + 4) for (x, y) in B]
blk = [3, 2, 4, 2, 1, 3, 2, 0, 3, 4, 0, 1]
w = [32, 129, 22, 128, 66, 129, 74, 64, 0, 0, 128, 2]
M = sc.graphic(8, edges)
k = M.k
print("k", k, "m", M.m, "components", M.comp)
t = tr.trace(M, blk, k, w)
tr.print_trace(t)
states, blocks = uc.ls_run(M, blk, k, w)
print("p_j:", [s["p"] for s in states])
print("min p_T =", min(states[-1]["p"]))
print("Psi = Opt:", sc.psi_from_v(M, blk, k, w, states[-1]["v"]) == sc.opt_rainbow(M, blk, k, w))
sys.path.insert(0, "referee_phase2a")
import core as ref
Mr = ref.graphic(8, edges)
for j, s in enumerate(states):
    A_, nu = ref.avoidable(ref.opt_bases(Mr, [Fraction(x) for x in s["v"]])[0], blk, k)
    print("referee nu0 at state", j, "=", nu, " ours =", s["nu"])
