import re, ast
import stage_core as sc, lsu_trace as tr
line = [l for l in open('lsu_logs/search_low_g6_10_b40.txt') if 'data=' in l][0]
data = ast.literal_eval(re.search(r'data=(\[.*?\]) blk', line).group(1))
blk = ast.literal_eval(re.search(r'blk=(\[.*?\]) w', line).group(1))
w = ast.literal_eval(re.search(r'w=(\[.*?\])$', line.strip()).group(1))
M = sc.graphic(6, data); k = M.k
t = tr.trace(M, blk, k, w)
for j, s in enumerate(t):
    print(j, "nu0", s["nu0"], "S0", sorted(s["S0"]), "tau", s["tau"], "a", s["a"], "mis", s["mismatch"], "jumps", s["jumps"])
print("final v", t[-1]["v2"])
print("v0", w)
