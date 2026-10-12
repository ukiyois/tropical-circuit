import stage_core as sc, lsu_trace as tr, lsu_core as uc
data=[(4, 0), (0, 2), (1, 2), (3, 4), (2, 1), (2, 3), (0, 3), (4, 0), (1, 3)]; blk=[1, 0, 1, 1, 1, 3, 1, 1, 2]; w=[4242742, 16777215, 951894, 2127425, 636, 12820884, 12108, 2754502, 8864554]
M = sc.graphic(5, data); k = M.k
t = tr.trace(M, blk, k, w)
for j, s in enumerate(t):
    print(j, "v", s["v"])
tr.print_trace(t)
print("final v", t[-1]["v2"])
data=[(0, 2), (1, 2), (1, 0), (1, 4), (0, 2), (3, 4), (4, 1), (3, 0), (0, 3)]; blk=[0, 2, 3, 2, 1, 1, 1, 2, 2]; w=[16777215, 174, 5778559, 132008, 7122328, 9210334, 7168312, 2684759, 1006902]
M = sc.graphic(5, data); k = M.k
t = tr.trace(M, blk, k, w)
for j, s in enumerate(t):
    print(j, "v", s["v"])
tr.print_trace(t)
print("final v", t[-1]["v2"])
