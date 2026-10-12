import sys
import stage_core as sc
import lsu_trace as tr
# k=6 instance with nu0 seq [1,2,2,...,2,4] would be ideal; use the logged k=6 'low' best
edges=[(2, 6), (0, 2), (6, 2), (3, 5), (3, 4), (4, 6), (6, 3), (5, 1), (2, 5), (1, 0), (1, 2), (4, 1)]
blk=[2, 4, 4, 3, 4, 2, 0, 5, 1, 4, 0, 0]
w=[999, 27669, 254, 65535, 9, 392, 5231, 65535, 32767, 16829, 605, 2332]
M=sc.graphic(7,edges); k=M.k
t=tr.trace(M,blk,k,w)
tr.print_trace(t)
