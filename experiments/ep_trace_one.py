"""Trace one instance given on the command line as a Python literal descriptor."""
import ast
import sys

from stage_search import build
from ep_trace import trace_instance

if __name__ == "__main__":
    d = ast.literal_eval(sys.argv[1])
    only = int(sys.argv[2]) if len(sys.argv) > 2 else None
    M = build(d)
    res, _ = trace_instance(M, d[2], M.k, d[3], only_r=only)
    print("epochs (r, rho, |U|, |R|, n):", [(e["r"], e["rho"], e["U"], e["R"], e["n"]) for e in res])
