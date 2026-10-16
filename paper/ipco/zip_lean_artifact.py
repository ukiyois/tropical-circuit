"""Pack lean-artifact/ (without .lake) into lean-artifact.zip for the submission."""
import os
import re
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "lean-artifact")
OUT = os.path.join(HERE, "lean-artifact.zip")
TOP = "greedy-intersection-lean"
BANNED = re.compile(r"Wang|ukiyo|Dsektop|signed_assignment|greedy_intersection\.tex")
SORRY = re.compile(r"\bsorry\b")

count = 0
with zipfile.ZipFile(OUT, "w", zipfile.ZIP_DEFLATED) as z:
    for dp, dn, fn in os.walk(SRC):
        dn[:] = sorted(d for d in dn if d != ".lake")
        for f in sorted(fn):
            if f == "NameCheck.lean":
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, SRC).replace(os.sep, "/")
            with open(p, encoding="utf-8") as fh:
                text = fh.read()
            m = BANNED.search(text) or (f.endswith(".lean") and SORRY.search(text))
            if m:
                raise SystemExit("%s contains %r" % (rel, m.group(0)))
            z.write(p, TOP + "/" + rel)
            count += 1
print("%s: %d files, %.0f KB" % (OUT, count, os.path.getsize(OUT) / 1024))
