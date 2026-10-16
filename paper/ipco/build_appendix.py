"""Build appendix.tex and gi_ipco.bib of the IPCO version from the full paper.

appendix_src.tex holds the text of the appendix with placeholders; every proof and
appendix-only statement, except the proof of Lemma lem:updint written there, is
copied from ../greedy_intersection.tex, so the two versions cannot drift apart.  The IPCO version has no figures; references to the figures
of the full paper are dropped.  Placeholders:

  %%ENV:label%%        the theorem-like environment carrying \\label{label}
  %%PROOF:label%%      the proof that follows that environment
  %%PROOFREF:label%%   that proof headed "Proof of Theorem~\\ref{label}" (or Lemma, ...),
                       for a result stated in the main text
  %%PROOFBODY:label%%  the same proof without \\begin{proof} and \\end{proof}
  %%PROOFOF:label%%    the proof of a main theorem, with its heading
  %%STAGE:lemma%%, %%STAGE:theorem%%
                       the proof of the stage length theorem, split into the
                       proof of Lemma lem:crossing and the counting
  %%CROSSING%%         Lemma lem:crossing: the statement of the stage length
                       theorem without its last sentence
  %%CHECKS%%           the list of computational checks
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MASTER = os.path.join(HERE, "..", "greedy_intersection.tex")
SRC = os.path.join(HERE, "appendix_src.tex")
OUT = os.path.join(HERE, "appendix.tex")
BIB_IN = os.path.join(HERE, "..", "greedy_intersection.bib")
BIB_OUT = os.path.join(HERE, "gi_ipco.bib")

THEOREM_ENVS = ("theorem", "lemma", "proposition", "corollary", "definition")


def fail(msg):
    sys.exit("build_appendix: " + msg)


def read(path):
    with io.open(path, encoding="utf-8") as f:
        return f.read().replace("\r\n", "\n")


master = read(MASTER)


def label_pos(label):
    key = "\\label{" + label + "}"
    if master.count(key) != 1:
        fail("label %s occurs %d times" % (label, master.count(key)))
    return master.index(key)


def env_span(label):
    """Start and end of the theorem-like environment that carries the label."""
    pos = label_pos(label)
    best = None
    for env in THEOREM_ENVS:
        i = master.rfind("\\begin{" + env + "}", 0, pos)
        if i >= 0 and (best is None or i > best[0]):
            best = (i, env)
    if best is None:
        fail("no environment for " + label)
    start, env = best
    end_tag = "\\end{" + env + "}"
    end = master.index(end_tag, pos) + len(end_tag)
    return start, end


def env(label):
    start, end = env_span(label)
    return master[start:end]


def proof_after(label):
    _, end = env_span(label)
    i = master.index("\\begin{proof}", end)
    between = master[end:i]
    if between.strip():
        fail("text between %s and its proof: %r" % (label, between.strip()[:60]))
    j = master.index("\\end{proof}", i) + len("\\end{proof}")
    return master[i:j]


def proof_body(label):
    p = proof_after(label)
    p = p[len("\\begin{proof}"):-len("\\end{proof}")]
    return p.strip("\n")


def proof_of(label):
    head = "\\begin{proof}[Proof of Theorem~\\ref{" + label + "}]"
    if master.count(head) != 1:
        fail("proof of %s occurs %d times" % (label, master.count(head)))
    i = master.index(head)
    j = master.index("\\end{proof}", i) + len("\\end{proof}")
    return master[i:j]


KINDS = {"thm": "Theorem", "lem": "Lemma", "cor": "Corollary", "prop": "Proposition"}


def proof_ref(label):
    """The proof of a result of the main text, headed by a reference to it."""
    kind = KINDS[label.split(":")[0]]
    p = proof_after(label)
    return ("\\begin{proof}[Proof of " + kind + "~\\ref{" + label + "}]"
            + p[len("\\begin{proof}"):])


def stage_parts():
    body = proof_body("thm:stagelength")
    parts = re.split(r"(?=\\emph\{Step \d+,)", body)
    intro, steps = parts[0], parts[1:]
    if len(steps) != 7:
        fail("stage length proof has %d steps" % len(steps))
    for n, s in enumerate(steps, 1):
        if not s.startswith("\\emph{Step %d," % n):
            fail("stage length step %d out of order" % n)

    def sub(text, old, new, count=1):
        found = len(re.findall(old, text))
        if found != count:
            fail("pattern %r found %d times" % (old, found))
        return re.sub(old, lambda _: new, text)

    s6 = sub(steps[5], r"\\emph\{Step 6, item 3\.\}", "\\emph{Step 5, item 3.}")
    lemma = ("\\begin{proof}\n" + intro + steps[0] + steps[1] + steps[2] + steps[3]
             + s6.rstrip("\n") + "\n\\end{proof}")
    s5 = sub(steps[4], r"\\emph\{Step 5, counting within phases\.\}",
             "\\emph{Step 1, counting within phases.}")
    s5 = sub(s5, r"by item 2", "by Lemma~\\ref{lem:crossing}(2)")
    s5 = sub(s5, r"by\s+item 1", "by Lemma~\\ref{lem:crossing}(1)")
    s7 = sub(steps[6], r"\\emph\{Step 7, counting across phases\.\}",
             "\\emph{Step 2, counting across phases.}")
    s7 = sub(s7, r"so item 3 applies", "so Lemma~\\ref{lem:crossing}(3) applies")
    s7 = sub(s7, r"With Step 5,", "With Step 1,")
    theorem = ("\\begin{proof}[Proof of Theorem~\\ref{thm:stagelength}]\n"
               "Write $\\rho=|S_0|-(k-r)$.\n\n" + s5 + s7.rstrip("\n") + "\n\\end{proof}")
    return lemma, theorem


def crossing():
    """Lemma lem:crossing: items 1-3 of thm:stagelength, without the stage bound."""
    s = env("thm:stagelength")
    key = "\\label{thm:stagelength}"
    head = s.index(key) + len(key)
    cut = s.index("Consequently")
    return ("\\begin{lemma}\n\\label{lem:crossing}\n" + s[head:cut].strip("\n")
            + "\n\\end{lemma}")


def checks():
    head = "\\paragraph{Computational checks.}"
    i = master.index(head)
    j = master.index("\\end{itemize}", i) + len("\\end{itemize}")
    return master[i:j]


def fill(src):
    lemma, theorem = stage_parts()

    def repl(m):
        kind, arg = m.group(1), m.group(2)
        if kind == "ENV":
            return env(arg)
        if kind == "PROOF":
            return proof_after(arg)
        if kind == "PROOFREF":
            return proof_ref(arg)
        if kind == "PROOFBODY":
            return proof_body(arg)
        if kind == "PROOFOF":
            return proof_of(arg)
        if kind == "STAGE":
            return lemma if arg == "lemma" else theorem
        fail("unknown placeholder " + kind)

    out = re.sub(r"%%(ENV|PROOF|PROOFREF|PROOFBODY|PROOFOF|STAGE):([^%]+)%%", repl, src)
    out = out.replace("%%CHECKS%%", checks())
    out = out.replace("%%CROSSING%%", crossing())
    return out


# Replacements for references that change between the two versions.
RULES = [
    (r"\s*\(Figure~\\ref\{fig:[a-z]+\}\)", ""),
    # only theorems carry names in the IPCO version
    (r"\\begin\{(lemma|corollary|proposition|definition)\}\[[^\]]*\]", r"\\begin{\1}"),
    # the term of the IPCO line of work for circuits over max, + and -
    (r"signed\s+tropical\s+complexity", r"$(\\max,+,-)$-circuit complexity"),
    (r"signed\s+tropical\s+circuits", r"$(\\max,+,-)$-circuits"),
    (r"signed\s+tropical\s+circuit", r"$(\\max,+,-)$-circuit"),
    (r"signed\s+circuits", r"$(\\max,+,-)$-circuits"),
    (r"signed\s+circuit\b", r"$(\\max,+,-)$-circuit"),
    (r"the integral\s+formula \\eqref\{eq:update-integral\}",
     r"the integral formula of Lemma~\\ref{lem:updint}"),
    (r"\\eqref\{eq:update-integral\}", r"Lemma~\\ref{lem:updint}"),
    (r"the paragraph after\s+Definition~\\ref\{def:update\}", r"Lemma~\\ref{lem:updint}"),
    (r"Proposition~\\ref\{prop:nphard\}", r"Proposition~\\ref{prop:obstacles}(2)"),
    (r"Proposition~\\ref\{prop:notmatroid\}", r"Proposition~\\ref{prop:obstacles}(1)"),
    (r"Theorem~\\ref\{thm:stagelength\}\(1\)", r"Lemma~\\ref{lem:crossing}(1)"),
    (r"the dual circuit of\s+Corollary~\\ref\{cor:classes\}\(4\)",
     r"the dual rank circuit of the proof of Corollary~\\ref{cor:classes}(4)"),
    (r"Step 1 of the proof of\s+Theorem~\\ref\{thm:stagelength\}",
     r"Step 1 of the proof of Lemma~\\ref{lem:crossing}"),
]

# cor:classes is stated in the IPCO version with the sizes of h_M only; the
# sizes of the rank circuits move into the proof.
CLASSES_RULES = [
    (r"Theorem~\\ref\{thm:A\} with \$k\\le r\$\s+gives the second bound\.",
     r"Theorem~\\ref{thm:A} with $k\\le r$ gives the bound of item 1."),
    (r"Counting costs \$11r\\lceil\\log_2\(r\+1\)\\rceil\$ gates and\s+the constant \$1\$ one gate, "
     r"and Theorem~\\ref\{thm:A\}, applied to the exact count with\s+\$k\\le r\$ and \$q\\ge2\$, gives "
     r"the second bound\.",
     r"Counting costs $11r\\lceil\\log_2(r+1)\\rceil$ gates and the constant $1$ one gate, so the "
     r"rank circuit has\n\\[\n  m(6q^{2}r^{2}+3qr^{2}+r^{2}+qr+6r+1)+11r\\lceil\\log_2(r+1)\\rceil+1"
     r"\n\\]\ngates, and Theorem~\\ref{thm:A}, applied to this count with $k\\le r$ and $q\\ge2$, "
     r"gives the bound of item 2."),
    (r"\$2\^\{19\}\(m\+1\)\(r\+1\)\^\{2\}\(r\(r\+b\)\+1\)\^\{6\}\$ gates\.",
     r"$2^{19}(m+1)(r+1)^{2}(r(r+b)+1)^{6}$ gates, and Theorem~\\ref{thm:A} with $k\\le r$ gives the "
     r"bound of item 3."),
    (r"the result is \$r\^\{\*\}\(S\)\$, at\s+\$s\+m\+1\+11\(m\+1\)W\$ gates\.",
     r"the result is $r^{*}(S)$, at $s+m+1+11(m+1)W$ gates, and Theorem~\\ref{thm:A} for $M^{*}$ "
     r"gives the bound of item 4."),
    (r"item 1 with \$r=n\$ and item 4 with\s+Theorem~\\ref\{thm:A\} give the two bounds\.",
     r"item 1 with $r=n$ gives the first bound, and the rank circuits of the proofs of items 1 "
     r"and 4 with Theorem~\\ref{thm:A} give the second."),
]


# Displays of the full paper that are wider than the LNCS text: the same
# formulas, broken over lines.  Each rule must apply exactly once.
LAYOUT_RULES = [
    ("  v\\leftarrow x_eA_{\\cdot e},\\qquad v\\leftarrow v-[f_p]\\,v_p\\,b_p\\ \\ (p=1,\\ldots,r),\\qquad\n"
     "  f_p\\leftarrow f_p\\vee\\ell_p,\\qquad b_p\\leftarrow\\ell_p\\,?\\,v_p^{-1}v:b_p\n",
     "  \\begin{gathered}\n"
     "  v\\leftarrow x_eA_{\\cdot e},\\qquad v\\leftarrow v-[f_p]\\,v_p\\,b_p\\ \\ (p=1,\\ldots,r),\\\\\n"
     "  f_p\\leftarrow f_p\\vee\\ell_p,\\qquad b_p\\leftarrow\\ell_p\\,?\\,v_p^{-1}v:b_p\n"
     "  \\end{gathered}\n"),
    ("  r^{*}(S)=|S|+r(E\\setminus S)-r(E)\n"
     "  \\equiv\\bigl(2^{W}-(r(E)\\bmod2^{W})\\bigr)+\\sum_{e\\in S}1+r(E\\setminus S)\\pmod{2^{W}},\n",
     "  \\begin{aligned}\n"
     "  r^{*}(S)&=|S|+r(E\\setminus S)-r(E)\\\\\n"
     "  &\\equiv\\bigl(2^{W}-(r(E)\\bmod2^{W})\\bigr)+\\sum_{e\\in S}1+r(E\\setminus S)\\pmod{2^{W}},\n"
     "  \\end{aligned}\n"),
    ("  \\theta(B)=\\max\\Bigl(0,\\ \\max_{f\\in B}v_f-\\min_{e\\notin B}v_e\\Bigr),\\qquad\n"
     "  \\bigl(\\theta(ab),\\theta(ac),\\theta(ad),\\theta(bc),\\theta(bd),\\theta(cd)\\bigr)=(0,1,2,2,3,3).\n",
     "  \\begin{gathered}\n"
     "  \\theta(B)=\\max\\Bigl(0,\\ \\max_{f\\in B}v_f-\\min_{e\\notin B}v_e\\Bigr),\\\\\n"
     "  \\bigl(\\theta(ab),\\theta(ac),\\theta(ad),\\theta(bc),\\theta(bd),\\theta(cd)\\bigr)=(0,1,2,2,3,3).\n"
     "  \\end{gathered}\n"),
    ("  y\\to x\\ \\ \\text{if }I-x+y\\text{ is independent},\\qquad\n"
     "  x\\to y\\ \\ \\text{if }\\blk(y)=\\blk(x)\\qquad(x\\in I,\\ y\\notin I),\n",
     "  y\\to x\\ \\ \\text{if }I-x+y\\text{ is independent},\\quad\n"
     "  x\\to y\\ \\ \\text{if }\\blk(y)=\\blk(x)\\quad(x\\in I,\\ y\\notin I),\n"),
    ("  u_t(f)\\le u_t(e)\\quad\\text{since}\\quad\n"
     "  \\begin{cases}\n"
     "    u_t(e)=m+1,&e\\notin\\PO_t,\\\\\n"
     "    \\text{clusters are ordered by value},&e\\in\\PO_t,\\ v_f\\le v_e,\\\\\n"
     "    0<v_f-v_e\\le\\theta(B)\\le t\\text{ links }e\\text{ and }f,&e\\in\\PO_t,\\ v_f>v_e,\n"
     "  \\end{cases}\n",
     "  \\begin{gathered}\n"
     "  u_t(f)\\le u_t(e)\\quad\\text{since}\\\\\n"
     "  \\begin{cases}\n"
     "    u_t(e)=m+1,&e\\notin\\PO_t,\\\\\n"
     "    \\text{clusters are ordered by value},&e\\in\\PO_t,\\ v_f\\le v_e,\\\\\n"
     "    0<v_f-v_e\\le\\theta(B)\\le t\\text{ links }e\\text{ and }f,&e\\in\\PO_t,\\ v_f>v_e,\n"
     "  \\end{cases}\n"
     "  \\end{gathered}\n"),
    ("  u_t(x)<u_t(y)\\iff t\\ge t_x\\ \\text{and}\\\n"
     "  \\bigl(t<t_y\\ \\text{or}\\ t<\\min(T_{xy},v_y-v_x)\\bigr)\\iff t_x\\le t<\\omega_{xy},\n",
     "  \\begin{aligned}\n"
     "  u_t(x)<u_t(y)&\\iff t\\ge t_x\\ \\text{and}\\\n"
     "  \\bigl(t<t_y\\ \\text{or}\\ t<\\min(T_{xy},v_y-v_x)\\bigr)\\\\\n"
     "  &\\iff t_x\\le t<\\omega_{xy},\n"
     "  \\end{aligned}\n"),
    ("  \\alpha=\\max\\{v_z:z\\notin E_{S_0},\\ v_z<v_y\\}=v_{z_1},\\qquad\n",
     "  \\alpha=\\max\\{v_z:z\\notin E_{S_0},\\ v_z<v_y\\}=v_{z_1},\\quad\n"),
    ("  \\mathbf 1\\bigl[|I|\\le r_0\\bigr]\\wedge\\mathbf 1\\bigl[b\\in\\{b:b\\text{ missed by }I\\}\\cup\\blk(I\\cap Z)\\bigr]\n"
     "  =\\mathbf 1\\bigl[\\nu(N_x)\\le r_0\\bigr]\\wedge\\mathbf 1\\bigl[b\\in\\Av(N_x)\\bigr].\n",
     "  \\begin{aligned}\n"
     "  &\\mathbf 1\\bigl[|I|\\le r_0\\bigr]\\wedge\\mathbf 1\\bigl[b\\in\\{b:b\\text{ missed by }I\\}\\cup\\blk(I\\cap Z)\\bigr]\\\\\n"
     "  &\\qquad=\\mathbf 1\\bigl[\\nu(N_x)\\le r_0\\bigr]\\wedge\\mathbf 1\\bigl[b\\in\\Av(N_x)\\bigr].\n"
     "  \\end{aligned}\n"),
    ("  A\\text{ independent in }N_t\\iff y\\in\\PO\\ \\text{and}\\\n"
     "  r_M\\bigl(\\mathrm{Below}(y)\\cup(A\\cap\\mathrm{Lev}(y))\\bigr)\n"
     "  =r_M\\bigl(\\mathrm{Below}(y)\\bigr)+|A\\cap\\mathrm{Lev}(y)|.\n",
     "  \\begin{aligned}\n"
     "  &A\\text{ independent in }N_t\\iff y\\in\\PO\\ \\text{and}\\\\\n"
     "  &\\qquad r_M\\bigl(\\mathrm{Below}(y)\\cup(A\\cap\\mathrm{Lev}(y))\\bigr)\n"
     "  =r_M\\bigl(\\mathrm{Below}(y)\\bigr)+|A\\cap\\mathrm{Lev}(y)|.\n"
     "  \\end{aligned}\n"),
    ("  \\sum_{r=1}^{k-1}\\ell_r\\le(k-1)\\bigl(1+k(2m-k-1)\\bigr)\\le(k-1)(1+2km)\n"
     "  =2k^{2}m-(2km-k+1)\\le2k^{2}m.\n",
     "  \\begin{aligned}\n"
     "  \\sum_{r=1}^{k-1}\\ell_r&\\le(k-1)\\bigl(1+k(2m-k-1)\\bigr)\\le(k-1)(1+2km)\\\\\n"
     "  &=2k^{2}m-(2km-k+1)\\le2k^{2}m.\n"
     "  \\end{aligned}\n"),
    ("  X\\times\\{1\\}\\cup(E\\setminus X)\\times\\{2\\}\\in\\Bases(N)\n"
     "  \\iff X\\in\\Bases(M_1),\\ E\\setminus X\\in\\Bases(M_2^{*})\n"
     "  \\iff X\\in\\Bases(M_1)\\cap\\Bases(M_2),\n",
     "  \\begin{aligned}\n"
     "  X\\times\\{1\\}\\cup(E\\setminus X)\\times\\{2\\}\\in\\Bases(N)\n"
     "  &\\iff X\\in\\Bases(M_1),\\ E\\setminus X\\in\\Bases(M_2^{*})\\\\\n"
     "  &\\iff X\\in\\Bases(M_1)\\cap\\Bases(M_2),\n"
     "  \\end{aligned}\n"),
    ("  X\\text{ is linked from }S\\iff X\\cap B=\\varnothing\\text{ for some }B\\in\\Bases(T)\n"
     "  \\iff X\\text{ is independent in }T^{*}.\n",
     "  \\begin{aligned}\n"
     "  X\\text{ is linked from }S&\\iff X\\cap B=\\varnothing\\text{ for some }B\\in\\Bases(T)\\\\\n"
     "  &\\iff X\\text{ is independent in }T^{*}.\n"
     "  \\end{aligned}\n"),
    ("  36(v+1)(v+a+1)^{2}(2v+a+1)+(v+1)+11(v+1)\\lceil\\log_2(v+1)\\rceil\n"
     "  \\le48(v+1)(v+a+1)^{2}(2v+a+1)\n",
     "  \\begin{aligned}\n"
     "  &36(v+1)(v+a+1)^{2}(2v+a+1)+(v+1)+11(v+1)\\lceil\\log_2(v+1)\\rceil\\\\\n"
     "  &\\qquad\\le48(v+1)(v+a+1)^{2}(2v+a+1)\n"
     "  \\end{aligned}\n"),
]


def apply_layout(text):
    for old, new in LAYOUT_RULES:
        n = text.count(old)
        if n != 1:
            fail("layout rule %r applies %d times" % (old.strip()[:40], n))
        text = text.replace(old, new)
    return text


def apply_rules(text, rules):
    for old, new in rules:
        text = re.sub(old, new, text)
    return text


def main():
    src = read(SRC)
    # drop the leading comment block of the source, which names the placeholders
    lines = src.split("\n")
    while lines and lines[0].startswith("%"):
        lines.pop(0)
    src = "\n".join(lines).lstrip("\n")
    head = ("% Generated by build_appendix.py from appendix_src.tex and\n"
            "% ../greedy_intersection.tex.  Edit those files, not this one.\n\n")
    body = fill(src)
    # the proof of cor:classes gets its own rules, each of which must apply once
    start = body.index("\\begin{proof}[Proof of Corollary~\\ref{cor:classes}]")
    end = body.index("\\end{proof}", start) + len("\\end{proof}")
    part = body[start:end]
    for old, new in CLASSES_RULES:
        if len(re.findall(old, part)) != 1:
            fail("cor:classes rule %r applies %d times" % (old[:40], len(re.findall(old, part))))
        part = re.sub(old, new, part)
    body = body[:start] + part + body[end:]
    body = apply_rules(body, RULES)
    body = apply_layout(body)
    for bad in ("wang26", "companion", "prop:assign-pos", "eq:update-integral",
                "prop:nphard", "prop:notmatroid", "%%", "Figure", "signed tropical", "signed circuit", "\\begin{figure}"):
        if bad in body:
            fail("%r left in the appendix" % bad)
    # vocabulary that the paper does not use: coined terms and terms of the
    # companion paper; labels such as thm:compiler and lem:observer are exempt
    banned = re.compile(r"(?i)(?<!thm:)compil|(?<!lem:)observer|observable|amplitude|\blift"
                        r"|filtration|\bguard|signed tropical|signed circuit|companion"
                        r"|threshold integral|\bschedul|\bepoch")
    for name, text in (("the appendix", body), ("gi_ipco.tex", read(os.path.join(HERE, "gi_ipco.tex")))):
        left = banned.search(text)
        if left:
            fail("%r left in %s" % (left.group(0), name))
    with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(head + body)

    bib = read(BIB_IN)
    if "wang26" in bib:
        fail("the bibliography cites the companion paper")
    with io.open(BIB_OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(bib)
    print("appendix.tex and gi_ipco.bib written")


if __name__ == "__main__":
    main()
