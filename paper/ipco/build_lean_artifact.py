"""Build the Lean supplementary material of the IPCO submission.

Copies the development in ../../daishu-formal (left unchanged) to lean-artifact/, keeping
the modules that the paper needs, and

* renames the package to GreedyIntersection and the modules, declarations and namespaces
  whose names use vocabulary that the paper does not use;
* replaces the module headers listed in lean_artifact_headers.py and rewrites the comments:
  citations of labels become the numbering of the paper, and the vocabulary follows the
  paper;
* writes lakefile.toml, lake-manifest.json, lean-toolchain, Axioms.lean and README.md;
* fails if a banned term is left.

The directory lean-artifact/.lake (build output, and the package directory) is kept between
runs.  Run:  python build_lean_artifact.py
"""
import io
import json
import os
import re
import shutil
import sys

from lean_artifact_headers import HEADERS, BODY

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, "..", "..", "daishu-formal"))
DST = os.path.join(HERE, "lean-artifact")
OLD, NEW = "SignedTropical", "GreedyIntersection"
DROP = {"Examples", "NormalForm", "Polytope"}

# module files renamed (paths relative to the package directory, dotted)
MODULES = {
    "GapSum": "LevelSum",
    "Compiler": "SumCircuit",
    "LevelCompiler": "LevelSumCircuit",
    "Lift": "Simulation",
    "Rainbow.Observer": "Rainbow.Tests",
    "Rainbow.ObserverOracle": "Rainbow.ExchangeTests",
    "Rainbow.Schedule": "Rainbow.Updates",
    "Rainbow.GapUpdate": "Rainbow.LevelUpdate",
}

# declarations and namespaces renamed as whole identifiers (qualified uses included)
IDENT = {
    # Theorem 3 and Corollary 26
    "compileB": "levelSumB", "compileCost": "levelSumCost", "compileB_spec": "levelSumB_spec",
    "compiler": "sumCircuit", "compileCost_le": "levelSumCost_le", "compiler_size": "sumCircuit_size",
    "thm_compiler": "thm_levelSum", "compileB_impl": "levelSumB_impl",
    "intObsB": "intSumB", "intObsB_spec": "intSumB_spec", "intObsCircuit": "intSumCircuit",
    "integer_observable": "integer_levelSum",
    "integer_observable_lipschitz": "integer_levelSum_lipschitz",
    # the gate-by-gate simulation
    "liftInterp": "simInterp", "eval_liftInterp": "eval_simInterp", "liftGad": "simGad",
    "liftCost": "simCost", "length_liftGad": "length_simGad", "liftGad_spec": "simGad_spec",
    "liftB": "simB", "length_liftB": "length_simB", "liftCost_sum_le": "simCost_sum_le",
    "liftB_spec": "simB_spec", "liftCircuit": "simCircuit", "lift_vanish": "simAt_vanish",
    "ampl": "scaledVal", "ampl_op": "scaledVal_op", "ampl_true": "scaledVal_true", "ampl_false": "scaledVal_false",
    # Lemma 24
    "castAdd_mem_lift": "castAdd_mem_doubleSet", "addNat_mem_lift": "addNat_mem_doubleSet",
    "fst_lift": "fst_doubleSet", "card_lift": "card_doubleSet", "isRainbow_lift": "isRainbow_doubleSet",
    "blocksMet_lift": "blocksMet_doubleSet", "isBase_lift_iff": "isBase_doubleSet_iff",
    "sum_weight_lift": "sum_weight_doubleSet", "eq_lift_of_isRainbowBase": "eq_doubleSet_of_isRainbowBase",
    # Lemma 22
    "obsV": "testsV", "obsB": "testsB", "obsCost": "testsCost", "obsB_impl": "testsB_impl",
    "observer": "levelTests", "obsCost_le": "testsCost_le", "obsCost_le_bigO": "testsCost_le_bigO",
    "lem_observer": "lem_levelTests", "lem_observer_oracle": "lem_exchangeTests",
    "IsObserver": "IsTestCircuit", "isObserver_observer": "isTestCircuit_levelTests",
    "observer_size_le": "levelTests_size_le", "MonotoneObs": "MonotoneTest",
    # Lemma 21
    "nuGuardB": "nuIndB", "nuGuardB_impl": "nuIndB_impl", "avGuardB": "avIndB",
    "avGuardB_impl": "avIndB_impl", "avGuardV_eq": "avIndV_eq", "avGuardCircuit": "avIndCircuit",
    "avGuardCircuit_spec": "avIndCircuit_spec",
    # the proof of Theorem C
    "schedule": "updateSeq", "le_nu_schedule": "le_nu_updateSeq", "psi_schedule": "psi_updateSeq",
    # the old numbering of the corollaries
    "corollaryD_count": "count_codes", "corollaryD_explicit": "count_explicit",
    "corollaryD_tendsto": "count_tendsto", "corollaryD_tendsto_of_forall": "count_tendsto_of_forall",
    "corollaryD_most": "count_most", "corollaryD_unconditional": "count_unconditional",
    "corollaryD": "count_bound",
    "corollaryC_binary": "classes_binary", "corollaryC_binary_poly": "classes_binary_poly",
    "corollaryC_graphic": "classes_graphic", "corollaryC_cographic": "classes_cographic",
    "corollaryF_upper": "monotone_upper", "corollaryF_upper_mon": "monotone_upper_mon",
    "corollaryF_lower": "monotone_lower",
    # namespaces
    "Observer": "Tests", "Schedule": "Updates", "GapUpdate": "LevelUpdate",
}
SUBSTR = {"gapSum": "levelSum", "GapSum": "LevelSum", "threshSet": "sublevelSet",
          "STOp": "MPMOp", "stInterp": "mpmInterp"}
# the bare identifier `lift` names two different definitions
BARE_LIFT = {"Lift": "simAt", "Compiler": "simAt", "Rainbow.Doubling": "doubleSet"}

# comment prose, outside backticks; order matters
PROSE = [
    ("signed tropical circuits", "(max,+,-)-circuits"), ("signed tropical circuit", "(max,+,-)-circuit"),
    ("Signed tropical circuits", "(max,+,-)-circuits"), ("Signed tropical", "(max,+,-)"),
    ("signed tropical", "(max,+,-)"),
    ("signed circuits", "(max,+,-)-circuits"), ("signed circuit", "(max,+,-)-circuit"),
    ("signed comparison", "two's complement comparison"), ("signed gates", "(max,+,-) gates"),
    ("signed gate", "(max,+,-) gate"),
    ("threshold integrals", "level sums"), ("threshold integral", "level sum"),
    ("Threshold integral", "Level sum"), ("gap sums", "level sums"), ("gap sum", "level sum"),
    ("The compiler", "The circuit of Theorem 3"), ("the compiler", "the circuit of Theorem 3"),
    ("compiler", "circuit of Theorem 3"), ("compiled", "computed"), ("compiles", "computes"),
    ("compile", "compute"),
    ("Observers", "Test circuits"), ("observers", "test circuits"), ("Observer", "Test circuit"),
    ("observer", "test circuit"), ("observables", "Boolean functions"),
    ("observable", "Boolean function"), ("observations", "tests"), ("observation", "test"),
    ("amplitude", "scale"),
    ("schedules", "update sequences"), ("schedule", "update sequence"),
    ("Schedule", "Update sequence"),
    ("epochs", "phases"), ("Epochs", "Phases"), ("epoch", "phase"), ("Epoch", "Phase"),
    ("guards", "indicator factors"), ("guard", "indicator factor"),
    ("filtration", "family of sublevel sets"),
    ("Phase 1", "this development"), ("Phase 2", "this development"),
    ("Corollary C", "Corollary 6(1)"), ("Corollary D", "Corollary 28"),
]
PROSE_LIFT = [("lifted", "simulated"), ("lifts", "simulates"), ("Lifting", "Simulating"),
              ("lifting", "simulating"), ("lift", "simulation")]

# labels of the full paper that the IPCO version numbers differently or does not have
LABEL_TEXT = {
    "cor:integer-observable": "Corollary 26", "def:filtration": "Definition 2",
    "eq:sorted": "Definition 2", "eq:gap-sum": "Definition 2",
    "eq:lovasz": "the remark after Definition 2", "def:models": "Definition 1",
    "def:lattice": "the lattice circuits of `Lattice.lean`",
    "prop:sugeno": "`levelSum_eq_sugeno`", "eq:sugeno": "`levelSum_eq_sugeno`",
    "thm:lattice": "`thm_lattice`", "thm:equivalence": "Theorems A and B",
    "sec:amplitude": "the proof of Theorem 3",
    "prop:two-readings": "Definition 2 and the remark after it",
    "lem:lipschitz": "the Lipschitz bound of `Integral.lean`",
    "eq:update-integral": "Lemma 13", "lem:bit": "equation (2) in the proof of Theorem 3",
    "lem:levelcompiler": "Corollary 4", "lem:lift": "the simulation in the proof of Theorem 3",
    "prop:notmatroid": "Proposition 10(1)", "prop:nphard": "Proposition 10(2)",
}
KIND = {"thm": "Theorem", "lem": "Lemma", "cor": "Corollary", "prop": "Proposition",
        "def": "Definition", "eq": "equation", "sec": "Section", "app": "Appendix"}

BANNED = re.compile(
    r"signed_assignment|greedy_intersection|notes/|BLUEPRINT|docs/|research-direction|PHASE"
    r"|Phase [12]|(?i:compil)|(?i:observer)|(?i:observable)|(?i:observation)|amplitude|\blift"
    r"|(?i:schedul)|(?i:epoch)|(?i:guard)|filtration|(?i:signed tropical)|SignedTropical"
    r"|(?i:threshold integral)|gap sum|Corollary [CDEF]\b|corollary[CDF]|companion"
    r"|Wang|ukiyo|Dsektop")


def fail(msg):
    sys.exit("build_lean_artifact: " + msg)


def read(p):
    with io.open(p, encoding="utf-8") as f:
        return f.read().replace("\r\n", "\n")


def write(p, text):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with io.open(p, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def split_comments(text):
    """Split Lean source into ('code', s) and ('comment', s) pieces."""
    out, buf, i, n = [], [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(("code", "".join(buf)))
            buf = []
            out.append(("comment", text[i:j]))
            i = j
        elif text.startswith("/-", i):
            depth, j = 0, i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(("code", "".join(buf)))
            buf = []
            out.append(("comment", text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            buf.append(text[i:j + 1])
            i = j + 1
        else:
            buf.append(text[i])
            i += 1
    out.append(("code", "".join(buf)))
    return out


def label_phrase(kind_word, label):
    if label in LABEL_TEXT:
        return LABEL_TEXT[label]
    if label not in NUMS:
        fail("label %s has no number in gi_ipco.aux" % label)
    num, prefix = NUMS[label], label.split(":")[0]
    if prefix == "eq":
        return "%s (%s)" % ("Equation" if kind_word == "Equation" else "equation", num)
    return "%s %s" % (KIND[prefix], num)


# a kind word before the label is absorbed, so "equation `eq:x`" gives "equation (1)"
LABEL_RE = re.compile(r"(?:(Theorem|Lemma|Corollary|Proposition|Definition|Section|Thm\.|"
                      r"Equation|equation)\s+)?"
                      r"`((?:thm|lem|cor|prop|def|eq|sec|app):[A-Za-z0-9-]+)`")


def rewrite_comment(c, module):
    parts = c.split("`")
    rules = PROSE + ([] if module == "Rainbow.Doubling" else PROSE_LIFT)
    for k in range(0, len(parts), 2):
        for old, new in rules:
            parts[k] = parts[k].replace(old, new)
    c = "`".join(parts)
    c = LABEL_RE.sub(lambda m: label_phrase(m.group(1), m.group(2)), c)
    c = re.sub(r"`greedy_intersection\.tex`,?\s*", "", c)
    return c


def ident_sub(text, old, new):
    return re.sub(r"(?<![\w'!?])" + re.escape(old) + r"(?![\w'!?])", new, text)


def transform(module, text):
    if module in HEADERS:
        i = text.find("/-!")
        j = text.find("-/", i) + 2
        if i < 0:
            fail("no header in " + module)
        text = text[:i] + HEADERS[module] + text[j:]
    for old, new in BODY.get(module, []):
        if text.count(old) != 1:
            fail("body rule for %s applies %d times: %r" % (module, text.count(old), old[:50]))
        text = text.replace(old, new)
    text = "".join(rewrite_comment(s, module) if kind == "comment" else s
                   for kind, s in split_comments(text))
    # imports of renamed modules
    for old, new in MODULES.items():
        text = re.sub(r"^(import %s\.)%s$" % (OLD, re.escape(old)), r"\g<1>" + new, text, flags=re.M)
        text = text.replace("`%s.lean`" % old.replace(".", "/"), "`%s.lean`" % new.replace(".", "/"))
        short_old, short_new = old.split(".")[-1], new.split(".")[-1]
        text = text.replace("`%s.lean`" % short_old, "`%s.lean`" % short_new)
    for old, new in sorted(IDENT.items(), key=lambda kv: -len(kv[0])):
        text = ident_sub(text, old, new)
    for old, new in SUBSTR.items():
        text = text.replace(old, new)
    if module in BARE_LIFT:
        text = ident_sub(text, "lift", BARE_LIFT[module])
    return text.replace(OLD, NEW)


def main():
    global NUMS
    aux = read(os.path.join(HERE, "gi_ipco.aux"))
    NUMS = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}", aux))

    os.makedirs(DST, exist_ok=True)
    for name in os.listdir(DST):
        if name != ".lake":
            p = os.path.join(DST, name)
            shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)

    root_dir = os.path.join(SRC, OLD)
    modules = []
    for dp, dn, fn in os.walk(root_dir):
        for f in sorted(fn):
            if not f.endswith(".lean"):
                continue
            mod = os.path.relpath(os.path.join(dp, f), root_dir)[:-5].replace(os.sep, ".")
            if mod in DROP:
                continue
            modules.append(mod)
            new_mod = MODULES.get(mod, mod)
            out = transform(mod, read(os.path.join(dp, f)))
            write(os.path.join(DST, NEW, *new_mod.split(".")) + ".lean", out)

    # root module: the imports of the development, minus the dropped modules
    root = read(os.path.join(SRC, OLD + ".lean"))
    lines = [l for l in root.split("\n")
             if not any(l.strip() == "import %s.%s" % (OLD, d) for d in DROP)]
    write(os.path.join(DST, NEW + ".lean"), transform("", "\n".join(lines)))

    lakefile = read(os.path.join(SRC, "lakefile.toml")).replace(OLD, NEW)
    write(os.path.join(DST, "lakefile.toml"), lakefile)
    manifest = json.loads(read(os.path.join(SRC, "lake-manifest.json")))
    manifest["name"] = NEW
    write(os.path.join(DST, "lake-manifest.json"), json.dumps(manifest, indent=1) + "\n")
    shutil.copy(os.path.join(SRC, "lean-toolchain"), os.path.join(DST, "lean-toolchain"))
    for extra in ("Axioms.lean", "README.md"):
        write(os.path.join(DST, extra), read(os.path.join(HERE, "lean_artifact_" + extra)))

    bad = []
    for dp, dn, fn in os.walk(DST):
        if ".lake" in dp.split(os.sep):
            continue
        for f in fn:
            p = os.path.join(dp, f)
            for k, line in enumerate(read(p).split("\n"), 1):
                for m in BANNED.finditer(line):
                    bad.append("%s:%d: %s   [%s]" % (os.path.relpath(p, DST), k, line.strip()[:110], m.group(0)))
    if bad:
        print("\n".join(bad[:80]))
        fail("%d banned terms left" % len(bad))
    print("lean-artifact written: %d modules" % len(modules))


if __name__ == "__main__":
    main()
