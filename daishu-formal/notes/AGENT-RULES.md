# Rules for agents formalizing in this package

You are one of several agents formalizing, in parallel, results of a research project in Lean 4.
The coordinator (the main session) is also writing Lean in this package at the same time. Work
autonomously until your assignment is complete, then return the report described at the end.

## Project and frozen toolchain
- Lean package: D:/Dsektop/daishu/daishu-formal (library SignedTropical). Lean v4.32.0 and Mathlib v4.32.0
  (commit 81a5d257) are FROZEN by the user's explicit instruction: never run lake update, lake clean
  or any elan command, never edit lean-toolchain, lakefile.toml or lake-manifest.json, never download
  or build Mathlib sources, never install anything. If something seems to need a newer Mathlib, work
  around it.
- Build only your own modules, one build at a time, from D:/Dsektop/daishu/daishu-formal:
  "lake build SignedTropical.<Path>.<Module>" (or "lake env lean <file>" for a quick check of one
  file). Never run a bare "lake build". The machine (32 threads, 32 GB RAM) is shared with other
  agents building concurrently: never start several Lean processes at once and never leave one
  running in the background.
- Shell: Windows; PowerShell and Git Bash are both available.
- The package is tracked in the git repository D:/Dsektop/daishu. Never run git commands; the
  coordinator commits.
- API outages (HTTP 403, SSL errors) have killed agents mid-run. Save your work to disk often and keep
  your notes file current, so that a relaunched agent can continue from your files.

## Ownership
- Create only the files assigned to you (you may add more files under your assigned paths). Do not
  edit, touch, move or delete any other file: not the Phase 1 modules (SignedTropical/*.lean), not the
  root SignedTropical.lean (the coordinator adds imports at the end), not
  SignedTropical/Rainbow/Defs.lean (the shared Phase 2 interface; if a definition there is wrong or
  unusable, say so in your report and work around it in your own files), not other agents' or the
  coordinator's modules, not PHASE1.md or BLUEPRINT.md, and nothing in D:/Dsektop/daishu outside
  this package (the papers are read-only for you).
- Finished modules of other agents are frozen: import them, never edit them. If you need a lemma
  that belongs to a module that is not finished, prove it yourself in your own namespace.
- Put every declaration in your assigned namespace, so that modules written in parallel can be
  imported together without name clashes; use open to reach other namespaces.

## Sources
- Paper, the source of the statements: D:/Dsektop/daishu/paper/greedy_intersection.tex. Companion
  paper: D:/Dsektop/daishu/paper/signed_assignment.tex. Phase 2 research note with fuller proofs and
  referee corrections: D:/Dsektop/daishu/docs/phase2a-rainbow-2026-10-11.md.
- Phase 1 Lean (all proved, zero warnings): SignedTropical/{Circuit,Inline,Models,Sorting,GapSum,
  Lift,Compiler,Lattice,Matroid,TheoremA,Converse,Subtractionfree,Binary,Counting,Polytope,
  Examples}.lean, with natural-language companion PHASE1.md and design notes BLUEPRINT.md. Reuse
  their API (Circuit, Gate, Arg, the gate sets STOp and BoolOp, stInterp, boolInterp, indicator,
  bitsVal, the builders Bld, emit, Den, DenL, inline and inline_spec, gapSum, thm_compiler,
  integer_observable, rk, rank, maxBasisWeight, basisWeights, theoremA, theoremB, binary matroids)
  instead of redefining things.
- Shared Phase 2 interface: SignedTropical/Rainbow/Defs.lean (definitions only: IsRainbow, blockSet,
  blocksMet, IsRainbowIndep, nu, Av, IsRainbowBase, IsMinBase, minBaseWeight, Opt, shift, Psi,
  levelPiece, minBases, theta, Pos, connRel, IsAdmissible).
- Finished Phase 2 modules (frozen; their companions are in notes/): Rainbow/Connectivity.lean
  (P0b: components, lem:minbases(1),(4), notes/P0b-connectivity.md), Rainbow/MinBases.lean
  (P0a: lem:minbases(2),(3), eq:rank-mu, API for beta, nu, Av, Opt, notes/P0a-minbases.md),
  Rainbow/Exchange.lean (P2: lem:avoidable, exchange graphs, shortest augmenting paths, the
  augmenting path algorithm as a mathematical procedure, notes/P2-exchange.md). Also finished:
  NormalForm.lean, Integral.lean, SparsePaving.lean, Asymptotic.lean.
- Mathlib's matroid library: .lake/packages/mathlib/Mathlib/Combinatorics/Matroid (this version has
  no matroid intersection, no connectivity, and no uniform, partition, transversal or graphic
  matroids).

## Standards (the user's words: short but flawless; every formal statement must agree exactly with
## its natural-language statement)
- No sorry, admit, axiom, native_decide, implemented_by, extern, unsafe or opaque workarounds. Zero
  errors and zero warnings (linter and deprecation warnings included) in your modules. Check
  "#print axioms" of every main theorem in a scratch file outside SignedTropical/ (for example
  notes/scratch-<ID>.lean compiled with lake env lean; delete it when done): only propext,
  Classical.choice and Quot.sound may appear.
- Each main Lean statement must express the paper's statement exactly: same hypotheses, same
  conclusion. Where the paper writes O(...), prove an explicit numeric bound that implies it and
  state that bound. External results may enter only where your assignment explicitly allows it, as
  explicit hypotheses, never as axioms. If a paper statement is false, ambiguous, or must change to
  be formalizable, formalize the closest faithful version and report the discrepancy with proposed
  replacement wording for the paper. Never weaken a statement silently.
- Lean style: Mathlib conventions, concise proofs, no duplicated developments, a module docstring
  summarizing the results, a docstring on each main result naming its paper label.
- Natural-language companion: write notes/<ID>.md with (1) for each formalized result: the paper
  label, the Lean names, the precise natural-language statement that the Lean statement expresses,
  and a proof organized as "Step 1, ...", "Step 2, ..." that follows the Lean proof; (2) a
  correspondence table (paper label | Lean names | module | status); (3) differences from the paper,
  each with proposed paper wording when the paper should change; (4) module line counts; (5) what is
  not done, and why. Manuscript style for this file: no em-dashes and no "---", no "claim" wording,
  no filler such as "Note that", "Importantly", "It is worth noting".
- Before returning, rebuild each of your modules once more and confirm zero warnings.

## Report (your final message; keep it under 1500 words)
1. ID and status (complete, partial, failed).
2. Modules (paths) and line counts.
3. Results: paper label, Lean name, proved or not.
4. Checks: build clean (zero warnings), sorry-free, axioms.
5. Proposed paper changes (exact replacement wording).
6. API for later agents: exact names and signatures, one line each on what they say.
7. Not done, and concerns.
