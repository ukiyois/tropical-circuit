# Referee check of `docs/phase2a-rainbow-2026-10-11.md`, section 4

Independent implementation (`core.py`, exact rationals) written by a separate
referee pass on 2026-10-11; the authors' code is imported only by
`verify_long_stage*.py`, for cross-checks.

| script | checks | log |
|---|---|---|
| `exhaustive.py` | (F1) to (F4), Theorems 6 and 8, compiled update; 15 small matroids, all block assignments, all `v` in `{0..3}^m` | `exh_L3_m6.txt`, `exh_F7_L2.txt` |
| `test_main.py` | Proposition 7, Theorems 6 and 8, compilation, random states | |
| `test_lemmaR.py` | Lemma R and R' on random matroids | |
| `test_families.py` | Theorem 6 on other (F1) to (F4) families | |
| `test_schedule.py` | full static schedules | |
| `test_bipartite.py` | the bipartite clause of Proposition 7 | |
| `test_readings.py`, `examples.py` | which readings of the definitions are needed | `examples_out.txt` |
| `stage_length.py`, `hill_long.py`, `hill_k3.py`, `search_long.py` | stage lengths beyond `r+1` | `stage_len_L3.txt`, `hill_out.txt`, `hill_k3_out.txt` |
| `verify_long_stage.py`, `verify_long_stage2.py` | long stages against the authors' code | |

Run from this directory; `core.py` is imported by the others.
