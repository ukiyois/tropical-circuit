#!/bin/sh
# Phase 2e: rerun every check of docs/phase2e-epoch-rho2-2026-10-12.md on the final data set
# (logs of B0, B0d, this note's searches, and random instances); outputs in ep2_logs/check_*.txt.
cd "$(dirname "$0")"
L='stage_logs/*.txt'; E='ep_logs/*.txt'; F='ep2_logs/search*.txt'
python ep2_psi.py "$L" "$E" "$F" random:600:11 > ep2_logs/check_psi.txt 2>&1
python ep2_lemmas12.py "$L" "$E" > ep2_logs/check_lemmas12.txt 2>&1
python ep2_repeat_anchor.py "$L" "$E" "$F" > ep2_logs/check_repeat_anchor.txt 2>&1
python ep2_phi_by_span.py "$L" "$E" "$F" random:600:11 > ep2_logs/check_phi_by_span.txt 2>&1
python ep2_phi.py "$L" > ep2_logs/check_phi_B0.txt 2>&1
python ep2_phi.py "$E" > ep2_logs/check_phi_B0d.txt 2>&1
python ep2_phi.py random:400:7 > ep2_logs/check_phi_random.txt 2>&1
python ep2_linkpos.py "$L" > ep2_logs/check_linkpos_B0.txt 2>&1
python ep2_linkpos.py "$E" > ep2_logs/check_linkpos_B0d.txt 2>&1
python ep2_referee.py > ep2_logs/check_referee.txt 2>&1
python ep2_refQ.py > ep2_logs/check_refQ.txt 2>&1
python ep2_coverage.py "$L" "$E" "$F" random:600:11 > ep2_logs/check_coverage.txt 2>&1
python ep_conjQ.py "ep2_logs/searchQ_Q_graphic_6_12.txt" > ep2_logs/check_conjQ_B0d_script.txt 2>&1
echo done
