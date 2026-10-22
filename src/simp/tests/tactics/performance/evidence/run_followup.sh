#!/bin/sh
# Explicitly invoked only inside the parent-authorized exclusive window.
set -eu
P=src/simp/tests/tactics/performance
ROWS=full_complete.0,rev_complete.0,no_strip_full_complete.0,simp_complete.8,rev_reuse.8,no_strip_full_reuse.8,no_strip_full_complete.8,no_strip_rev_reuse.8
for MODE in current control; do
  CONTROL=
  if [ "$MODE" = control ]; then CONTROL=--baseline-control; fi
  python3 -B "$P/run_tactics.py" --authorize-measurements $CONTROL \
    --rows "$ROWS" --pairs 10 --samples 3 --timeout 1800 \
    --fixed-iterations "$P/followup-iterations.json" \
    --output "$P/evidence/followup-$MODE"
done
python3 -B "$P/summarize.py" \
  --candidate "$P/evidence/followup-current" \
  --control "$P/evidence/followup-control" \
  --output "$P/evidence/followup-analysis.json"
for MODE in current control; do
  CONTROL=
  if [ "$MODE" = control ]; then CONTROL=--baseline-control; fi
  python3 -B "$P/run_tactics.py" --authorize-measurements $CONTROL \
    --gc-trace --rows "$ROWS" --pairs 2 --samples 3 --timeout 1800 \
    --fixed-iterations "$P/followup-iterations.json" \
    --output "$P/evidence/followup-trace-$MODE"
done
