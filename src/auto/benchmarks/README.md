# Automation parity benchmarks

This directory holds the data-driven Phase-8 parity suites.  Every corpus
goal gates only the HOL4 tactic mapped from its recorded Isabelle method;
the wider tactic battery is informational.  Expected shortfalls are exact,
dated data, so either a regression or an unrecorded improvement fails the
selftest until the register is reconciled.

The checked-in modules exhaustively account for the pinned mined sources.
There are 1,061 source outcomes after nine documented HOL4 `aconv`
collapses, plus eleven HOL4 integer-regression goals.  Unsupported
translations are explicit shortfalls rather than omitted commands.
