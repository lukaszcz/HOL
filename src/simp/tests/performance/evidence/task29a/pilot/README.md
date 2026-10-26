# TASK29A pilot runs (design evidence, not acceptance)

Two `task29a_grid.py run --only frag_record-0 --only compile_collector-10000`
subsets, used to choose the grid's pairs and samples before the full rerun.
Same candidate source as the grid (production `src/simp` unchanged), same
predeclared counts (`../iterations.json`), equivalence policy version 2.
`--only` runs write no `decisions.json` and never count as a grid decision.

| Run | Cell | CPU | wall | B/B CPU | Outcome |
| --- | --- | --- | --- | --- | --- |
| 10 pairs, 3 samples | frag_record/0 | [0.9687, 1.0346] | [0.9674, 1.0345] | [0.9883, 1.0143] | inconclusive |
| 10 pairs, 3 samples | compile_collector/10000 | [0.9618, 1.0259] | [0.9619, 1.0259] | [0.9577, 1.0888] | inconclusive (control invalid) |
| 20 pairs, 5 samples | frag_record/0 | [0.9842, 1.0009] | [0.9843, 1.0032] | [0.9897, 1.0140] | pass |
| 20 pairs, 5 samples | compile_collector/10000 | [1.0050, 1.0221] | [1.0000, 1.0211] | [0.9901, 1.0089] | pass |

GC (reported): fragment 0.85 [0.78, 0.98] and collector 1.16 [1.03, 1.19]
at 20 pairs. The collector's CPU is measurably 1.4% higher, inside the
margin. At 10 pairs the per-pair spread (fragment ±5%, collector ±13% from
GC-phase bimodality on a host at load 17–25) leaves the intervals wider than
the margin; 20 pairs and 5 samples resolve it. Durations: 658 s and 1558 s.

The 10-pair inventory's driver seal predates the `--pairs/--samples`
options; both inventories, archives and logs are kept unchanged.
