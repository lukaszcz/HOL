set -u
cd /home/lukasz/work/HOL/worktrees/simplifier
G=src/simp/tests/performance/task29a_grid.py
I=src/simp/tests/performance/evidence/task29a/iterations.json
W=src/simp/tests/compatibility/evidence/task26/root-wrapper.sh
O=/tmp/claude-1003/-home-lukasz-work-HOL-worktrees-simplifier/5c7ba8a1-57f2-40d8-8321-1f50cc2ea65d/scratchpad/grid2
R=""; [ -f $O/stage1/inventory.json ] && R="--resume"
if [ ! -f $O/stage1/decisions.json ]; then
  echo "=== stage1 $R $(date -u +%FT%TZ)"; df -h / | tail -1
  sh $W env TMPDIR=/dev/shm python3 -B $G run --candidate 6f62229c04d548973eb74955a283e2abe3ce9133 --iterations $I --pairs 20 --samples 5 --layout-seed task29a-grid-1 --authorize-measurements --output $O/stage1 $R
  echo "=== stage1 exit=$? $(date -u +%FT%TZ)"; df -h / | tail -1
  [ -f $O/stage1/decisions.json ] || { echo "=== stage1 incomplete"; exit 3; }
fi
R=""; [ -f $O/stage2/inventory.json ] && R="--resume"
echo "=== stage2 $R $(date -u +%FT%TZ)"
sh $W env TMPDIR=/dev/shm python3 -B $G extend --grid $O/stage1 --output $O/stage2 --authorize-measurements $R
echo "=== stage2 exit=$? $(date -u +%FT%TZ)"; df -h / | tail -1
[ -f $O/stage2/decisions.json ] || { echo "=== stage2 incomplete"; exit 3; }
echo "=== done"
