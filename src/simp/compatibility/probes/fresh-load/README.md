# Fresh-load tests (TASK_03 and later)

Reserved location for maintained attribute/theorem-set namespace probes.
The preserved historical input is
`../../inputs/investigation/namespace-selftest.sml`.

Use a separately linked `selftest.sml` executable, Holmake-built against
`bin/hol.state0`, without a static dependency on simpLib/splitLib. Verify
registry preconditions before dynamically loading the lane's simpLib;
record the actual load path and check handler/data preservation afterward.
The ordinary differential control executable preloads simpLib and cannot
establish these preconditions. `run.py` therefore excludes this directory.
