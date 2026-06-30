# Local Minimized Regressions

Put minimized `.smt2` reproducers from external benchmark or Z3 proof-regression
failures here when they are small enough to check in.  Larger private or
upstream checkouts should be supplied with `--regression-dir /path/to/dir`.

Every checked-in regression should keep any `; holsmt-expected:` directive
needed to make unsupported behavior an exact diagnostic rather than a silent
skip.
