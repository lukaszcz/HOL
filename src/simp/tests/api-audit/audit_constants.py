"""Constants of the API audit that its consumers import (never copy).

`run.py` validates every process against them and records this file's seal
in its receipt; `performance/loading.py` binds a receipt to the same
objects.
"""

# Files whose bytes the receipt seals.
SOURCES = ("Holmakefile", "selftest.sml", "ordinary.ML", "runtime.ML",
           "Documentation.sml", "audit_constants.py", "run.py")

# Checks per process, by (foreign kind, owner timing).
CASE_CHECKS = {("attribute", "before"): 174,
               ("attribute", "after"): 170,
               ("exporter", "before"): 178,
               ("exporter", "after"): 173}

# Modules whose .sig and .sml the process must load from the native tree.
NATIVE_MODULES = ("simpLib", "congLib", "Traverse", "Cond_rewr", "Trace",
                  "simpExtLib", "TraverseExt",
                  "Cond_rewrExt", "congExtLib")
