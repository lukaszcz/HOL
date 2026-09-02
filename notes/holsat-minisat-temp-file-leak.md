# HolSat MiniSat temporary-file leak on abort

`HolSatLib.SAT_PROVE` delegates checked propositional proofs to
`src/HolSat/minisatProve.sml`.  Its temporary CNF and resolution-proof files
are removed on the normal return path, but their cleanup is not protected by
an exception-safe bracket.  An interrupt, timeout, or replay exception after
file creation can therefore leave those files behind.

TASK_19 deliberately does not change `src/HolSat`: the skeleton-and-atoms
engine consumes the existing checked MiniSat plus resolution path as a
library client.  The leak can be reproduced by interrupting a sufficiently
large `HolSatLib.SAT_PROVE` call and inspecting the temporary directory for
the generated input/proof pair.  It affects cleanup only; reconstructed HOL
theorems still pass through the kernel checker.

A separate HolSat change should wrap creation and use of both paths in one
exception-safe cleanup region, remove each path after success or any raised
exception, and add an interrupt/forced-failure regression.  That change
belongs with the owner of `minisatProve.sml`, independently of HolSmt replay.
