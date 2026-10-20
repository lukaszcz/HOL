# Simplifier compatibility investigation

Branch: 62a6bdc3453c29e8f31faa72f2b70a245f44840d
Reference: origin/develop, cccaa27d7099cbadc886983020cbe745db7793f3

Verdict: not behavior-preserving on all legacy paths. Three confirmed
compatibility breaks require no use of new simplifier APIs.

1. src/simp/src/simpLib.sml:2068-2107: traversedata_for_ss returns a
   CONFIG_REDUCER even for empty_ss, whereas develop returns REDUCER.
   An existing `val Traverse.REDUCER _ = hd (#rewriters
   (simpLib.traversedata_for_ss simpLib.empty_ss))` now raises Bind.
   The additive legacy_traversedata_for_ss API requires client migration.

2. src/simp/src/simpLib.sml:1079-1116: Excl reinterprets prefixes rule:,
   solver:, looper:, split:, case:. Previously valid literal conversion
   names can no longer be excluded through Excl. Previously unmatched
   strings with these prefixes were silent no-ops; now they raise HOL_ERR.
   Example: `simpLib.empty_ss && [simpLib.Excl "rule:compat_missing"]`.
   All five prefixes were tested both with missing names and with a
   matching literal conversion name; all ten cases pass on develop and
   fail on this branch. Direct -* retains literal interpretation.

3. src/simp/src/splitLib.sml:122-137: loading simpLib unconditionally loads
   splitLib and reserves/registers the split attribute/theorem-set name.
   Registering a custom ThmAttribute attribute named split and then loading
   simpLib succeeds on develop but fails on this branch with
   `settype or attribute split already exists`.

Validation:
- Branch src/simp/src/selftest.sml: exit 0; 425 OK markers.
- Branch src/marker/selftest.sml: exit 0; 61 OK markers.
- Unmodified develop simplifier selftest: exit 0 on both versions;
  73 OK markers each.
- compat-selftest.sml: 12 checks. Develop 12 pass; branch 1 passes and
  11 fail (one constructor case and ten exclusion cases).
- namespace-selftest.sml: develop passes; branch fails.
- git diff --check origin/develop...HEAD: clean.

Method/scope:
Paired executables were built by Holmake from selftest.sml, not by piping
code into bin/hol. The baseline used isolated develop simplifier sources
and develop markerLib/markerSyntax sources. Both versions used this
checkout's kernel, other libraries and hol.state0; generated markerTheory
was shared. This was not a separate full develop repository build.
Current branch selftests ran in their normal directories.

Static review covered simpLib construction/history/dispatch, Traverse,
Opening, Travrules, congLib, Cond_rewr, marker integration and split loading.
No further concrete strategy-free traversal/conditional-rewrite regression
was identified. The original legacy traversal and conditional rewrite
runner are retained, with tests for context lifetime, callback staging,
live default depth, ordering, exceptions and shared bounded controls.
Passing these tests is not a proof of universal equivalence. No full-tree
build or exhaustive downstream-client test was run.

Inputs and compact results are retained here. Temporary copied source/build
folders were removed. No tracked repository files were changed.
