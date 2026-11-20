# Verification

Follow the main README to obtain the source and fetch the locked Mathlib
dependencies and cache. Start with a fresh Git checkout or extracted source
archive that has no `.lake/build` directory.

Run `bash verification/verify.sh`. The script checks the package's checksum
manifests and builds all vendored two-ninths and subexponential proof modules
from source with warnings treated as errors. It requires the compiled objects
and checks the exact axiom report for `AbcSubexp.subexp`. It builds `Challenge`
in a separate invocation and compares the types and bodies of the fixed
radical, triple predicate, and statement definitions. It requires a universal
quantifier at the root of each theorem type and checks that the challenge
theorem, library theorem, and solution restatement each have the retained
statement definition's body as their type. Finally it checks that
the source digests agree with those taken before the build.

The verification directory receives the source digests, build log, challenge
logs, axiom report, and statement comparison in JSON. The Comparator entry
points and permitted axioms are in [comparator.json](../comparator.json).
