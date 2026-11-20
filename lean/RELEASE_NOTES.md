# Lean formalization of Theorem 1.1

`AbcSubexp.subexp` formalizes Theorem 1.1 of Ruiyi Zhang's
*A subexponential upper bound for log c in the abc conjecture*.
`Challenge.lean` presents the statement in Mathlib. `Subexp.lean`
proves it with the proof library under `Subexp/`, and `Solution.lean`
restates it for the comparison harness.

Run `sha256sum -c SHA256SUMS SOURCE-SHA256SUMS` to check the package files.
The [build instructions](README.md#build-and-verification) identify the
vendored two-ninths modules and give the Lean commands to check the theorem
and its axioms.
