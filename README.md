# A subexponential upper bound for log c in the abc conjecture

Ruiyi Zhang

DOI: [DOI pending]

For every $`\varepsilon>0`$, there is a constant $`C_\varepsilon>0`$ such that
all positive integers $`a,b,c`$ with $`a+b=c`$ and $`\gcd(a,b)=1`$ satisfy

```math
\log\, c \leq C_\varepsilon\,\mathrm{rad}(abc)^\varepsilon.
```

## Contents

- [Paper](main.pdf) and [LaTeX source](source/)
- [Lean formalization](lean/) and its [README](lean/README.md)

## Lean formalization

The Lean 4 formalization of Theorem 1.1 is in [lean/](lean/). The same tree
is at the root of the [palomar](https://github.com/ryzfsu/abc-log-bound-subexponential/tree/palomar)
branch. The main declaration, `AbcSubexp.subexp`, proves this statement:

```lean
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
        Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε
```

The vendored `AbcTwoNinths/` modules come from
[An upper bound for log c in the abc conjecture with exponent 2/9](https://doi.org/10.5281/zenodo.24405683).

## Build

See [BUILD.md](BUILD.md) for the LaTeX build and the
[Lean README](lean/README.md) for build and verification commands. The root
`SHA256SUMS` covers the paper package. The Lean package has its own checksums.

## License

The paper and its source are licensed under CC BY 4.0. The Lean formalization
is licensed under Apache 2.0. See [LICENSE.md](LICENSE.md) for details.

## Citation

Ruiyi Zhang, *A subexponential upper bound for log c in the abc conjecture*,
preprint, 2026.

```bibtex
@misc{zhang2026abcsubexponential,
  author = {Zhang, Ruiyi},
  title  = {A subexponential upper bound for $\log\, c$ in the {$abc$} conjecture},
  year   = {2026},
  note   = {Preprint}
}
```
