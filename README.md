# A subexponential upper bound for log c in the abc conjecture

Ruiyi Zhang

DOI: [10.5281/zenodo.24407806](https://doi.org/10.5281/zenodo.24407806)

Lean (Palomar): [PALOMAR-2026-11-20-000026](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-20-000026)

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
branch. The Palomar registry entry [PALOMAR-2026-11-20-000026](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-20-000026)
registers the palomar branch commit 7629a771c6f35598f1c56d32a5f13fb521e2ede0, whose Lean files are
identical to lean/ here. The main declaration, `AbcTwoNinths.twoNinths`, proves this statement:

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

Ruiyi Zhang, *A subexponential upper bound for log c in the abc conjecture*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.24407806

```bibtex
@misc{zhang2026abcsubexponential,
  author    = {Zhang, Ruiyi},
  title     = {A subexponential upper bound for $\log\, c$ in the {$abc$} conjecture},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.24407806},
  url       = {https://doi.org/10.5281/zenodo.24407806}
}
```
