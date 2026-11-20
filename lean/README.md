# A subexponential upper bound for log c in the abc conjecture

Ruiyi Zhang

This package formalizes Theorem 1.1 of the companion paper (see [Citation](#citation)).
For every real $`\varepsilon>0`$, there is a real $`C_\varepsilon>0`$ such that
for all positive coprime integers $`a,b`$ with $`a+b=c`$,

```math
\log\, c \leq C_\varepsilon\,\mathrm{rad}(abc)^\varepsilon.
```

The radical is the product of the distinct prime factors. The abc conjecture
itself remains open.

[Subexp.lean](Subexp.lean) proves `AbcSubexp.subexp`.
[Solution.lean](Solution.lean) makes it available to the comparison harness
and restates it as `AbcSubexp.Solution.subexp`.
[Challenge.lean](Challenge.lean) presents the same statement for independent
comparison using only Mathlib.

```lean
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
        Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε
```

## Paper and module map

| Paper part | Proof folder under `Subexp/` |
| --- | --- |
| Section 1, Theorem 1.1 | `S1_Statement` |
| Section 2, inputs and parameter choices | `S2_Parameters` |
| Section 3, contact prime | `S3_ContactPrime` |
| Section 4, auxiliary primes and tuple counting | `S4_TupleCounting` |
| Section 5, box and vanishing polynomial | `S5_Box`, `S5_Determinant` |
| Section 6, hitting prime | `S6_HittingPrime` |
| Section 7, interpolation | `S7_Interpolation` |
| Final proof of Theorem 1.1 | `Conclusion` |

## Differences from the paper

- **Contact prime (Section 3).** The paper uses the local estimates of the two-ninths paper (Fact F2). Their source in the one-third paper is Fact F3, Lemma 2.1 and (2.8), which use Győry's corrected Proposition 5. Lean proves the real estimate at each positive rate. At the finite places it extracts a smooth modulus from excess mass at small primes and rules that modulus out. The remaining mass supplies the contact prime. See [Contact.lean](Subexp/S3_ContactPrime/Contact.lean).
- **Old-lattice separation (Lemma 4.1).** The paper applies Bugeaud–Laurent, Corollary 2, to two independent principal units. Lean uses the odd-prime two-logarithm estimate `AbcTwoNinths.Basic.twoLogUnbounded147` through the signed bound `AbcTwoNinths.Diamond.liftedBound` for the weighted shear. The proof handles a zero coefficient separately. See [WeightedShear.lean](Subexp/S4_TupleCounting/WeightedShear.lean).
- **Auxiliary-prime cutoff (4.1).** With `ℓ = log p`, the paper's second branch for `t/ℓ` uses the term `log(2/e)/ℓ`. Lean uses the stronger upper bound with `log(2/e)/x`. Once `20 ≤ e²x`, the loss `3e − e²/10 − log(2/e)/x` is positive, so multiplying it by `ℓ ≤ x` preserves the inequality. Both bounds give `t/ℓ < 1 − 2.8e`. See [AuxiliaryPrimeCutoff.lean](Subexp/S4_TupleCounting/AuxiliaryPrimeCutoff.lean).
- **Tuple count (Proposition 4.2).** With `Y = exp(κx)`, the paper counts at most one prime per signed residue class. This gives a factor `Y^(d+1)` and a bad-tuple proportion at most `exp(−2κx + o(x))`. The fixed-dimension Lean estimate allows `Y^(d+2)` and gives `exp(−κx + o(x))`. Lean's joint choice uses a separate growing-dimension count with short-vector cutoff `exp(√x)`. See [BadTupleOnset.lean](Subexp/S4_TupleCounting/BadTupleOnset.lean).
- **Determinant rows (Section 5).** Both row families in Lean use complete lower simplices. The second family has degree below `ceil(c₀n)`. The proof uses its pointwise residual bound and row-count ratio in the archimedean estimate. The polynomial has total degree at most `D = ceil((1+e/10)n)-1`. The interpolation step uses the smaller simplex up to `D+q` for the chosen prime `q`.
- **Fresh-prime costs.** The factor-three auxiliary prime interval allows an absolute logarithmic difference of at most `log 3` in the real-place estimate. The translating vector uses the separate lower bound `log(M/3) ≥ (log M)/2` above the onset.
- **Hitting prime (Lemma 6.1).** The paper fixes a tuple and applies Steuding–Technau, Theorem 3, (15), to find a prime in `(10X/11, X]`. Lean chooses the tuple and prime together. Products of finite cosine majorants and geometric sums bound the number of integers missing every tuple. A Chebyshev lower bound supplies more primes than exceptions in `(X/3, X]`, with `X = ceil(3D/(k+1))`. For `s = floor(x^(1/3))` lists, the temporary lattice has rank `ms+1` and minimum threshold `exp(√x)`. The chosen prime serves every low digit and phase. See [SeparatedMisses.lean](Subexp/S6_HittingPrime/SeparatedMisses.lean) and [HittingPrimeSelection.lean](Subexp/S6_HittingPrime/HittingPrimeSelection.lean).
- **Lucas interpolation (Proposition 7.3).** The paper writes a column index as `qv+s`, with high digit `v`. Lean splits the column coordinatewise by quotient and remainder modulo `q`, then recovers the high-digit coefficients by induction on total degree. See [LucasDigits.lean](Subexp/S7_Interpolation/LucasDigits.lean) and [HighDigitInterpolation.lean](Subexp/S7_Interpolation/HighDigitInterpolation.lean).
- **Constant and onset.** Both Theorem 1.1 and its Lean statement give an existential constant for each fixed exponent. The Lean proof specializes the two-ninths height bound at inner exponent `1/18` on the bounded-radical range. Its second simplex and wider interval enter the choice of the exponent-dependent onset.

## Build and verification

Install [Elan](https://github.com/leanprover/elan) and Git. Clone the `palomar`
branch, which contains the Lean package at the repository root.

```bash
git clone --branch palomar https://github.com/ryzfsu/abc-log-bound-subexponential
cd abc-log-bound-subexponential
lake exe cache get
lake build
lake env lean SolutionAxioms.lean
```

Elan reads `lean-toolchain` for Lean `v4.35.0-rc4`. Lake uses
`lake-manifest.json` for the revisions of Mathlib and its dependencies.
The vendored modules in `AbcTwoNinths/` come from Ruiyi Zhang's Lean
formalization of the two-ninths paper under Apache 2.0
([concept DOI 10.5281/zenodo.24405683](https://doi.org/10.5281/zenodo.24405683),
[source commit `e10c67b3`](https://github.com/ryzfsu/abc-log-bound-two-ninths/tree/e10c67b33dda8d5c97d6f275d9644a3be7438ee2)).
The default build checks the full proof library. The axiom command prints

```text
'AbcSubexp.subexp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For strict source verification, start with a fresh checkout and run the
following commands from this package's root. The package archive can also
be used in place of this checkout.

```bash
lake exe cache get
bash verification/verify.sh
```

The verifier compiles the proof with warnings treated as errors, checks
the theorem's type and axioms, builds the independent challenge, and
compares the inline theorem types and their fixed definitions. The challenge has one deliberate
`sorry` for the comparison harness. See [verification/README.md](verification/README.md).

## Citation

Ruiyi Zhang. [*A subexponential upper bound for log c in the abc conjecture*](https://github.com/ryzfsu/abc-log-bound-subexponential).
Preprint, Zenodo, 2026. Theorem 1.1. DOI: [10.5281/zenodo.24407806](https://doi.org/10.5281/zenodo.24407806). [ORCID](https://orcid.org/0009-0003-3110-8524).

## Use of AI tools

The author devised the method of proof. Codex (OpenAI, GPT-6 Astra) and Antigravity (Google, Gemini 4 Neon) ran blind reviews of the manuscript, and Codex assisted with the Lean formalization. Claude Code (Anthropic, Claude Fable 5) checked the proofs and the references. The author checked every step of the proof and every reference, and takes full responsibility for the content of the paper.

## Licence

The Lean source is licensed under the Apache License, Version 2.0.
See [LICENSE](LICENSE).
