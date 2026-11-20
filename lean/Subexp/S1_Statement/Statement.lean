/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Statement

/-!
# The subexponential statement

The statement bounds the logarithm of the sum for positive coprime triples
by every positive power of the natural radical, with a constant depending
on the exponent. The triple and radical use the two-ninths definitions.

## Main definitions

* `AbcSubexp.subexpStatement`
-/

@[expose] public section

namespace AbcSubexp

/-- The subexponential radical bound for positive coprime triples. -/
def subexpStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
    Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε

end AbcSubexp
