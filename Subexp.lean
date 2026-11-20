/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S1_Statement.Statement
public import Subexp.Conclusion.Assembly

/-!
# The subexponential radical bound

This module exports `AbcSubexp.subexp` for positive coprime triples.
-/

@[expose] public section

namespace AbcSubexp

/-- Theorem 1.1 bounds the logarithm of the sum by each positive power of the radical. -/
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
        Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε :=
  assembledSubexp

end AbcSubexp
