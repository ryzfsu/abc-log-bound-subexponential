/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp

/-!
# Proof of the subexponential radical bound

The assembly theorem gives Theorem 1.1 for positive coprime triples.
-/

@[expose] public section

namespace AbcSubexp.Solution

/-- Theorem 1.1 of the paper. -/
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
        Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε :=
  AbcSubexp.subexp

end AbcSubexp.Solution
