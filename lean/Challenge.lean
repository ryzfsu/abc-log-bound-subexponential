/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib

/-!
# The subexponential radical bound

Theorem 1.1 bounds `log c` for positive coprime summands `a + b = c`.
For every positive real exponent, the bound is a constant times the
corresponding power of the radical of `a * b * c`.
-/

@[expose] public section

namespace AbcTwoNinths

/-- The radical of a natural number, the product of its distinct prime factors. -/
def radNat (n : Nat) : Nat :=
  ∏ p ∈ n.primeFactors, p

/-- The positive, coprime triples with `a + b = c` in Theorem 1.1. -/
def TwoNinthsTriple (a b c : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

end AbcTwoNinths

namespace AbcSubexp

/-- The subexponential radical bound for positive coprime triples. -/
def subexpStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
    Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε

/-- Theorem 1.1 of the paper. -/
theorem subexp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
        Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε := by
  sorry

end AbcSubexp
