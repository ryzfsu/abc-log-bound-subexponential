/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S7_Interpolation.LucasDigits
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Elimination of low-digit blocks

The Newton evaluation rows on each selected residue class recover its high-digit
coefficients once the classes of smaller total low-digit degree have been eliminated.
This is the residue-class lifting argument of Section 7.

## Main results
* `AbcSubexp.digitBlockCoefficients_eq_zero`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators

/-- Injective evaluation on each high-digit witness set implies injective evaluation on
the corresponding lifted Newton rows. Only the residue classes in `R` require rows. -/
theorem digitBlockCoefficients_eq_zero {m q : ℕ} [Fact q.Prime]
    (R : Finset (Fin m → ℕ)) (H : (Fin m → ℕ) → Finset (Fin m → ℕ))
    (W : (Fin m → ℕ) → (Fin m → ℕ) → Prop)
    (c : (Fin m → ℕ) → (Fin m → ℕ) → ZMod q)
    (hdigit : ∀ s ∈ R, ∀ i, s i < q)
    (hhigh : ∀ r ∈ R, (∀ y, W r y → ∑ u ∈ H r, c r u * digitBinomial q y u = 0) →
      ∀ u ∈ H r, c r u = 0)
    (hrow : ∀ r ∈ R, ∀ y, W r y →
      ∑ s ∈ R, ∑ u ∈ H s, c s u * digitBinomial q
        (fun i => q * y i + r i) (fun i => q * u i + s i) = 0) :
    ∀ r ∈ R, ∀ u ∈ H r, c r u = 0 := by
  classical
  intro r
  generalize hdeg : (∑ i, r i) = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    intro hr
    apply hhigh r hr
    intro y hy
    let block (s : Fin m → ℕ) := ∑ u ∈ H s, c s u * digitBinomial q
      (fun i => q * y i + r i) (fun i => q * u i + s i)
    have hoff (s : Fin m → ℕ) (hs : s ∈ R) (hne : s ≠ r) : block s = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hle : s ≤ r
      · obtain ⟨i, hi⟩ : ∃ i, s i < r i := by
          by_contra! hall
          exact hne (le_antisymm hle hall)
        have hlt : (∑ i, s i) < n := by
          rw [← hdeg]
          exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i, Finset.mem_univ i, hi⟩
        rw [ih _ hlt s rfl hs u hu, zero_mul]
      · rw [digitBinomial_split_digits q y u r s (hdigit r hr) (hdigit s hs),
            digitBinomial_zero_of_not_le q hle, zero_mul, mul_zero]
    have hall : ∑ s ∈ R, block s = 0 := hrow r hr y hy
    rw [Finset.sum_eq_single_of_mem r hr hoff] at hall
    simpa only [block, digitBinomial_split_digits q y _ r r (hdigit r hr) (hdigit r hr),
      digitBinomial_self, one_mul] using hall

end AbcSubexp
