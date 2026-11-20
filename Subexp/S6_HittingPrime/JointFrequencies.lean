/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.CosineSpectrum
public import Subexp.S6_HittingPrime.GeometricOrbit

/-!
# Integer frequencies of the product character

Each nonconstant mode of the product spectrum gives a nonzero integer vector on
the same rows and coordinates as the slopes. Its absolute coefficient sum is
bounded by the number of coordinates times the one-coordinate frequency cap.

## Main results
* `AbcSubexp.CosineSpectrum.jointFrequency_ne_zero`
* `AbcSubexp.CosineSpectrum.jointFrequency_mass_le`
* `AbcSubexp.CosineSpectrum.productNode_eq_character`
* `AbcSubexp.CosineSpectrum.productNode_Ico_norm_le`
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open AbcSubexp.CosineFourier

namespace AbcSubexp.CosineSpectrum

variable {s m : ℕ}

/-- The integer vector multiplying the slopes in a product of row modes. -/
def jointFrequency (F : ℕ) (k : Fin s → Mode m F) (b : Fin s) (i : Fin m) : ℤ :=
  frequency F (k b i)

/-- Every nonzero array of formal modes gives a nonzero integer vector. -/
theorem jointFrequency_ne_zero (F : ℕ) {k : Fin s → Mode m F} (hk : k ≠ 0) :
    jointFrequency F k ≠ 0 := by
  intro h
  apply hk
  funext b i
  exact (frequency_eq_zero_iff F _).1 (congrFun (congrFun h b) i)

/-- The joint integer vector has natural absolute mass at most `s*m*F`. -/
theorem jointFrequency_mass_le (F : ℕ) (k : Fin s → Mode m F) :
    (∑ b, ∑ i, (jointFrequency F k b i).natAbs) ≤ s * m * F := by
  calc
    _ ≤ ∑ _b : Fin s, ∑ _i : Fin m, F := by
      refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ => ?_
      exact_mod_cast (show ((jointFrequency F k b i).natAbs : ℤ) ≤ F by
        rw [Int.natCast_natAbs]
        exact abs_frequency_le F _)
    _ = _ := by simp [Nat.mul_assoc]

/-- The row product character is evaluated at the integer dot product with the slopes. -/
theorem productNode_eq_character (F : ℕ) (x : Fin s → Fin m → ℝ)
    (k : Fin s → Mode m F) :
    ∏ b, node F (x b) (k b) =
      phaseCharacter (∑ b, ∑ i, (jointFrequency F k b i : ℝ) * x b i) := by
  unfold node
  rw [prod_phase]
  unfold angle jointFrequency phase phaseCharacter
  rw [mul_comm Complex.I]

/-- Short-vector separation of the actual slopes bounds every nonconstant mode
sum on an integer interval. -/
theorem productNode_Ico_norm_le (F : ℕ) (x : Fin s → Fin m → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ y : Fin s → Fin m → ℤ, y ≠ 0 → (∑ b, ∑ i, (y b i).natAbs) ≤ s * m * F →
      δ ≤ |(∑ b, ∑ i, (y b i : ℝ) * x b i) - round (∑ b, ∑ i, (y b i : ℝ) * x b i)|)
    {lo hi : ℕ} (hI : lo ≤ hi) (k : Fin s → Mode m F) (hk : k ≠ 0) :
    ‖∑ v ∈ Finset.Ico lo hi, (∏ b, node F (x b) (k b)) ^ v‖ ≤ 1 / (2 * δ) := by
  rw [productNode_eq_character]
  exact phaseCharacter_Ico_norm_le hδ
    (hsep _ (jointFrequency_ne_zero F hk) (jointFrequency_mass_le F k)) hI

end AbcSubexp.CosineSpectrum
