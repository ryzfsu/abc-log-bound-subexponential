/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

/-! # Fourier sums over a finite integer orbit -/

@[expose] public section

noncomputable section

open Finset Real

namespace AbcSubexp

/-- The additive character of period one, evaluated at a real frequency. -/
def phaseCharacter (u : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * π * u : ℝ) : ℂ))

/-- Every additive phase character has unit norm. -/
@[simp] theorem norm_phaseCharacter (u : ℝ) : ‖phaseCharacter u‖ = 1 := by
  simp [phaseCharacter, Complex.norm_exp]

/-- The phase character is multiplicative under addition. -/
theorem phaseCharacter_add (u v : ℝ) :
    phaseCharacter (u + v) = phaseCharacter u * phaseCharacter v := by
  simp [phaseCharacter, mul_add, Complex.exp_add]

/-- Integer frequencies evaluate to the unit character. -/
@[simp] theorem phaseCharacter_intCast (n : ℤ) : phaseCharacter n = 1 := by
  unfold phaseCharacter
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring

/-- The chord of a unit-circle character dominates four times the phase distance. -/
theorem four_mul_dist_le_phaseCharacter (u : ℝ) :
    4 * |u - round u| ≤ ‖phaseCharacter u - 1‖ := by
  let v := u - (round u : ℝ)
  have hv : |v| ≤ 1 / 2 := abs_sub_round u
  have he : phaseCharacter u = phaseCharacter v := by
    calc
      phaseCharacter u = phaseCharacter (v + (round u : ℝ)) := by
        simp [v]
      _ = phaseCharacter v := by simp [phaseCharacter_add]
  have harg : |π * v| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos pi_pos]
    linarith [mul_le_mul_of_nonneg_left hv pi_pos.le]
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos pi_pos] at hsin
  have hcancel : 2 / π * (π * |v|) = 2 * |v| := by field_simp
  rw [hcancel] at hsin
  rw [he, phaseCharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * π * v / 2 = π * v by ring, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  change 4 * |v| ≤ _
  linarith

/-- On any interval, a separated nonconstant Fourier mode has bounded total contribution. -/
theorem phaseCharacter_Ico_norm_le {u δ : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ |u - round u|) {lo hi : ℕ} (hI : lo ≤ hi) :
    ‖∑ n ∈ Ico lo hi, phaseCharacter u ^ n‖ ≤ 1 / (2 * δ) := by
  have hchord := four_mul_dist_le_phaseCharacter u
  have hden : 0 < ‖phaseCharacter u - 1‖ := by linarith
  have hne : phaseCharacter u ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hden)
  rw [geom_sum_Ico hne hI, norm_div]
  apply (div_le_div_iff₀ hden (by positivity : (0:ℝ) < 2 * δ)).mpr
  have hnum := norm_sub_le (phaseCharacter u ^ hi) (phaseCharacter u ^ lo)
  simp [norm_pow] at hnum
  nlinarith [mul_le_mul_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 2 * δ)]

end AbcSubexp
