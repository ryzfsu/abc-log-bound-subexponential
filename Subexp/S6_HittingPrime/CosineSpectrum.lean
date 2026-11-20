/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.CosineFourier
public import Subexp.S6_HittingPrime.CosineMajorant

/-! # Finite spectrum of the miss majorant on one row -/

@[expose] public section

noncomputable section

open scoped BigOperators
open AbcSubexp.CosineFourier

namespace AbcSubexp.CosineSpectrum

variable {m : ℕ}

/-- A formal mode across all coordinates of one row. -/
abbrev Mode (m F : ℕ) := Fin m → Fin (2 * F + 1)

/-- Tensor weight of the unshifted cosine kernel. -/
def amplitude (F : ℕ) (k : Mode m F) : ℝ := ∏ i, weight F (k i)

/-- The scalar phase of a formal mode on a row. -/
def angle (F : ℕ) (x : Fin m → ℝ) (k : Mode m F) : ℝ :=
  ∑ i, (frequency F (k i) : ℝ) * x i

/-- The character evaluated at the row slopes. -/
def node (F : ℕ) (x : Fin m → ℝ) (k : Mode m F) : ℂ := phase (angle F x k)

/-- The Fourier coefficient of the cosine kernel centered at `a`. -/
def kernelCoefficient (F : ℕ) (a : Fin m → ℝ) (k : Mode m F) : ℂ :=
  (amplitude F k : ℂ) * phase (-angle F a k)

/-- Centered Fourier coefficient of the majorant. -/
def coefficient (η : ℝ) (F : ℕ) (a : Fin m → ℝ) (k : Mode m F) : ℂ :=
  (if k = 0 then ((1 + (Real.cos (Real.pi * η) ^ 2) ^ F : ℝ) : ℂ) else 0) -
    kernelCoefficient F a k

private theorem amplitude_nonneg (F : ℕ) (k : Mode m F) : 0 ≤ amplitude F k :=
  Finset.prod_nonneg fun _ _ => weight_nonneg _ _

private theorem amplitude_sum (F : ℕ) : ∑ k : Mode m F, amplitude F k = 1 := by
  simp [amplitude, ← Fintype.prod_sum, weights_sum_one]

private theorem kernelCoefficient_norm (F : ℕ) (a : Fin m → ℝ) (k : Mode m F) :
    ‖kernelCoefficient F a k‖ = amplitude F k := by
  simp [kernelCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (amplitude_nonneg F k)]

/-- The zero mode has the constant character. -/
@[simp] theorem node_zero (F : ℕ) (x : Fin m → ℝ) : node F x 0 = 1 := by
  simp [node, angle]

/-- Finite products of characters add their arguments. -/
theorem prod_phase {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∏ i ∈ s, phase (x i) = phase (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, phase_add]

private theorem kernel_expansion (F : ℕ) (x a : Fin m → ℝ) (v : ℕ) :
    (cosineKernel F (fun i => (v : ℝ) * x i - a i) : ℂ) =
      ∑ k : Mode m F, kernelCoefficient F a k * node F x k ^ v := by
  classical
  unfold cosineKernel
  simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  simp_rw [CosineFourier.expansion, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, prod_phase]
  have hangle : (∑ i, (frequency F (k i) : ℝ) * ((v : ℝ) * x i - a i)) =
      -angle F a k + (v : ℝ) * angle F x k := by
    unfold angle
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hangle, phase_add, phase_nat_mul]
  simp [kernelCoefficient, node, amplitude, mul_assoc]

/-- Fourier expansion on the actual centered one-row orbit. -/
theorem expansion (η : ℝ) (F : ℕ) (a x : Fin m → ℝ) (v : ℕ) :
    (cosineMissMajorant η F (fun i => (v : ℝ) * x i - a i) : ℂ) =
      ∑ k : Mode m F, coefficient η F a k * node F x k ^ v := by
  classical
  unfold cosineMissMajorant coefficient
  rw [Complex.ofReal_sub, kernel_expansion]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  simp [ite_mul]

/-- The absolute mass of a row is bounded independently of its dimension. -/
theorem mass_le_three (η : ℝ) (F : ℕ) (a : Fin m → ℝ)
    (hρ : (Real.cos (Real.pi * η) ^ 2) ^ F ≤ 1) :
    ∑ k : Mode m F, ‖coefficient η F a k‖ ≤ 3 := by
  classical
  let d := 1 + (Real.cos (Real.pi * η) ^ 2) ^ F
  have hd : 0 ≤ d := by dsimp [d]; positivity
  calc
    _ ≤ ∑ k : Mode m F, (‖(if k = 0 then (d : ℂ) else 0)‖ + amplitude F k) :=
      Finset.sum_le_sum fun k _ => (norm_sub_le _ _).trans_eq
        (congrArg (_ + ·) (kernelCoefficient_norm F a k))
    _ = d + 1 := by
      rw [Finset.sum_add_distrib, amplitude_sum]
      simp [apply_ite norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    _ ≤ 3 := by dsimp [d]; linarith

/-- The cosine kernel has at least this much constant weight. -/
theorem central_amplitude_lower (m F : ℕ) :
    ((2 * (F : ℝ) + 1) ^ m)⁻¹ ≤ amplitude F (0 : Mode m F) := by
  rw [show amplitude F (0 : Mode m F) = (weight F 0) ^ m by simp [amplitude], ← inv_pow]
  apply pow_le_pow_left₀ (by positivity)
  simpa using central_weight_lower F

/-- The norm of the zero mode is the exact constant term of the majorant. -/
theorem constant_norm (η : ℝ) (F : ℕ) (a : Fin m → ℝ) :
    ‖coefficient η F a 0‖ =
      1 + (Real.cos (Real.pi * η) ^ 2) ^ F - amplitude F (0 : Mode m F) := by
  classical
  have hup : amplitude F (0 : Mode m F) ≤ 1 := by
    rw [← amplitude_sum (m := m) F]
    exact Finset.single_le_sum (fun k _ => amplitude_nonneg F k) (Finset.mem_univ _)
  have hρ : 0 ≤ (Real.cos (Real.pi * η) ^ 2) ^ F := by positivity
  have hpos : 0 ≤ 1 + (Real.cos (Real.pi * η) ^ 2) ^ F - amplitude F (0 : Mode m F) := by linarith
  simp only [coefficient, ite_true, kernelCoefficient, angle, Pi.zero_apply, frequency_zero,
    Int.cast_zero, zero_mul, Finset.sum_const_zero, neg_zero, phase_zero, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]

/-- With the degree given by `exists_cosineDegree`, the gap is at least half
the actual constant weight of the cosine kernel. -/
theorem constant_norm_le_central (η : ℝ) (F : ℕ) (a : Fin m → ℝ)
    (hsmall : (Real.cos (Real.pi * η) ^ 2) ^ F ≤ ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2) :
    ‖coefficient η F a 0‖ ≤ 1 - amplitude F (0 : Mode m F) / 2 := by
  rw [constant_norm]
  linarith [central_amplitude_lower m F]

/-- An explicit gap for the constant coefficient. -/
theorem constant_norm_le (η : ℝ) (F : ℕ) (a : Fin m → ℝ)
    (hsmall : (Real.cos (Real.pi * η) ^ 2) ^ F ≤ ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2) :
    ‖coefficient η F a 0‖ ≤ 1 - ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2 := by
  linarith [constant_norm_le_central η F a hsmall, central_amplitude_lower m F]

end AbcSubexp.CosineSpectrum
