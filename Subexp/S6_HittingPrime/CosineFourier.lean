/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-! # Finite Fourier coefficients of an even cosine power -/

@[expose] public noncomputable section

open scoped BigOperators
open Complex

namespace AbcSubexp.CosineFourier

/-- The ordinary binomial column corresponding to a centered mode. -/
def column (F : ℕ) : Equiv.Perm (Fin (2 * F + 1)) :=
  Equiv.swap 0 ⟨F, by omega⟩

/-- The integer frequency of a centered mode. -/
def frequency (F : ℕ) (k : Fin (2 * F + 1)) : ℤ := ((column F k).val : ℤ) - F

/-- The normalized binomial coefficient of a centered mode. -/
def weight (F : ℕ) (k : Fin (2 * F + 1)) : ℝ :=
  ((2 * F).choose (column F k).val : ℝ) / 4 ^ F

/-- The complex character at one real phase. -/
def phase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

/-- The centered mode at index zero has zero frequency. -/
@[simp] theorem frequency_zero (F : ℕ) : frequency F 0 = 0 := by
  simp [frequency, column]

/-- Zero frequency occurs only at the centered mode. -/
theorem frequency_eq_zero_iff (F : ℕ) (k : Fin (2 * F + 1)) : frequency F k = 0 ↔ k = 0 := by
  refine ⟨fun h => (column F).injective ?_, fun h => h ▸ frequency_zero F⟩
  apply Fin.ext
  have hv : ((column F k).val : ℤ) = F := sub_eq_zero.mp h
  simpa [column] using hv

/-- Every centered frequency lies in the interval from `-F` to `F`. -/
theorem abs_frequency_le (F : ℕ) (k : Fin (2 * F + 1)) : |frequency F k| ≤ F := by
  have h := (column F k).isLt
  simp only [frequency, abs_le]
  omega

/-- Every normalized binomial weight is nonnegative. -/
theorem weight_nonneg (F : ℕ) (k : Fin (2 * F + 1)) : 0 ≤ weight F k := by
  unfold weight
  positivity

/-- The normalized binomial weights sum to one. -/
theorem weights_sum_one (F : ℕ) : ∑ k, weight F k = 1 := by
  let w (j : Fin (2 * F + 1)) := ((2 * F).choose j.val : ℝ) / (4 : ℝ) ^ F
  change ∑ k, w (column F k) = 1
  rw [Equiv.sum_comp, show (∑ j, w j) = (∑ j : Fin (2 * F + 1), ((2 * F).choose j.val : ℝ)) / 4 ^ F by simp [w, Finset.sum_div]]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((2 * F).choose j : ℝ)), ← Nat.cast_sum,
    Nat.sum_range_choose, Nat.cast_pow, pow_mul]
  norm_num

/-- Every binomial weight is bounded by the central weight. -/
theorem weight_le_central (F : ℕ) (k : Fin (2 * F + 1)) : weight F k ≤ weight F 0 := by
  unfold weight
  gcongr
  simp only [column, Equiv.swap_apply_left]
  exact_mod_cast Nat.choose_le_centralBinom _ F

/-- The central weight is at least the reciprocal of the number of modes. -/
theorem central_weight_lower (F : ℕ) : ((2 * F + 1 : ℕ) : ℝ)⁻¹ ≤ weight F 0 := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (2 * F + 1))))
    (fun i _ => weight_le_central F i)
  rw [weights_sum_one] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- The phase at zero is the unit complex number. -/
@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

/-- Every phase has unit norm. -/
@[simp] theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp_mul_I]

/-- Phases turn addition into multiplication. -/
theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, mul_add, add_mul, Complex.exp_add]

/-- A natural multiple of a phase is the corresponding power. -/
theorem phase_nat_mul (n : ℕ) (t : ℝ) : phase (n * t) = phase t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simpa [Nat.cast_succ, add_mul, phase_add, pow_succ] using congrArg (· * phase t) ih

private theorem raw_expansion (F : ℕ) (t : ℝ) :
    (Real.cos (Real.pi * t) : ℂ) ^ (2 * F) =
      ∑ j : Fin (2 * F + 1), (((2 * F).choose j : ℕ) : ℂ) / 4 ^ F *
        phase (((j : ℝ) - F) * t) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (((2 * F).choose j : ℕ) : ℂ) / 4 ^ F *
    phase (((j : ℝ) - F) * t)), Complex.ofReal_cos, Complex.cos, div_pow, add_pow]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ 2 * F := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have hpow : (2 : ℂ) ^ (2 * F) = 4 ^ F := by rw [pow_mul]; norm_num
  rw [hpow]
  unfold phase
  push_cast [Nat.cast_sub hle]
  ring_nf

/-- Each even cosine power has finite support in the integer interval from `-F` to `F`. -/
theorem expansion (F : ℕ) (t : ℝ) : (Real.cos (Real.pi * t) : ℂ) ^ (2 * F) =
    ∑ k, (weight F k : ℂ) * phase ((frequency F k : ℝ) * t) := by
  let f (j : Fin (2 * F + 1)) := (((2 * F).choose j : ℕ) : ℂ) / 4 ^ F *
    phase (((j : ℝ) - F) * t)
  calc
    _ = ∑ j, f j := raw_expansion F t
    _ = ∑ k, f (column F k) := (Equiv.sum_comp (column F) f).symm
    _ = _ := by simp [f, weight, frequency]

end AbcSubexp.CosineFourier
