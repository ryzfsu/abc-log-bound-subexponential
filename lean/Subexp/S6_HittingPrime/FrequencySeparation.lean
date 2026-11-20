/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# The cost of bounded frequencies

In Section 6, the transverse contribution of bounded integer frequencies
must fit below the height floor supplied by the grouped lattice.
-/

@[expose] public section

open Filter Real
open scoped BigOperators

namespace AbcSubexp

/-- The total cost of bounded coefficients over all rows is eventually at most
half the grouped lattice height floor from Section 4. -/
theorem eventually_grouped_frequency_cost (m F : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      3 * x * ((⌊x ^ (1 / 3 : ℝ)⌋₊ : ℝ) * m * F) ≤ exp (sqrt x) / 2 := by
  let K : ℝ := 720 * m * F
  filter_upwards [eventually_ge_atTop (max 1 (K ^ 2))] with x hx
  have hx1 : 1 ≤ x := (le_max_left ..).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hroot : K ≤ sqrt x := Real.le_sqrt_of_sq_le ((le_max_right ..).trans hx)
  have hs : (⌊x ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ x :=
    (Nat.floor_le (Real.rpow_nonneg hx0 _)).trans (Real.rpow_le_self_of_one_le hx1 (by norm_num))
  have hf := Real.pow_div_factorial_le_exp (sqrt x) (Real.sqrt_nonneg x) 5
  norm_num [Nat.factorial] at hf
  have hsq := Real.sq_sqrt hx0
  have hpow : sqrt x ^ 5 = x ^ 2 * sqrt x := by
    calc
      _ = (sqrt x ^ 2) ^ 2 * sqrt x := by ring
      _ = _ := by rw [hsq]
  rw [hpow] at hf
  have hbudget := mul_le_mul_of_nonneg_left hroot (sq_nonneg x)
  have hcount : 3 * x * ((⌊x ^ (1 / 3 : ℝ)⌋₊ : ℝ) * m * F) ≤
      3 * x * (x * m * F) := by gcongr
  dsimp [K] at hbudget
  nlinarith only [hcount, hbudget, hf]

/-- A shortest-vector lower bound and a bound on the transverse cost together
separate the nearest integer from the actual roof phase. -/
theorem frequency_separation_of_height {Y h phase transverse : ℝ}
    (hh : 0 < h) (hcost : transverse ≤ Y / 2)
    (hheight : Y < 2 * h * |(-(round phase : ℤ) : ℝ) + phase| + transverse) :
    Y / (4 * h) ≤ |phase - (round phase : ℤ)| := by
  have hshift : (-(round phase : ℤ) : ℝ) + phase = phase - (round phase : ℤ) := by
    ring
  rw [hshift] at hheight
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end AbcSubexp
