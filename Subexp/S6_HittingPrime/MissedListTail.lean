/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# The error in counting indices that miss every list

The number of disjoint lists is the integer part of the cube root.
For this choice both terms in the Fourier majorant fit strictly below
the lower bound for the number of primes in the interval.

## Main results
* `AbcSubexp.eventually_missedListBound_lt_primeBudget`
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace AbcSubexp

/-- The geometric decay of the constant Fourier coefficient and the height
error jointly leave a strict margin in the prime count. -/
theorem eventually_missedListBound_lt_primeBudget {a M A B : ℝ}
    (ha : 0 ≤ a) (ha' : a < 1) (hM : 0 < M) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, ∀ (X h : ℝ), 1 < X → 0 ≤ h → h ≤ A * X * x →
      log X ≤ B * x →
      X * a ^ ⌊x ^ ((1 : ℝ) / 3)⌋₊ +
        M ^ ⌊x ^ ((1 : ℝ) / 3)⌋₊ * h / exp (sqrt x) < X / (5 * log X) := by
  let s (x : ℝ) := ⌊x ^ ((1 : ℝ) / 3)⌋₊
  have hs : Tendsto s atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 3))
  have hsReal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hs
  have err₁ := (tendsto_pow_const_mul_const_pow_of_lt_one 3 ha ha').comp hs
  have err₂ := (tendsto_pow_const_mul_const_pow_of_lt_one 6
    (exp_pos (-1)).le (by simp : exp (-1) < 1)).comp hs
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hsReal.eventually_ge_atTop 1, hsReal.eventually_ge_atTop ((log M + 1)^2),
    err₁.eventually_lt_const (by positivity : 0 < 1 / (80 * B)),
    err₂.eventually_lt_const (by positivity : 0 < 1 / (640 * A * B))] with
    x hx hs₁ hslog he₁ he₂
  let n := s x
  change 1 ≤ (n : ℝ) at hs₁
  change (log M + 1)^2 ≤ (n : ℝ) at hslog
  change (n : ℝ)^3 * a ^ n < 1 / (80 * B) at he₁
  change (n : ℝ)^6 * exp (-1) ^ n < 1 / (640 * A * B) at he₂
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hroot : (x ^ ((1 : ℝ) / 3))^3 = x := by
    simpa only [one_div, Nat.cast_ofNat] using rpow_inv_natCast_pow hx (by decide : 3 ≠ 0)
  have hfloor : (n : ℝ) ≤ x ^ ((1 : ℝ) / 3) :=
    Nat.floor_le (rpow_nonneg hx _)
  have hceil : x ^ ((1 : ℝ) / 3) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : (n : ℝ)^3 ≤ x := hroot ▸ pow_le_pow_left₀ hn hfloor 3
  have hhi : x ≤ 8 * (n : ℝ)^3 := by
    calc
      x = (x ^ ((1 : ℝ) / 3))^3 := hroot.symm
      _ ≤ (2 * (n : ℝ))^3 := pow_le_pow_left₀ (rpow_nonneg hx _) (by linarith) _
      _ = _ := by ring
  have hfourier : M ^ n / exp (sqrt x) ≤ exp (-1) ^ n := by
    have hsq : ((log M + 1) * n)^2 ≤ x := by
      calc
        _ = (log M + 1)^2 * (n : ℝ)^2 := by ring
        _ ≤ n * (n : ℝ)^2 := by gcongr
        _ = (n : ℝ)^3 := by ring
        _ ≤ x := hlo
    have hlen : (log M + 1) * n ≤ sqrt x :=
      (le_abs_self _).trans (by simpa [sqrt_sq_eq_abs] using sqrt_le_sqrt hsq)
    rw [← exp_log hM, ← exp_nat_mul, ← exp_sub, ← exp_nat_mul]
    apply exp_le_exp.mpr
    linarith [mul_comm (log M) (n : ℝ)]
  intro X h hX hh hhcap hlog
  change X * a ^ n + M ^ n * h / exp (sqrt x) < X / (5 * log X)
  have hXpos := zero_lt_one.trans hX
  have hlogpos := log_pos hX
  have hb₁ : 10 * B * (x * a ^ n) < 1 := by
    have he := (lt_div_iff₀ (by positivity)).mp he₁
    nlinarith only [he, mul_le_mul_of_nonneg_right hhi (by positivity : 0 ≤ a ^ n),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi (pow_nonneg ha n)) hB.le]
  have hb₂ : 10 * A * B * (x^2 * (M^n / exp (sqrt x))) < 1 := by
    have he := (lt_div_iff₀ (by positivity)).mp he₂
    have aux : x^2 * (M^n / exp (sqrt x)) ≤ (8 * (n : ℝ)^3)^2 * exp (-1)^n := by
      gcongr
    nlinarith only [he, mul_le_mul_of_nonneg_right aux (mul_nonneg hA.le hB.le)]
  apply (lt_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (X * a ^ n + M ^ n * (A * X * x) / exp (sqrt x)) * (5 * (B * x)) := by gcongr
    _ = X * (5 * B * (x * a^n) + 5 * A * B * (x^2 * (M^n / exp (sqrt x)))) := by ring
    _ < X := mul_lt_of_lt_one_right hXpos (by linarith)

end AbcSubexp
