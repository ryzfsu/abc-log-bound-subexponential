/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Primes in the upper two thirds of an interval

Chebyshev's theta bounds give a lower bound for the number of primes in
`(X / 3, X]` for sufficiently large natural `X`. A finite exceptional set
of smaller cardinality leaves a prime in the interval with a successful block.
-/

@[expose] public section

open Finset Filter Real
open scoped Topology

namespace AbcSubexp

/-- Primes in the natural interval (X / 3, X]. -/
def thirdWindowPrimes (X : ℕ) : Finset ℕ :=
  X.primesLE \ (X / 3).primesLE

/-- Membership is equivalent to primality together with `X < 3 * q` and `q ≤ X`. -/
theorem mem_thirdWindowPrimes {X q : ℕ} :
    q ∈ thirdWindowPrimes X ↔ q.Prime ∧ X < 3 * q ∧ q ≤ X := by
  simp only [thirdWindowPrimes, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hq, hp⟩, hn⟩
    exact ⟨hp, by by_contra! hc; exact hn ⟨by omega, hp⟩, hq⟩
  · rintro ⟨hp, hq, hX⟩
    exact ⟨⟨hX, hp⟩, fun h => by omega⟩

private theorem thirdWindow_theta_mass (X : ℕ) :
    ∑ p ∈ thirdWindowPrimes X, log p =
      Chebyshev.theta X - Chebyshev.theta (X / 3 : ℕ) := by
  have hsub : (X / 3).primesLE ⊆ X.primesLE := by
    intro q hq
    obtain ⟨h, hp⟩ := Nat.mem_primesLE.mp hq
    exact Nat.mem_primesLE.mpr ⟨h.trans (Nat.div_le_self _ _), hp⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

/-- The third-window primes contribute more than X/5 to Chebyshev's theta sum. -/
theorem eventually_thirdWindow_mass :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) / 5 < ∑ p ∈ thirdWindowPrimes X, log p := by
  have hsmall := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 1000 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    eventually_ge_atTop (1000 : ℕ)] with X hlog hX
  have hX' : (1000 : ℝ) ≤ X := by exact_mod_cast hX
  have hpos : (0 : ℝ) < X := by linarith
  have hge : (1 : ℝ) ≤ X := by linarith
  have hsr := Real.sq_sqrt hpos.le
  have hspos := Real.sqrt_nonneg (X : ℝ)
  have hsle : √(X : ℝ) ≤ X := by nlinarith
  have hl : log (X : ℝ) ≤ (1 / 1000 : ℝ) * √(X : ℝ) := by
    change ‖log (X : ℝ)‖ ≤ 1 / 1000 * ‖(X : ℝ) ^ (1 / 2 : ℝ)‖ at hlog
    rwa [← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hge), abs_of_nonneg hspos] at hlog
  have hadd : log ((X : ℝ) + 1) ≤ log 2 + log X := by
    rw [← Real.log_mul (by norm_num) hpos.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hdiv : ((X / 3 : ℕ) : ℝ) * 3 ≤ X := by
    exact_mod_cast Nat.div_mul_le_self X 3
  have hu := Chebyshev.theta_le_log4_mul_x (show 0 ≤ ((X / 3 : ℕ) : ℝ) by positivity)
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h4] at hu
  have h2 := Real.log_two_gt_d9
  have h2u := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  rw [thirdWindow_theta_mass]
  nlinarith only [Chebyshev.theta_ge X, hu, hadd, hl, hsle, hsr, h2u, hX',
    mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (show 1 ≤ (2 : ℝ) by norm_num)),
    mul_le_mul_of_nonneg_left hl hspos, mul_le_mul_of_nonneg_right h2.le hpos.le]

/-- For sufficiently large `X`, the window contains more than `X / (5 * log X)` primes. -/
theorem eventually_thirdWindow_card :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) / (5 * log X) < (thirdWindowPrimes X).card := by
  filter_upwards [eventually_thirdWindow_mass, eventually_ge_atTop (2 : ℕ)] with X hm hX
  have hx : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hsum : ∑ p ∈ thirdWindowPrimes X, log p ≤
      (thirdWindowPrimes X).card * log X := by
    calc
      _ ≤ ∑ _p ∈ thirdWindowPrimes X, log X := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp', _, hpX⟩ := mem_thirdWindowPrimes.mp hp
        exact Real.log_le_log (by exact_mod_cast hp'.pos : (0 : ℝ) < p)
          (by exact_mod_cast hpX : (p : ℝ) ≤ X)
      _ = _ := by simp
  have hlog := Real.log_pos hx
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 5 * log X)).mpr
  linarith

/-- A single prime with a single successful block, for any finite covering of the misses. -/
theorem exists_thirdWindow_prime_and_block {ι : Type*} {X : ℕ} (exceptional : Finset ℕ)
    (hit : ℕ → ι → Prop) (hcard : exceptional.card < (thirdWindowPrimes X).card)
    (hmiss : ∀ q ∈ thirdWindowPrimes X, (∀ i, ¬hit q i) → q ∈ exceptional) :
    ∃ q i, q.Prime ∧ X < 3 * q ∧ q ≤ X ∧ hit q i := by
  classical
  by_contra! hn
  apply (Nat.not_le_of_gt hcard) (card_le_card ?_)
  intro q hq
  obtain ⟨hp, hlo, hhi⟩ := mem_thirdWindowPrimes.mp hq
  exact hmiss q hq fun i => hn q i hp hlo hhi

end AbcSubexp
