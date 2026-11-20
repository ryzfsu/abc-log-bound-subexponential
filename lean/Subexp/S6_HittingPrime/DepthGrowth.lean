/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Mathlib.Analysis.Complex.Exponential

/-! # Eventual lower bounds for the native contact depth and degree -/

@[expose] public section

namespace AbcSubexp

open Parameters Real

/-- For each fixed working exponent and depth target, a common tail meets the
depth target and the degree lower bound required in the hitting-prime argument. -/
theorem Contact.exists_depth_degree_threshold {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ X₀ : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X₀ ≤ t.thirdLogRadical →
      K ≤ (c.depth : ℝ) ∧ (depthParameter ε + 1) ^ 2 ≤ c.degree := by
  let e := exponent ε
  let N : ℕ := (depthParameter ε + 1) ^ 2
  let A : ℝ := e ^ 2 * (3 * e) ^ 2 / 2
  let M : ℝ := max K ((N : ℝ) + 1)
  have he : 0 < e := lt_min hε (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨max 1 (M / A), fun t c hX => ?_⟩
  have hx : 0 < t.thirdLogRadical := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hX)
  have hM : M ≤ A * t.thirdLogRadical := by
    rw [mul_comm]
    exact (div_le_iff₀ hA).mp ((le_max_right _ _).trans hX)
  have hexp : (3 * e * t.thirdLogRadical) ^ 2 / 2 ≤ exp (3 * e * t.thirdLogRadical) := by
    have hnonneg : 0 ≤ 3 * e * t.thirdLogRadical := by positivity
    have hquad := quadratic_le_exp_of_nonneg hnonneg
    linarith
  have hdepth : A * t.thirdLogRadical < (c.depth : ℝ) := by
    refine lt_of_mul_lt_mul_right ?_ hx.le
    calc
      A * t.thirdLogRadical * t.thirdLogRadical = e ^ 2 * ((3 * e * t.thirdLogRadical) ^ 2 / 2) := by dsimp [A]; ring
      _ ≤ e ^ 2 * exp (3 * e * t.thirdLogRadical) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg e)
      _ = (2 * e) * ((e / 2) * exp (3 * e * t.thirdLogRadical)) := by ring
      _ ≤ (2 * e) * AbcTwoNinths.Basic.rationalHeight c.source :=
        mul_le_mul_of_nonneg_left c.axial_height_lower (by positivity)
      _ < (c.depth : ℝ) * log (c.prime : ℝ) := c.depth_share
      _ ≤ (c.depth : ℝ) * t.thirdLogRadical := mul_le_mul_of_nonneg_left c.log_upper (by positivity)
  have hN : N + 1 ≤ c.depth := by
    exact_mod_cast ((le_max_right K ((N : ℝ) + 1)).trans (hM.trans hdepth.le))
  have hmargin : 0 ≤ degreeMargin ε := div_nonneg he.le (by norm_num)
  have hceil : c.depth ≤ ⌈(1 + degreeMargin ε) * (c.depth : ℝ)⌉₊ := by
    have hreal : (c.depth : ℝ) ≤ (1 + degreeMargin ε) * (c.depth : ℝ) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (a := (1 : ℝ)) hmargin)
          (Nat.cast_nonneg c.depth))
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  refine ⟨(le_max_left K ((N : ℝ) + 1)).trans (hM.trans hdepth.le), ?_⟩
  change N ≤ ⌈(1 + degreeMargin ε) * (c.depth : ℝ)⌉₊ - 1
  omega

end AbcSubexp
