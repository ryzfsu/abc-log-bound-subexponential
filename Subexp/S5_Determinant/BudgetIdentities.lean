/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-! # Exact budgets for the determinant comparison -/

@[expose] public section

noncomputable section

namespace AbcSubexp.Contact

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)

private theorem height_pos (hε : 0 < ε) : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
  lt_of_lt_of_le (mul_pos (div_pos (exponentPos hε) (by norm_num)) (exp_pos _))
    c.axial_height_lower

/-- The exact axial and transverse parts of the first-box height allowance. -/
theorem width_height_add_transverse (hε : 0 < ε) :
    c.width * AbcTwoNinths.Basic.rationalHeight c.source + ((dimension ε : ℝ) + 1) * c.transverseBudget =
    (1 - exponent ε / 5) * (c.depth : ℝ) * log (c.prime : ℝ) := by
  have hh := (c.height_pos hε).ne'
  have hk : (0 : ℝ) < depthParameter ε := by exact_mod_cast depthParameterPos hε
  have hd : 0 < (dimension ε : ℝ) + 1 := by positivity
  unfold width transverseBudget
  field_simp
  ring

/-- Both geometric widths are positive at a contact of positive depth. -/
theorem transverseBudget_width_pos (hε : 0 < ε) (hn : 0 < c.depth) :
    0 < c.transverseBudget ∧ 0 < c.width := by
  have he := (exponentBounds hε).2.2
  have he' : 0 < 1 - exponent ε / 5 := by linarith
  have hl : 0 < log (c.prime : ℝ) := Real.log_pos (by exact_mod_cast c.prime_isPrime.one_lt)
  have hk : 0 < (depthParameter ε : ℝ) := by exact_mod_cast depthParameterPos hε
  have hh := c.height_pos hε
  have hA : 0 < c.transverseBudget := by unfold transverseBudget; positivity
  exact ⟨hA, by unfold width; positivity⟩

/-- The two row-block degree caps give the degree prescribed for the polynomial. -/
theorem rowDegree_sum_le (hε : 0 < ε) :
    (c.depth - 1) + (⌈degreeMargin ε * c.depth⌉₊ - 1) ≤ c.degree := by
  have hm : 0 ≤ degreeMargin ε * c.depth :=
    mul_nonneg (le_of_lt (div_pos (exponentPos hε) (by norm_num : (0 : ℝ) < 10)))
      (Nat.cast_nonneg _)
  unfold degree
  rw [add_mul, one_mul, add_comm (c.depth : ℝ), Nat.ceil_add_natCast hm]
  omega

/-- The strict local lower estimate and the archimedean upper estimate are incompatible. -/
theorem determinant_budget_contradiction {K L Δ δ : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hlower : K * (1 - degreeMargin ε) * L < Δ)
    (hupper : Δ ≤ K * (1 - exponent ε / 5 + δ) * L)
    (hδ : δ < exponent ε / 10) : False := by
  have hm : 1 - exponent ε / 5 + δ < 1 - degreeMargin ε := by
    unfold degreeMargin
    linarith
  exact (not_lt_of_ge (hlower.trans_le hupper).le) (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hm hK) hL)

end AbcSubexp.Contact
