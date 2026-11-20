/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S2_Parameters.Parameters

/-!
# Size of a cyclic colour interval

The chosen dimension puts the consecutive witness colours inside half of the guaranteed
phase window. The coordinatewise error uses one further quarter of that window.
-/

@[expose] public section

namespace AbcSubexp.Parameters

/-- The dimension and slope tolerance satisfy the witness bounds in Section 7. -/
theorem interpolationParameterBounds {ε : ℝ} (hε : 0 < ε) :
    0 < dimension ε ∧
    (((depthParameter ε + 1 : ℕ) : ℝ) / dimension ε ≤ windowWidth ε / 2) ∧
    (((depthParameter ε + 1 : ℕ) : ℝ) * phaseTolerance ε ≤ windowWidth ε / 4) := by
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  have hw : 0 < windowWidth ε := div_pos he hk
  have hdim : 2 * ((depthParameter ε : ℝ) + 1) / windowWidth ε ≤ (dimension ε : ℝ) :=
    Nat.le_ceil _
  have hm : 0 < (dimension ε : ℝ) := (div_pos (mul_pos (by norm_num) hk) hw).trans_le hdim
  refine ⟨by exact_mod_cast hm, ?_, ?_⟩
  · rw [Nat.cast_add_one, div_le_iff₀ hm]
    have := (div_le_iff₀ hw).mp hdim
    linarith [mul_comm (dimension ε : ℝ) (windowWidth ε)]
  · rw [Nat.cast_add_one, phaseTolerance]
    apply le_of_eq
    field_simp

end AbcSubexp.Parameters
