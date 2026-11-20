/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Basic.SignedPrincipalUnitEstimate

/-!
# Zero-coordinate exclusion

A height product bound forces both coordinates of a primitive exponent pair to be nonzero.
-/

@[expose] public section

namespace AbcSubexp.Prerequisites

open AbcTwoNinths.Basic (rationalHeight heightInv)

/-- If one coordinate of a primitive exponent pair vanishes, the height of `z` equals
the height of the remaining base. Since both base heights are at least `D`, the product
bound `L₁ * L₂ ≤ 2 * h * t` contradicts `2 * t < D` when `h` is positive. -/
theorem exclude_zero_coordinate {u v z : ℚ} {c d : ℤ} {h L₁ L₂ t D : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hz : z = u ^ c * v ^ d) (hgcd : Int.gcd c d = 1)
    (hzero : c = 0 ∨ d = 0) (hh : 0 < h)
    (hhz : rationalHeight z = h) (h₁ : rationalHeight u = L₁) (h₂ : rationalHeight v = L₂)
    (hf₁ : D ≤ L₁) (hf₂ : D ≤ L₂) (hprod : L₁ * L₂ ≤ 2 * h * t) (ht : 2 * t < D) : False := by
  have heightOfUnitExponent (a : ℚ) (ha : a ≠ 0) (k : ℤ) (hk : k.natAbs = 1) :
      rationalHeight (a ^ k) = rationalHeight a := by
    rcases Int.natAbs_eq_iff.mp hk with he | he
    · simp [he]
    · simpa [he] using heightInv ha
  rcases hzero with rfl | rfl
  · have hvHeight := heightOfUnitExponent v hv d (by simpa using hgcd)
    rw [hz, zpow_zero, one_mul, hvHeight, h₂] at hhz
    subst L₂
    nlinarith [mul_le_mul_of_nonneg_right hf₁ hh.le, mul_pos hh (sub_pos.mpr ht)]
  · have huHeight := heightOfUnitExponent u hu c (by simpa using hgcd)
    rw [hz, zpow_zero, mul_one, huHeight, h₁] at hhz
    subst L₁
    nlinarith [mul_le_mul_of_nonneg_left hf₂ hh.le, mul_pos hh (sub_pos.mpr ht)]

end AbcSubexp.Prerequisites
