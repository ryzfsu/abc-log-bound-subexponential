/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.CommonIndexLift
public import AbcTwoNinths.Basic.TripleAndHeight
public import Mathlib.Algebra.Order.Round

/-!
# Axial normalization of the transverse generators

Rounding each roof slope in Section 5 preserves the principal units, every
transverse projection, and the height separation of the full auxiliary lattice.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting


/-- Signed axial exponent that puts the roof slope within one half of zero. -/
noncomputable def roofCorrection (roof : ℕ) (axis u : ℚ) : ℤ :=
  -round ((padicValRat roof u : ℝ) / (padicValRat roof axis : ℝ))

/-- Transverse generator with its roof coordinate reduced along the axis. -/
noncomputable def normalizedGenerator (roof : ℕ) (axis u : ℚ) : ℚ :=
  u * axis ^ roofCorrection roof axis u

private theorem congruent_one {p : ℕ} {u : ℚ} (hu : AbcTwoNinths.Basic.RatPrincipalUnit p u) :
    AbcTwoNinths.Basic.RatCongruent p 1 u 1 :=
  hu.2.2.imp id (by intro h; norm_num; omega)

/-- The roof correction stays in the rational principal units. -/
theorem normalizedGeneratorPrincipal {p : ℕ} [Fact p.Prime] (roof : ℕ)
    {axis u : ℚ} (ha : AbcTwoNinths.Basic.RatPrincipalUnit p axis) (hu : AbcTwoNinths.Basic.RatPrincipalUnit p u) :
    AbcTwoNinths.Basic.RatPrincipalUnit p (normalizedGenerator roof axis u) := by
  let k := roofCorrection roof axis u
  have haks := AbcTwoNinths.Basic.congrZpow (congruent_one ha) ha.1 one_ne_zero
    ha.2.1 (padicValRat.one) k
  have hak : AbcTwoNinths.Basic.RatCongruent p 1 (axis ^ k) 1 := by simpa using haks
  have hh := AbcTwoNinths.Basic.congrMul (congruent_one hu) hak hu.2.1.symm.le
    (show AbcTwoNinths.Basic.IntegralAt p 1 by simp [AbcTwoNinths.Basic.IntegralAt])
  change AbcTwoNinths.Basic.RatPrincipalUnit p (u * axis ^ k)
  refine ⟨mul_ne_zero hu.1 (zpow_ne_zero _ ha.1), ?_, ?_⟩
  · rw [padicValRat.mul hu.1 (zpow_ne_zero _ ha.1), padicValRat.zpow, ha.2.1, hu.2.1]
    simp
  · have hh' : AbcTwoNinths.Basic.RatCongruent p 1 (u * axis ^ k) 1 := by simpa using hh
    exact hh'.imp id (by intro h; norm_num at h; omega)

/-- Valuations shift by the same axial multiple at every prime. -/
theorem normalizedGeneratorValuation (roof p : ℕ) [Fact p.Prime] {axis u : ℚ}
    (ha : axis ≠ 0) (hu : u ≠ 0) :
    padicValRat p (normalizedGenerator roof axis u) =
      padicValRat p u + roofCorrection roof axis u * padicValRat p axis := by
  rw [normalizedGenerator, padicValRat.mul hu (zpow_ne_zero _ ha), padicValRat.zpow]

/-- The normalized roof slope is bounded in absolute value by one half. -/
theorem normalizedGeneratorRoof (roof : ℕ) [Fact roof.Prime] {axis u : ℚ}
    (ha : axis ≠ 0) (hu : u ≠ 0) (hn : padicValRat roof axis ≠ 0) :
    |(padicValRat roof (normalizedGenerator roof axis u) : ℝ) / (padicValRat roof axis : ℝ)| ≤ 1 / 2 := by
  rw [normalizedGeneratorValuation roof roof ha hu, Int.cast_add, Int.cast_mul, add_div,
    mul_div_cancel_right₀ _ (by exact_mod_cast hn), roofCorrection, Int.cast_neg, ← sub_eq_add_neg]
  exact abs_sub_round _

/-- Removing the axial roof component gives identical projected coordinates
before and after normalization. -/
theorem normalizedGeneratorTransverse (roof p : ℕ) [Fact roof.Prime] [Fact p.Prime]
    {axis u : ℚ} (ha : axis ≠ 0) (hu : u ≠ 0) (hn : padicValRat roof axis ≠ 0) :
    (padicValRat p (normalizedGenerator roof axis u) : ℝ) -
      ((padicValRat roof (normalizedGenerator roof axis u) : ℝ) / (padicValRat roof axis : ℝ)) *
        (padicValRat p axis : ℝ) =
    (padicValRat p u : ℝ) - ((padicValRat roof u : ℝ) / (padicValRat roof axis : ℝ)) *
      (padicValRat p axis : ℝ) := by
  rw [normalizedGeneratorValuation roof p ha hu, normalizedGeneratorValuation roof roof ha hu]
  push_cast
  field_simp [show (padicValRat roof axis : ℝ) ≠ 0 by exact_mod_cast hn]
  ring

/-- Every nonzero coefficient vector still exceeds the same height floor after
independent axial corrections to the transverse generators. -/
theorem normalizedGeneratorHeightSeparation {I : Type*} [Fintype I] (roof : ℕ)
    {axis : ℚ} (ha : axis ≠ 0) (u : I → ℚ) {Y : ℝ}
    (hsep : ∀ (a : ℤ) (y : I → ℤ), (a, y) ≠ 0 →
      Y < AbcTwoNinths.Basic.rationalHeight (axis ^ a * ∏ i, u i ^ y i)) :
    ∀ (a : ℤ) (y : I → ℤ), (a, y) ≠ 0 →
      Y < AbcTwoNinths.Basic.rationalHeight (axis ^ a * ∏ i, normalizedGenerator roof axis (u i) ^ y i) := by
  classical
  intro a y hne
  let b (i : I) := roofCorrection roof axis (u i) * y i
  have hpow (s : Finset I) : (∏ i ∈ s, axis ^ b i) = axis ^ (∑ i ∈ s, b i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]
  have hb : (a + ∑ i, b i, y) ≠ 0 := by
    intro he
    have hy : y = 0 := congrArg Prod.snd he
    apply hne
    subst y
    simpa [b] using he
  have he : axis ^ a * ∏ i, normalizedGenerator roof axis (u i) ^ y i =
      axis ^ (a + ∑ i, b i) * ∏ i, u i ^ y i := by
    simp only [normalizedGenerator, mul_zpow, ← zpow_mul, Finset.prod_mul_distrib]
    rw [hpow Finset.univ, zpow_add₀ ha]
    ring
  rw [he]
  exact hsep _ y hb

end AbcSubexp.TupleCounting
