/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.BadPairCount
public import AbcTwoNinths.Paper.S6_Diamond.SelectedPrimeData
public import Subexp.Prerequisites.PlaneHeightBounds

/-!
# Integral coordinates of the auxiliary lattice

In Section 4 the exponents at the fresh primes recover every transverse
coefficient. Primitivity in the old signed residue kernel then recovers the
remaining integral coefficient along the axis.

## Main results
* `AbcSubexp.TupleCounting.integralCoefficientsOfFreshCoordinates`
* `AbcSubexp.TupleCounting.auxiliaryCoordinatesInjective`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting


/-- An integral signed-kernel vector in the real span of the auxiliary tuple
has integral coefficients in its generating basis, in every finite dimension. -/
theorem integralCoefficientsOfFreshCoordinates {I J : Type*} [Fintype J]
    {p : ℕ} [Fact p.Prime] (r : AbcTwoNinths.ExteriorE2.Exponents I →* (ZMod p)ˣ)
    (v : AbcTwoNinths.ExteriorE2.Kernel r) (roof : I) (hroof : v.val.toAdd roof ≠ 0)
    (hprim : ∀ (n : ℕ) (w : AbcTwoNinths.ExteriorE2.Kernel r), 0 < n → v = w ^ n → n = 1)
    (old : J → I → ℤ) (ratio : J → (ZMod p)ˣ)
    (hlift : ∀ j, AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd (old j))) * AbcTwoNinths.Diamond.quotientLabel (ratio j) = 1)
    (w : I → ℤ) (c : J → ℤ)
    (hker : AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd w)) * ∏ j, AbcTwoNinths.Diamond.quotientLabel (ratio j) ^ c j = 1)
    (hspan : ∃ (a : ℝ) (b : J → ℝ), (∀ j, b j = (c j : ℝ)) ∧
      ∀ i, (w i : ℝ) = a * (v.val.toAdd i : ℝ) + ∑ j, b j * (old j i : ℝ)) :
    ∃ a : ℤ, w = a • v.val.toAdd + ∑ j, c j • old j := by
  classical
  let u := ∑ j, c j • old j
  let ρ := ∏ j, ratio j ^ c j
  let L : (ZMod p)ˣ →* AbcTwoNinths.ExteriorE2.Label p := QuotientGroup.mk' (AbcTwoNinths.ExteriorE2.signs p)
  have hρ : AbcTwoNinths.Diamond.quotientLabel ρ = ∏ j, AbcTwoNinths.Diamond.quotientLabel (ratio j) ^ c j := by
    change L (∏ j, ratio j ^ c j) = ∏ j, L (ratio j) ^ c j
    simp only [map_prod, map_zpow]
  have hu : AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd u)) * AbcTwoNinths.Diamond.quotientLabel ρ = 1 := by
    change (L.comp r) (Multiplicative.ofAdd (∑ j, c j • old j)) * _ = 1
    rw [hρ, show Multiplicative.ofAdd (∑ j, c j • old j) =
      ∏ j, (Multiplicative.ofAdd (old j)) ^ c j from rfl, map_prod]
    simp only [map_zpow, ← Finset.prod_mul_distrib, ← mul_zpow]
    exact Finset.prod_eq_one fun j _ => by
      change (AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd (old j))) * AbcTwoNinths.Diamond.quotientLabel (ratio j)) ^ c j = 1
      rw [hlift, one_zpow]
  have hline : ∀ w₀ : I → ℤ, AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd w₀)) = 1 →
      (∃ a : ℝ, ∀ i, (w₀ i : ℝ) = a * (v.val.toAdd i : ℝ)) →
      ∃ a : ℤ, w₀ = a • v.val.toAdd := by
    rintro w₀ hzero ⟨a, ha⟩
    let z : AbcTwoNinths.ExteriorE2.Kernel r := ⟨Multiplicative.ofAdd w₀, hzero⟩
    obtain ⟨k, hk⟩ := AbcTwoNinths.Diamond.lineOfPowerPrimitive (AbcTwoNinths.ExteriorE2.Kernel r) v
      roof hroof hprim z a ha
    exact ⟨k, congrArg (fun t : AbcTwoNinths.ExteriorE2.Kernel r => t.val.toAdd) hk⟩
  have hw : AbcTwoNinths.Diamond.quotientLabel (r (Multiplicative.ofAdd w)) * AbcTwoNinths.Diamond.quotientLabel ρ ^ (1 : ℤ) = 1 := by
    simpa only [zpow_one, hρ] using hker
  obtain ⟨a, b, hb, hold⟩ := hspan
  have hplane : AbcSubexp.Prerequisites.inRealPlane v.val.toAdd u w 1 := by
    refine ⟨a, fun i => ?_⟩
    rw [hold]
    rw [Int.cast_one, one_mul]
    congr 1
    rw [show u i = ∑ j, c j * old j i from Finset.sum_apply i _ _]
    simp only [Int.cast_sum, Int.cast_mul, hb]
  obtain ⟨k, hk⟩ := AbcSubexp.Prerequisites.plane_coefficients r v.val.toAdd u w (1 : ℤ) ρ hline hu hw hplane
  exact ⟨k, by simpa only [one_zsmul] using hk⟩

/-- The non-anchor fresh coordinates distinguish the transverse coefficients,
and the nonzero roof distinguishes the axial coefficient. -/
theorem auxiliaryCoordinatesInjective {I J : Type*} [Fintype J] (v : I → ℤ)
    (roof : I) (hroof : v roof ≠ 0) (old : J → I → ℤ) :
    Function.Injective (fun t : ℤ × (J → ℤ) => (t.1 • v + ∑ j, t.2 j • old j, t.2)) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ heq
  obtain ⟨h, rfl⟩ := Prod.mk.inj heq
  have haxis := add_right_cancel h
  have hcoord := congrFun haxis roof
  change a * v roof = b * v roof at hcoord
  exact Prod.ext (mul_right_cancel₀ hroof hcoord) rfl

end AbcSubexp.TupleCounting
