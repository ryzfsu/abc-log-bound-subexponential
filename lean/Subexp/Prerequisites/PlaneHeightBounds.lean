/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.BadPairCount

/-!
# Plane height bounds

The signed monomial height is invariant under negation and homogeneous under
integer scaling. A plane height bound controls each roof coordinate, and the
native area estimate bounds the product of two basis heights. Primitivity in
the signed residue kernel gives an integral axial coefficient.
-/

@[expose] public section

namespace AbcSubexp.Prerequisites

open AbcTwoNinths.Diamond (Pair height quotientLabel side)
open AbcTwoNinths.ExteriorE2 (Exponents reduction)
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The larger logarithmic sum after adjoining the prime pair with opposite exponents. -/
noncomputable def planeHeight (q : ι → ℕ) (s : Pair) (w : ι → ℤ) (b : ℤ) : ℝ :=
  max (side q w + max (b : ℝ) 0 * Real.log s.val.1 + max (-(b : ℝ)) 0 * Real.log s.val.2)
    (side q (-w) + max (-(b : ℝ)) 0 * Real.log s.val.1 + max (b : ℝ) 0 * Real.log s.val.2)

private theorem side_smul_of_nonneg (q : ι → ℕ) (w : ι → ℤ) {a : ℤ} (ha : 0 ≤ a) :
    side q (a • w) = (a : ℝ) * side q w := by
  unfold side
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change max (((a * w i : ℤ) : ℝ)) 0 * _ = _
  have he : max ((a : ℝ) * (w i : ℝ)) 0 = (a : ℝ) * max (w i : ℝ) 0 := by
    simpa only [mul_zero] using
      (mul_max_of_nonneg (w i : ℝ) 0 (show 0 ≤ (a : ℝ) by exact_mod_cast ha)).symm
  rw [Int.cast_mul, he, mul_assoc]

/-- Reversing every exponent preserves the monomial height. -/
theorem height_neg (q : ι → ℕ) (w : ι → ℤ) :
    height q (-w) = height q w := by
  simp [height, max_comm]

/-- Integer scaling multiplies the monomial height by the absolute value of the scalar. -/
theorem height_smul (q : ι → ℕ) (w : ι → ℤ) (a : ℤ) :
    height q (a • w) = |(a : ℝ)| * height q w := by
  have hscale (a : ℤ) (ha : 0 ≤ a) : height q (a • w) = (a : ℝ) * height q w := by
    simp only [height, ← smul_neg, side_smul_of_nonneg q _ ha]
    rw [mul_max_of_nonneg _ _ (by exact_mod_cast ha)]
  by_cases ha : 0 ≤ a
  · rw [hscale a ha, abs_of_nonneg (by exact_mod_cast ha)]
  · have hna : 0 ≤ -a := by omega
    have hneg : (a • w) = -((-a) • w) := by simp
    rw [hneg, height_neg, hscale (-a) hna, Int.cast_neg,
      abs_of_neg (by exact_mod_cast (lt_of_not_ge ha))]

/-- With zero exponent on the prime pair, the plane height is the monomial height. -/
theorem planeHeight_zero (q : ι → ℕ) (s : Pair) (w : ι → ℤ) :
    planeHeight q s w 0 = height q w := by
  simp [planeHeight, height]

/-- A plane height bound confines the chosen roof coordinate to an integer interval. -/
theorem roof_bound (q : ι → ℕ) (hp : ∀ i, (q i).Prime) (roof : ι)
    (s : Pair) (w : ι → ℤ) (b : ℤ) (Y : ℝ) (hY : planeHeight q s w b ≤ Y) :
    w roof ∈ Finset.Icc (-(⌊Y / Real.log 2⌋₊ : ℤ)) ⌊Y / Real.log 2⌋₊ := by
  classical
  have nonneg (i : ι) : 0 ≤ Real.log (q i) :=
    Real.log_nonneg (by exact_mod_cast (hp i).one_lt.le)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2q : Real.log 2 ≤ Real.log (q roof) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (hp roof).two_le)
  have hnum := (le_max_left _ _).trans hY
  have hden := (le_max_right _ _).trans hY
  change side q w + _ + _ ≤ Y at hnum
  change side q (-w) + _ + _ ≤ Y at hden
  have hq₁ : 0 ≤ Real.log (s.val.1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast s.property.1.one_lt.le)
  have hq₂ : 0 ≤ Real.log (s.val.2 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast s.property.2.1.one_lt.le)
  have hs (a : ι → ℤ) (h : side q a ≤ Y) : max (a roof : ℝ) 0 * Real.log 2 ≤ Y := by
    refine (mul_le_mul_of_nonneg_left h2q (le_max_right _ _)).trans ?_
    exact (Finset.single_le_sum
      (f := fun i => max (a i : ℝ) 0 * Real.log (q i))
      (fun i _ => mul_nonneg (le_max_right _ _) (nonneg i)) (Finset.mem_univ roof)).trans h
  have h11 := mul_nonneg (le_max_right (b : ℝ) 0) hq₁
  have h12 := mul_nonneg (le_max_right (-(b : ℝ)) 0) hq₂
  have h21 := mul_nonneg (le_max_right (-(b : ℝ)) 0) hq₁
  have h22 := mul_nonneg (le_max_right (b : ℝ) 0) hq₂
  have h₁ := hs w (by linarith)
  have h₂ := hs (-w) (by linarith)
  have habs : |(w roof : ℝ)| ≤ Y / Real.log 2 := by
    rw [abs_eq_max_neg]
    apply max_le
    · exact (le_div_iff₀ hl2).mpr
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) hl2.le).trans h₁)
    · exact (le_div_iff₀ hl2).mpr
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) hl2.le).trans (by simpa using h₂))
  have hfloor : (w roof).natAbs ≤ ⌊Y / Real.log 2⌋₊ := by
    apply Nat.le_floor
    have he : ((w roof).natAbs : ℝ) = |(w roof : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact he ▸ habs
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- Substitute the native height and weight bounds in the plane area estimate. -/
theorem planeHeightProductLe {HV H W x U Z : ℝ} {Q : ℕ}
    (hQ : 0 < Q) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hV : HV ≤ 2 * H) (hw : W ≤ 3 * x)
    (harea : U * Z ≤ 4 * HV * (W / (Q : ℝ))) :
    U * Z ≤ 24 * H * x / (Q : ℝ) := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  calc
    U * Z ≤ 4 * HV * (W / (Q : ℝ)) := harea
    _ ≤ (4 * (2 * H)) * ((3 * x) / (Q : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num))
        (div_le_div_of_nonneg_right hw hQR.le) (div_nonneg hW hQR.le) (by positivity)
    _ = 24 * H * x / (Q : ℝ) := by ring

/-- A real linear combination with a prescribed integer transverse coefficient. -/
def inRealPlane (v u w : ι → ℤ) (j : ℤ) : Prop :=
  ∃ a : ℝ, ∀ i, (w i : ℝ) = a * (v i : ℝ) + (j : ℝ) * (u i : ℝ)

omit [Fintype ι] in
/-- After subtracting the transverse term, primitivity of the axis in the signed residue kernel
makes the remaining coefficient integral. -/
theorem plane_coefficients {p : ℕ} [Fact p.Prime]
    (r : Exponents ι →* (ZMod p)ˣ) (v u w : ι → ℤ) (j : ℤ)
    (ρ : (ZMod p)ˣ)
    (hprimitive : ∀ w₀ : ι → ℤ, quotientLabel (r (Multiplicative.ofAdd w₀)) = 1 →
      (∃ a : ℝ, ∀ i, (w₀ i : ℝ) = a * (v i : ℝ)) → ∃ a : ℤ, w₀ = a • v)
    (hu : quotientLabel (r (Multiplicative.ofAdd u)) * quotientLabel ρ = 1)
    (hw : quotientLabel (r (Multiplicative.ofAdd w)) * quotientLabel ρ ^ j = 1)
    (hPlane : inRealPlane v u w j) :
    ∃ a : ℤ, w = a • v + j • u := by
  let R := reduction r
  have hprod : R (Multiplicative.ofAdd (j • u)) * quotientLabel ρ ^ j = 1 := by
    have he : Multiplicative.ofAdd (j • u) = (Multiplicative.ofAdd u) ^ j := rfl
    rw [he, map_zpow, ← mul_zpow]
    rw [show R (Multiplicative.ofAdd u) * quotientLabel ρ = 1 from hu, one_zpow]
  have heq : R (Multiplicative.ofAdd w) = R (Multiplicative.ofAdd (j • u)) :=
    mul_right_cancel (hw.trans hprod.symm)
  have hzero : R (Multiplicative.ofAdd (w - j • u)) = 1 := by
    have he : Multiplicative.ofAdd (w - j • u) =
        Multiplicative.ofAdd w / Multiplicative.ofAdd (j • u) := rfl
    rw [he, map_div, heq, div_self']
  obtain ⟨a, ha⟩ := hPlane
  obtain ⟨m, hm⟩ := hprimitive (w - j • u) hzero ⟨a, by
    intro i
    change ((w i - j * u i : ℤ) : ℝ) = a * (v i : ℝ)
    rw [Int.cast_sub, Int.cast_mul, ha i]
    ring⟩
  exact ⟨m, sub_eq_iff_eq_add.mp hm⟩

end AbcSubexp.Prerequisites
