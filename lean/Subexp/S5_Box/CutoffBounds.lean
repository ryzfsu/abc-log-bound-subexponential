/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-!
# Height and cutoff scales

Uniform estimates on the axial height and the logarithm of the cutoff ensure
that the box and its translation are available in Section 5.

## Main results
* `AbcSubexp.Box.eventualCutoffBounds`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.Box

open Parameters Real

/-- Beyond a threshold depending on the exponent, the logarithmic cutoff dominates
the projection budget and is bounded by the axial height. -/
theorem eventualCutoffBounds (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical →
      1 ≤ AbcTwoNinths.Basic.rationalHeight c.source ∧
      0 < log c.cutoff ∧
      t.thirdLogRadical / log t.thirdLogRadical ≤ log c.cutoff ∧
      log c.cutoff ≤ AbcTwoNinths.Basic.rationalHeight c.source ∧
      0 ≤ c.transverseBudget := by
  let e := exponent ε
  let β := auxiliaryRate ε
  have he : 0 < e := lt_min hε (by norm_num)
  have he' : e ≤ 1 / 10 := min_le_right _ _
  have hβ : 0 < β := by
    change 0 < e ^ 2 / 10
    positivity
  have hβ' : β ≤ 1 := by
    change e ^ 2 / 10 ≤ 1
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr he')]
  refine ⟨max 1 (max (exp (1 / β)) (16 / e ^ 3)), ?_⟩
  intro t c hx
  have hx1 : 1 ≤ t.thirdLogRadical := (le_max_left _ _).trans hx
  have hx' : 0 < t.thirdLogRadical := zero_lt_one.trans_le hx1
  have hxexp : exp (1 / β) ≤ t.thirdLogRadical := (le_max_of_le_right (le_max_left _ _)).trans hx
  have hxpoly : 16 / e ^ 3 ≤ t.thirdLogRadical := (le_max_of_le_right (le_max_right _ _)).trans hx
  have hepoly : 16 ≤ t.thirdLogRadical * e ^ 3 := (div_le_iff₀ (pow_pos he _)).mp hxpoly
  have hlogx : 1 / β ≤ log t.thirdLogRadical := by
    rw [← log_exp (1 / β)]
    exact log_le_log (exp_pos _) hxexp
  have hlogx' : 0 < log t.thirdLogRadical := (div_pos zero_lt_one hβ).trans_le hlogx
  have hxlog : t.thirdLogRadical / log t.thirdLogRadical ≤ β * t.thirdLogRadical := by
    rw [div_le_iff₀ hlogx']
    have H := (div_le_iff₀ hβ).mp hlogx
    calc
      t.thirdLogRadical = t.thirdLogRadical * 1 := (mul_one _).symm
      _ ≤ t.thirdLogRadical * (log t.thirdLogRadical * β) := mul_le_mul_of_nonneg_left H hx'.le
      _ = β * t.thirdLogRadical * log t.thirdLogRadical := by ring
  have hpoly := quadratic_le_exp_of_nonneg (show 0 ≤ 3 * e * t.thirdLogRadical by positivity)
  have hscale : 2 * t.thirdLogRadical ≤ AbcTwoNinths.Basic.rationalHeight c.source := by
    calc
      2 * t.thirdLogRadical ≤ (e / 2) * (1 + 3 * e * t.thirdLogRadical + (3 * e * t.thirdLogRadical) ^ 2 / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hepoly hx'.le,
          mul_nonneg he.le (mul_nonneg he.le hx'.le)]
      _ ≤ (e / 2) * exp (3 * e * t.thirdLogRadical) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ ≤ _ := c.axial_height_lower
  have hh : 1 ≤ AbcTwoNinths.Basic.rationalHeight c.source := by linarith
  let p : ℝ := c.prime
  have hp : 1 ≤ p := by
    change (1 : ℝ) ≤ (c.prime : ℝ)
    exact_mod_cast c.prime_isPrime.one_le
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hs : 1 ≤ sqrt p := by simpa using sqrt_le_sqrt hp
  let r := max (sqrt p) (p / AbcTwoNinths.Basic.rationalHeight c.source)
  have hr : 1 ≤ r := hs.trans (le_max_left _ _)
  have hrp : r ≤ p := by
    apply max_le
    · have hmul := mul_le_mul_of_nonneg_right hs (sqrt_nonneg p)
      rw [one_mul, mul_self_sqrt hp₀.le] at hmul
      exact hmul
    · rw [div_le_iff₀ (zero_lt_one.trans_le hh)]
      exact le_mul_of_one_le_right hp₀.le hh
  have hcut : log c.cutoff = β * t.thirdLogRadical + log r := by
    change log (exp (β * t.thirdLogRadical) * r) = _
    rw [log_mul (exp_pos _).ne' (zero_lt_one.trans_le hr).ne', log_exp]
  have hlogr : 0 ≤ log r := log_nonneg hr
  have hlogr' : log r ≤ t.thirdLogRadical :=
    (log_le_log (zero_lt_one.trans_le hr) hrp).trans c.log_upper
  have hcutLower : β * t.thirdLogRadical ≤ log c.cutoff := by linarith
  have hcutUpper : log c.cutoff ≤ 2 * t.thirdLogRadical := by
    have H := mul_le_mul_of_nonneg_right hβ' hx'.le
    linarith
  have hk : 0 < (depthParameter ε : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (div_pos zero_lt_two he))
  have hslack : 0 ≤ 1 - e / 5 := by linarith
  have hlogp : 0 ≤ log p := log_nonneg hp
  have hbudget : 0 ≤ c.transverseBudget := by
    change 0 ≤ (1 - e / 5) * (c.depth : ℝ) * log p /
      (((dimension ε : ℝ) + 1) * (1 + 1 / (depthParameter ε : ℝ)))
    positivity
  exact ⟨hh, (mul_pos hβ hx').trans_le hcutLower, hxlog.trans hcutLower,
    hcutUpper.trans hscale, hbudget⟩

end AbcSubexp.Box
