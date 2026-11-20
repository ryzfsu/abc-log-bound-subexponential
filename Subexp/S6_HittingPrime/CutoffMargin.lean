/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-! # The logarithmic cutoff margin for the native sphere radius -/

@[expose] public section

noncomputable section

open Real
open AbcSubexp.Parameters

namespace AbcSubexp.Contact

/-- Both branches of the auxiliary cutoff leave a margin of at least
`14 * e / 5` of the logarithm of the contact prime on the fixed-exponent tail. -/
theorem eventually_log_cutoff_margin {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t), X ≤ t.thirdLogRadical →
      0 < log c.cutoff ∧
      log c.cutoff ≤ (1 - 14 * exponent ε / 5) * log (c.prime : ℝ) := by
  let e := exponent ε
  have he : 0 < e := lt_min hε (by norm_num)
  have hele : e ≤ 1 / 10 := min_le_right _ _
  refine ⟨max 1 (-(10 * log (e / 2)) / e), ?_⟩
  intro t c hx
  have hxpos : 0 < t.thirdLogRadical := by linarith [le_trans (le_max_left _ _) hx]
  have hoff := (div_le_iff₀ he).mp ((le_max_right _ _).trans hx)
  have hp : (0 : ℝ) < c.prime := by exact_mod_cast c.prime_isPrime.pos
  have hpone : (1 : ℝ) < c.prime := by exact_mod_cast c.prime_isPrime.one_lt
  let l := log (c.prime : ℝ)
  let h := AbcTwoNinths.Basic.rationalHeight c.source
  have hl : 0 < l := log_pos hpone
  have he2 : 0 < e / 2 := by positivity
  have hlow : (e / 2) * exp (3 * e * t.thirdLogRadical) ≤ h := c.axial_height_lower
  have hh : 0 < h := lt_of_lt_of_le (by positivity) hlow
  have hlog := Real.log_le_log (mul_pos he2 (exp_pos _)) hlow
  rw [log_mul he2.ne' (exp_ne_zero _), log_exp] at hlog
  have hell : l ≤ t.thirdLogRadical := c.log_upper
  have hcontact : (3 - 6 / 100) * e * t.thirdLogRadical < l := c.log_lower
  have hsmall : auxiliaryRate ε * t.thirdLogRadical ≤ e * l / 20 := by
    change e ^ 2 / 10 * t.thirdLogRadical ≤ e * l / 20
    nlinarith [mul_pos he hxpos, mul_pos he (sub_pos.mpr hcontact),
      mul_pos he (mul_pos he hxpos)]
  have hheight : (29 / 10) * e * l ≤ log h := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hell)]
  have hroot : auxiliaryRate ε * t.thirdLogRadical + l / 2 ≤ (1 - 14 * e / 5) * l := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hele) hl.le]
  have hratio : auxiliaryRate ε * t.thirdLogRadical + (l - log h) ≤ (1 - 14 * e / 5) * l := by
    nlinarith [mul_pos he hl]
  have hs : 0 < √(c.prime : ℝ) := Real.sqrt_pos_of_pos hp
  have hmax : 0 < max (√(c.prime : ℝ)) ((c.prime : ℝ) / h) := hs.trans_le (le_max_left ..)
  unfold Contact.cutoff
  change 0 < log (exp (auxiliaryRate ε * t.thirdLogRadical) * max (√(c.prime : ℝ)) ((c.prime : ℝ) / h)) ∧ _
  rw [log_mul (exp_ne_zero _) hmax.ne', log_exp]
  have auxpos : 0 < auxiliaryRate ε * t.thirdLogRadical := by change 0 < e ^ 2 / 10 * t.thirdLogRadical; positivity
  have hlogs : log (√(c.prime : ℝ)) = l / 2 := log_sqrt hp.le
  constructor
  · have hmono := log_le_log hs (le_max_left (√(c.prime : ℝ)) ((c.prime : ℝ) / h))
    linarith
  · rcases le_total ((c.prime : ℝ) / h) (√(c.prime : ℝ)) with hcase | hcase
    · rw [max_eq_left hcase, hlogs]
      exact hroot
    · rw [max_eq_right hcase, log_div hp.ne' hh.ne']
      exact hratio

end AbcSubexp.Contact
