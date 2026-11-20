/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The auxiliary-prime cutoff

The selected-prime and primitive-height bounds imply the logarithmic cutoff
inequalities in equation (4.1).

## Main results

* `AbcSubexp.TupleCounting.auxiliaryPrimeCutoffBounds`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

/-- The cutoff for the auxiliary prime interval of Section 4. -/
noncomputable def auxiliaryPrimeCutoff (e x p h : ℝ) : ℝ :=
  Real.exp ((e ^ 2 / 10) * x) * max (p ^ (1 / 2 : ℝ)) (p / h)

/-- The cutoff bounds corresponding to equation (4.1), with onset `20 ≤ e ^ 2 * x`. -/
theorem auxiliaryPrimeCutoffBounds {e x p h : ℝ} (he : 0 < e) (heCap : e ≤ 1 / 10)
    (hp : 0 < p) (hOnset : 20 ≤ e ^ 2 * x)
    (hContact : (2.94 * e) * x < Real.log p) (hContactUpper : Real.log p ≤ x)
    (hHeight : (e / 2) * Real.exp (3 * e * x) ≤ h) :
    let M := auxiliaryPrimeCutoff e x p h
    let t := Real.log M
    let ℓ := Real.log p
    1 / 2 ≤ t / ℓ ∧
      t / ℓ ≤ max (1 / 2 + e / 29.4) (1 - 3 * e + e ^ 2 / 10 + Real.log (2 / e) / x) ∧
      max (1 / 2 + e / 29.4) (1 - 3 * e + e ^ 2 / 10 + Real.log (2 / e) / x) <
        1 - 2.8 * e ∧
      (e ^ 2 / 10) * x ≤ t ∧ t ≤ x ∧ M < p / 2 := by
  let ℓ := Real.log p
  have hx : 0 < x := by
    by_contra! hx
    have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg e) hx
    linarith
  have hℓ : 0 < ℓ := lt_trans (by positivity) hContact
  have hh : 0 < h := lt_of_lt_of_le (by positivity) hHeight
  have hHalfPower : 0 < p ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp _
  have hQuotient : 0 < p / h := div_pos hp hh
  have hCutoff : 0 < auxiliaryPrimeCutoff e x p h :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le hHalfPower (le_max_left _ _))
  have hLogCutoff :
      Real.log (auxiliaryPrimeCutoff e x p h) =
        (e ^ 2 / 10) * x + max (ℓ / 2) (ℓ - Real.log h) := by
    unfold auxiliaryPrimeCutoff
    rw [Real.log_mul (Real.exp_pos _).ne' (lt_of_lt_of_le hHalfPower (le_max_left _ _)).ne',
      Real.log_exp]
    rw [Real.strictMonoOn_log.monotoneOn.map_max hHalfPower hQuotient,
      Real.log_rpow hp, Real.log_div hp.ne' hh.ne']
    have hHalf : (1 / 2 : ℝ) * Real.log p = ℓ / 2 := by
      dsimp [ℓ]
      ring
    rw [hHalf]
  have hLogHeight : 3 * e * x - Real.log (2 / e) ≤ Real.log h := by
    have hLogLower := (Real.log_le_log_iff (by positivity) hh).2 hHeight
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div he.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hLogLower
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) he.ne']
    linarith
  have hOnsetLog : Real.log (2 / e) / x ≤ e / 10 := by
    apply (div_le_iff₀ hx).2
    calc
      Real.log (2 / e) ≤ 2 / e - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 2 / e := by linarith
      _ ≤ e / 10 * x := (div_le_iff₀ he).2 (by nlinarith only [hOnset])
  have hOffset := mul_le_mul_of_nonneg_left heCap he.le
  have hLoss : 0 < 3 * e - e ^ 2 / 10 - Real.log (2 / e) / x := by
    nlinarith only [hOnsetLog, hOffset, he]
  let B := max (1 / 2 + e / 29.4) (1 - 3 * e + e ^ 2 / 10 + Real.log (2 / e) / x)
  have hBound : B < 1 - 2.8 * e := by
    apply max_lt
    · rw [show (29.4 : ℝ) = 147 / 5 by norm_num, show (2.8 : ℝ) = 14 / 5 by norm_num]
      linarith only [heCap]
    · nlinarith only [hOnsetLog, hOffset, he]
  have hSquareRootBranch : (e ^ 2 / 10) * x + ℓ / 2 ≤ (1 / 2 + e / 29.4) * ℓ := by
    have hScale := mul_le_mul_of_nonneg_left hContact.le (show 0 ≤ e / 29.4 by positivity)
    change e / 29.4 * ((2.94 * e) * x) ≤ e / 29.4 * ℓ at hScale
    rw [show (29.4 : ℝ) = 147 / 5 by norm_num] at hScale ⊢
    rw [show (2.94 : ℝ) = 147 / 50 by norm_num] at hScale
    nlinarith only [hScale]
  have hHeightBranch :
      (e ^ 2 / 10) * x + (ℓ - Real.log h) ≤
        (1 - 3 * e + e ^ 2 / 10 + Real.log (2 / e) / x) * ℓ := by
    have hScale := mul_le_mul_of_nonneg_left hContactUpper hLoss.le
    have hCancel : (Real.log (2 / e) / x) * x = Real.log (2 / e) :=
      div_mul_cancel₀ _ hx.ne'
    linarith only [hLogHeight, hScale, hCancel]
  have hLogUpper : Real.log (auxiliaryPrimeCutoff e x p h) / ℓ ≤ B := by
    apply (div_le_iff₀ hℓ).2
    rw [hLogCutoff, add_max]
    exact max_le
      (hSquareRootBranch.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hℓ.le))
      (hHeightBranch.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hℓ.le))
  have hSlack : Real.log 2 ≤ (2.8 * e) * ℓ := by
    have hScale := mul_le_mul_of_nonneg_left hContact.le (show 0 ≤ 2.8 * e by positivity)
    have hLogTwo := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    nlinarith only [hScale, hOnset, hLogTwo]
  have hLogStrict : Real.log (auxiliaryPrimeCutoff e x p h) < (1 - 2.8 * e) * ℓ :=
    (div_lt_iff₀ hℓ).1 (hLogUpper.trans_lt hBound)
  change 1 / 2 ≤ Real.log (auxiliaryPrimeCutoff e x p h) / ℓ ∧
    Real.log (auxiliaryPrimeCutoff e x p h) / ℓ ≤ B ∧ B < 1 - 2.8 * e ∧
    (e ^ 2 / 10) * x ≤ Real.log (auxiliaryPrimeCutoff e x p h) ∧
    Real.log (auxiliaryPrimeCutoff e x p h) ≤ x ∧ auxiliaryPrimeCutoff e x p h < p / 2
  refine ⟨?_, hLogUpper, hBound, ?_, ?_, ?_⟩
  · have hBranch : ℓ / 2 ≤ max (ℓ / 2) (ℓ - Real.log h) := le_max_left _ _
    have hGrowth : 0 ≤ (e ^ 2 / 10) * x := by positivity
    apply (le_div_iff₀ hℓ).2
    rw [hLogCutoff]
    linarith only [hBranch, hGrowth]
  · rw [hLogCutoff]
    have hBranch : ℓ / 2 ≤ max (ℓ / 2) (ℓ - Real.log h) := le_max_left _ _
    linarith only [hBranch, hℓ]
  · have hDecrease : (1 - 2.8 * e) * ℓ ≤ ℓ := by
      have : 0 ≤ (2.8 * e) * ℓ := by positivity
      linarith only [this]
    exact hLogStrict.le.trans (hDecrease.trans hContactUpper)
  · have hLogHalf : Real.log (p / 2) = ℓ - Real.log 2 :=
      Real.log_div hp.ne' (by norm_num)
    apply (Real.log_lt_log_iff hCutoff (by positivity)).1
    rw [hLogHalf]
    linarith only [hLogStrict, hSlack]

end AbcSubexp.TupleCounting
