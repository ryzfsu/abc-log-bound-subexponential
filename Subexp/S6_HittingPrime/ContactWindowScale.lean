/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The size of the prime window

The contact depth bounds control the height and the logarithm of the
upper endpoint in the Chebyshev interval for the interpolation prime.

## Main results
* `AbcSubexp.Contact.hittingWindow_scale`
-/

@[expose] public section

open Real
open AbcSubexp.Parameters

namespace AbcSubexp.Contact

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}

/-- The upper endpoint for choosing the prime in the multiplicative interval. -/
noncomputable def hittingWindowEnd (c : Contact ε t) : ℕ :=
  ⌈3 * (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1)⌉₊

private theorem degree_bounds (hε : 0 < ε) (c : Contact ε t) :
    c.depth ≤ c.degree ∧ c.degree ≤ 2 * c.depth := by
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hem : exponent ε ≤ 1 / 10 := min_le_right _ _
  have hmar : 0 < degreeMargin ε := by unfold degreeMargin; positivity
  have hmar' : degreeMargin ε ≤ 1 := by unfold degreeMargin; linarith
  unfold Contact.degree
  by_cases hn : c.depth = 0
  · simp [hn]
  have hn' : 0 < (c.depth : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlow : c.depth < ⌈(1 + degreeMargin ε) * (c.depth : ℝ)⌉₊ := by
    apply Nat.lt_ceil.mpr
    nlinarith [mul_pos hmar hn']
  have hupp : ⌈(1 + degreeMargin ε) * (c.depth : ℝ)⌉₊ ≤ 2 * c.depth := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hmar') hn'.le]
  omega

/-- The actual window satisfies the two scale bounds used in the estimate
for the indices that miss every list. The constants are uniform in the triple. -/
theorem hittingWindow_scale (hε : 0 < ε) (c : Contact ε t) (hx : log 13 ≤ t.thirdLogRadical) :
    AbcTwoNinths.Basic.rationalHeight c.source ≤
      (((depthParameter ε : ℝ) + 1) / (2 * exponent ε)) * c.hittingWindowEnd * t.thirdLogRadical ∧
    log (c.hittingWindowEnd : ℝ) ≤ 2 * t.thirdLogRadical := by
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hx0 : 0 ≤ t.thirdLogRadical := (log_nonneg (by norm_num : (1 : ℝ) ≤ 13)).trans hx
  have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  have hd := degree_bounds hε c
  have hD : (c.depth : ℝ) ≤ c.degree := by exact_mod_cast hd.1
  have hD' : (c.degree : ℝ) ≤ 2 * c.depth := by exact_mod_cast hd.2
  have hp : 1 ≤ log (c.prime : ℝ) := by
    have hp' : (5 : ℝ) < c.prime := by exact_mod_cast c.prime_gt_five
    apply (le_log_iff_exp_le (by positivity)).mpr
    linarith [exp_one_lt_three]
  have hlog2 := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have hn : (c.depth : ℝ) ≤ exp t.thirdLogRadical + 1 := calc
    _ ≤ (c.depth : ℝ) * log c.prime := le_mul_of_one_le_right (by positivity) hp
    _ ≤ AbcTwoNinths.Basic.rationalHeight c.source + log 2 := c.depth_share_upper
    _ ≤ exp t.thirdLogRadical + 1 := by linarith [c.axial_height_upper, c.height_cap]
  have hscale := Nat.le_ceil (3 * (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1))
  change _ ≤ (c.hittingWindowEnd : ℝ) at hscale
  have hdepth : (c.depth : ℝ) ≤ c.hittingWindowEnd * ((depthParameter ε : ℝ) + 1) := by
    have := (div_le_iff₀ hk).mp hscale
    linarith
  constructor
  · have hh : 2 * exponent ε * AbcTwoNinths.Basic.rationalHeight c.source ≤
        (c.hittingWindowEnd * ((depthParameter ε : ℝ) + 1)) * t.thirdLogRadical := calc
      _ ≤ (c.depth : ℝ) * log c.prime := c.depth_share.le
      _ ≤ _ := by gcongr; exact c.log_upper
    calc
      _ ≤ ((c.hittingWindowEnd * ((depthParameter ε : ℝ) + 1)) * t.thirdLogRadical) /
          (2 * exponent ε) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      _ = _ := by ring
  · have hceil := Nat.ceil_lt_add_one
      (by positivity : 0 ≤ 3 * (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1))
    change (c.hittingWindowEnd : ℝ) < _ at hceil
    have hdiv : 3 * (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1) ≤ 3 * c.degree :=
      div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) (depthParameter ε)])
    have hX : (c.hittingWindowEnd : ℝ) ≤ 13 * exp t.thirdLogRadical := by
      linarith [one_le_exp hx0]
    by_cases hz : c.hittingWindowEnd = 0
    · simp [hz, hx0]
    have hXpos : 0 < (c.hittingWindowEnd : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    calc
      _ ≤ log (13 * exp t.thirdLogRadical) := log_le_log hXpos hX
      _ = log 13 + t.thirdLogRadical := by rw [log_mul (by norm_num) (exp_ne_zero _), log_exp]
      _ ≤ _ := by linarith

/-- Every fixed lower cutoff for the prime window holds uniformly on the
large-`x` tail, by the quadratic term of the contact height lower bound. -/
theorem eventually_hittingWindowEnd_ge (hε : 0 < ε) (N : ℕ) :
    ∃ x₀ : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), x₀ ≤ t.thirdLogRadical → N ≤ c.hittingWindowEnd := by
  let e := exponent ε
  let A := ((depthParameter ε : ℝ) + 1) / (2 * e)
  let b := e * (3 * e)^2 / 4
  have he : 0 < e := lt_min hε (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨max (log 13) (A * N / b), ?_⟩
  intro t c hx
  have hx' := le_trans (le_max_left _ _) hx
  have hxpos : 0 < t.thirdLogRadical := (log_pos (by norm_num : (1 : ℝ) < 13)).trans_le hx'
  have hN : A * N ≤ b * t.thirdLogRadical := by
    have := (div_le_iff₀ hb).mp (le_trans (le_max_right _ _) hx)
    linarith
  have hquad := pow_div_factorial_le_exp (3 * e * t.thirdLogRadical) (by positivity) 2
  norm_num at hquad
  have hh : b * t.thirdLogRadical^2 ≤ AbcTwoNinths.Basic.rationalHeight c.source := by
    apply le_trans _ c.axial_height_lower
    change _ ≤ e / 2 * exp (3 * e * t.thirdLogRadical)
    dsimp [b]
    nlinarith only [mul_le_mul_of_nonneg_left hquad he.le]
  have hupper := (hittingWindow_scale hε c hx').1
  change _ ≤ A * c.hittingWindowEnd * t.thirdLogRadical at hupper
  have hdiv : b * t.thirdLogRadical ≤ A * c.hittingWindowEnd := by
    apply (mul_le_mul_iff_left₀ hxpos).mp
    nlinarith only [hh.trans hupper]
  exact_mod_cast (mul_le_mul_iff_right₀ hA).mp (hN.trans hdiv)

/-- Every integer in a sufficiently large third window obeys the lower
degree cutoff and the strict square bound needed by the Lucas step. -/
theorem hittingWindow_degree_bounds (c : Contact ε t) {q : ℕ}
    (hsize : 3 * (depthParameter ε + 2) ≤ c.hittingWindowEnd)
    (hthird : c.hittingWindowEnd < 3 * q) :
    (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1) < q ∧
      depthParameter ε + 1 < q ∧ c.degree + q < q^2 := by
  have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  have hceil := Nat.le_ceil (3 * (c.degree : ℝ) / ((depthParameter ε : ℝ) + 1))
  change _ ≤ (c.hittingWindowEnd : ℝ) at hceil
  have hr : (c.hittingWindowEnd : ℝ) < 3 * q := by exact_mod_cast hthird
  have hd : (c.degree : ℝ) < q * ((depthParameter ε : ℝ) + 1) := by
    have := (div_le_iff₀ hk).mp hceil
    nlinarith only [this, mul_lt_mul_of_pos_right hr hk]
  have hn : c.degree < q * (depthParameter ε + 1) := by exact_mod_cast hd
  have hq : depthParameter ε + 2 ≤ q := by omega
  refine ⟨(div_lt_iff₀ hk).mpr hd, by omega, ?_⟩
  calc
    c.degree + q < q * (depthParameter ε + 1) + q := by omega
    _ = q * (depthParameter ε + 2) := by ring
    _ ≤ q^2 := by simpa only [pow_two] using Nat.mul_le_mul_left q hq

end AbcSubexp.Contact
