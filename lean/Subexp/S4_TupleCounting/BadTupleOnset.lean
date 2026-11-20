/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Onset for auxiliary tuple exclusion

The upper bound for the bad-tuple proportion in the proof of Proposition 4.2
is eventually less than one. The Lean estimate also covers the growing dimension
used to choose the lattice and the interpolation prime together.

## Main results

* `AbcSubexp.TupleCounting.eventuallyBadTupleRatioLtOne`
* `AbcSubexp.TupleCounting.eventuallyFixedBadTupleRatioLtOne`
* `AbcSubexp.TupleCounting.eventuallyGrowingBadTupleRatioLtOne`
* `AbcSubexp.TupleCounting.badTupleCountLtTotal`
-/

@[expose] public section

open Filter
open scoped Topology

namespace AbcSubexp.TupleCounting

/-- The logarithmic volume loss in the Section 4 lower bound for the common family. -/
noncomputable def tupleVolumeLoss (x : ℝ) : ℝ :=
  12 * x * Real.log (3 * Real.log x) / Real.log x

/-- A majorant for the ratio of bad tuples to all distinct tuples. The exponent `z` accounts
for the short-vector cutoff before subtracting the cluster growth rate. -/
noncomputable def badTupleRatio (C rate z x : ℝ) (d : ℕ) : ℝ :=
  C * 8 ^ d * x ^ 2 * (1 + 2 * (x / Real.log x)) *
    Real.exp (z - rate * x + 2 * (x / Real.log x) + tupleVolumeLoss x)

private theorem tendstoLogTripleDiv : Tendsto (fun y : ℝ => Real.log (3 * y) / y) atTop (𝓝 0) := by
  have hConst : Tendsto (fun y : ℝ => Real.log 3 / y) atTop (𝓝 0) :=
    by simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log 3)
  have hLog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hSum : Tendsto (fun y : ℝ => Real.log 3 / y + Real.log y / y) atTop (𝓝 0) := by
    simpa only [add_zero] using hConst.add hLog
  refine hSum.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun y hy => ?_)
  dsimp
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hy.ne', add_div]

private theorem tendstoNormalizedOverhead (C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (3 * C) / x + 3 * (Real.log x / x) +
      2 / Real.log x + 12 * (Real.log (3 * Real.log x) / Real.log x)) atTop (𝓝 0) := by
  have hConst : Tendsto (fun x : ℝ => Real.log (3 * C) / x) atTop (𝓝 0) :=
    by simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log (3 * C))
  have hLog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hInv : Tendsto (fun x : ℝ => 2 / Real.log x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 : ℝ)).comp Real.tendsto_log_atTop
  have hVolume := tendstoLogTripleDiv.comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, mul_zero, add_zero] using
    ((hConst.add (hLog.const_mul 3)).add hInv).add (hVolume.const_mul 12)

private theorem eventuallyBadTupleRatioLtOneOfExponent {C rate : ℝ}
    (hC : 0 < C) (hRate : 0 < rate) :
    ∀ᶠ x in atTop, ∀ (d : ℕ) (z : ℝ), (d : ℝ) * Real.log 8 + z ≤ rate / 2 * x →
      badTupleRatio C rate z x d < 1 := by
  have hSmall := (tendstoNormalizedOverhead C).eventually_lt_const (half_pos hRate)
  filter_upwards [hSmall, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hxSmall hx hLog
  intro d z hExponent
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hLogPos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hLog
  have hu : 0 ≤ x / Real.log x := by positivity
  have huUpper : x / Real.log x ≤ x := (div_le_iff₀ hLogPos).2 (by nlinarith)
  have hFactor : 1 + 2 * (x / Real.log x) ≤ 3 * x := by linarith
  have hFactorLog : Real.log (1 + 2 * (x / Real.log x)) ≤ Real.log 3 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hxPos.ne']
    exact Real.log_le_log (by positivity) hFactor
  have hOverhead :
      Real.log (3 * C) + 3 * Real.log x + 2 * (x / Real.log x) + tupleVolumeLoss x <
        rate / 2 * x := by
    have hMul := mul_lt_mul_of_pos_right hxSmall hxPos
    convert hMul using 1
    unfold tupleVolumeLoss
    field_simp [hxPos.ne', hLogPos.ne']
  have hRatio : 0 < badTupleRatio C rate z x d := by unfold badTupleRatio; positivity
  apply (Real.log_lt_log_iff hRatio one_pos).1
  unfold badTupleRatio
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul hC.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_one]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hC.ne'] at hOverhead
  push_cast
  linarith only [hExponent, hFactorLog, hOverhead]

/-- The upper bound for bad tuples divided by the lower bound for distinct tuples is eventually
less than one at fixed dimension, for every positive exponential saving. -/
theorem eventuallyBadTupleRatioLtOne {C κ : ℝ} (hC : 0 < C) (hκ : 0 < κ) (d : ℕ) :
    ∀ᶠ x in atTop, badTupleRatio C κ 0 x d < 1 := by
  let D : ℝ := (d : ℝ) * Real.log 8
  filter_upwards [eventuallyBadTupleRatioLtOneOfExponent hC hκ,
    eventually_ge_atTop (D / (κ / 2))] with x hx hBound
  apply hx d 0
  rw [add_zero]
  exact (div_le_iff₀ (half_pos hκ)).1 hBound |>.trans_eq (mul_comm _ _)

/-- The bad-tuple ratio with cutoff `exp (κ * x)` and cluster growth rate
`(d + 3) * κ`, as chosen in the fixed-dimension argument. -/
theorem eventuallyFixedBadTupleRatioLtOne {C κ : ℝ} (hC : 0 < C) (hκ : 0 < κ) (d : ℕ) :
    ∀ᶠ x in atTop,
      badTupleRatio C (((d : ℝ) + 3) * κ) (((d : ℝ) + 2) * (κ * x)) x d < 1 := by
  filter_upwards [eventuallyBadTupleRatioLtOne hC hκ d] with x hx
  have hExponent :
      ((d : ℝ) + 2) * (κ * x) - (((d : ℝ) + 3) * κ) * x = 0 - κ * x := by ring
  simpa only [badTupleRatio, hExponent] using hx

/-- The bad-tuple ratio is eventually less than one uniformly for the growing rank
of the joint lattice and prime selection, with cutoff `exp (sqrt x)`. -/
theorem eventuallyGrowingBadTupleRatioLtOne {C rate : ℝ} (hC : 0 < C) (hRate : 0 < rate)
    (m : ℕ) :
    ∀ᶠ x in atTop, ∀ d : ℕ, (d : ℝ) ≤ (m : ℝ) * x ^ (1 / 3 : ℝ) + 1 →
      badTupleRatio C rate (((d : ℝ) + 2) * Real.sqrt x) x d < 1 := by
  let K : ℝ := 8 * m + 10
  have hNeg : Tendsto (fun x : ℝ => x ^ (-(1 / 6) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)
  have hScaled : Tendsto (fun x : ℝ => K * x ^ (-(1 / 6) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hNeg.const_mul K
  filter_upwards [eventuallyBadTupleRatioLtOneOfExponent hC hRate,
    hScaled.eventually_lt_const (half_pos hRate), eventually_ge_atTop (1 : ℝ)]
    with x hx hPowerSmall hxOne
  intro d hd
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hxOne
  have hSqrt : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hxOne
  have hMono : Real.sqrt x ≤ x ^ (5 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxOne (by norm_num)
  have hCombine : x ^ (1 / 3 : ℝ) * Real.sqrt x = x ^ (5 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxPos]
    norm_num
  have hReweight : x ^ (-(1 / 6) : ℝ) * x = x ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add_one hxPos.ne']
    norm_num
  have hPower : K * x ^ (5 / 6 : ℝ) ≤ rate / 2 * x := by
    calc
      K * x ^ (5 / 6 : ℝ) = (K * x ^ (-(1 / 6) : ℝ)) * x := by
        rw [mul_assoc, hReweight]
      _ ≤ rate / 2 * x := mul_le_mul_of_nonneg_right hPowerSmall.le hxPos.le
  have hLogEight : Real.log 8 ≤ 7 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : 0 < (8 : ℝ))).trans (by norm_num)
  have hdNonneg : 0 ≤ (d : ℝ) := by positivity
  apply hx d
  calc
    (d : ℝ) * Real.log 8 + ((d : ℝ) + 2) * Real.sqrt x ≤
        (8 * (d : ℝ) + 2) * Real.sqrt x := by
      have hLog := mul_le_mul_of_nonneg_left hLogEight hdNonneg
      have hSqrtScale := mul_le_mul_of_nonneg_left hSqrt (show 0 ≤ 7 * (d : ℝ) by positivity)
      linarith only [hLog, hSqrtScale]
    _ ≤ (8 * ((m : ℝ) * x ^ (1 / 3 : ℝ)) + 10) * Real.sqrt x := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith only [hd]
    _ = 8 * (m : ℝ) * x ^ (5 / 6 : ℝ) + 10 * Real.sqrt x := by
      rw [← hCombine]
      ring
    _ ≤ K * x ^ (5 / 6 : ℝ) := by dsimp [K]; linarith only [hMono]
    _ ≤ rate / 2 * x := hPower

private theorem badTupleRatio_eq_div (C rate z x : ℝ) (d : ℕ) :
    badTupleRatio C rate z x d =
      C * 8 ^ d * x ^ 2 * (1 + 2 * (x / Real.log x)) *
        Real.exp (z + 2 * (x / Real.log x)) / Real.exp (rate * x - tupleVolumeLoss x) := by
  have hExponent : z - rate * x + 2 * (x / Real.log x) + tupleVolumeLoss x =
      (z + 2 * (x / Real.log x)) - (rate * x - tupleVolumeLoss x) := by ring
  rw [badTupleRatio, hExponent, Real.exp_sub, mul_div_assoc]

/-- A ratio below one also ensures that the cluster bound is large enough
for the distinct-tuple lower bound of Section 4. -/
theorem tupleRankSqLtCluster {C rate z x : ℝ} {d : ℕ}
    (hC : 0 < C) (hx : 0 < x) (hLog : 0 ≤ Real.log x) (hz : 0 ≤ z)
    (hRatio : badTupleRatio C rate z x d < 1) :
    (d : ℝ) ^ 2 < Real.exp (rate * x - tupleVolumeLoss x) / (C * x ^ 2) := by
  have hCast : (d : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (Nat.lt_pow_self (n := d) (by norm_num : 1 < (2 : ℕ))).le
  have hRank : (d : ℝ) ^ 2 ≤ (8 : ℝ) ^ d := by
    calc
      (d : ℝ) ^ 2 ≤ ((2 : ℝ) ^ d) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg d) hCast _
      _ = (4 : ℝ) ^ d := by rw [← pow_mul, mul_comm d, pow_mul]; norm_num
      _ ≤ (8 : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hu : 0 ≤ x / Real.log x := div_nonneg hx.le hLog
  have hExp : 1 ≤ Real.exp (z + 2 * (x / Real.log x)) := by
    rw [← Real.exp_zero, Real.exp_le_exp]
    positivity
  have hLower :
      (d : ℝ) ^ 2 * (C * x ^ 2) ≤
        C * 8 ^ d * x ^ 2 * (1 + 2 * (x / Real.log x)) *
          Real.exp (z + 2 * (x / Real.log x)) := by
    calc
      (d : ℝ) ^ 2 * (C * x ^ 2) ≤ (8 : ℝ) ^ d * (C * x ^ 2) := by gcongr
      _ = C * 8 ^ d * x ^ 2 := by ring
      _ ≤ C * 8 ^ d * x ^ 2 * (1 + 2 * (x / Real.log x)) := by
        apply le_mul_of_one_le_right (by positivity)
        linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  rw [badTupleRatio_eq_div, div_lt_iff₀ (Real.exp_pos _), one_mul] at hRatio
  exact (lt_div_iff₀ (by positivity)).2 (hLower.trans_lt hRatio)

/-- The bad-tuple bound, the cluster lower bound, and a ratio below one give strict
inequality between the bad count and the total count. -/
theorem badTupleCountLtTotal {C rate z x n bad total : ℝ} {d : ℕ}
    (hC : 0 < C) (hx : 0 < x) (hd : 0 < d)
    (hCluster : Real.exp (rate * x - tupleVolumeLoss x) / (C * x ^ 2) ≤ n)
    (hBad : bad ≤ 10 * 8 ^ d * (1 + 2 * (x / Real.log x)) *
      Real.exp (z + 2 * (x / Real.log x)) * n ^ (d - 1))
    (hTotal : n ^ d / 2 ≤ total)
    (hRatio : badTupleRatio (20 * C) rate z x d < 1) :
    bad < total := by
  let A := 10 * 8 ^ d * (1 + 2 * (x / Real.log x)) * Real.exp (z + 2 * (x / Real.log x))
  have hDenominator : 0 < C * x ^ 2 := by positivity
  have hn : 0 < n := (div_pos (Real.exp_pos _) hDenominator).trans_le hCluster
  have hCoeff : 2 * A < n := by
    apply lt_of_lt_of_le _ hCluster
    apply (lt_div_iff₀ hDenominator).2
    rw [badTupleRatio_eq_div, div_lt_iff₀ (Real.exp_pos _), one_mul] at hRatio
    convert hRatio using 1
    dsimp [A]
    ring
  calc
    bad ≤ A * n ^ (d - 1) := hBad
    _ < n / 2 * n ^ (d - 1) :=
      mul_lt_mul_of_pos_right (by linarith only [hCoeff]) (pow_pos hn _)
    _ = n ^ d / 2 := by
      rw [← mul_div_right_comm, ← pow_succ', Nat.sub_add_cancel hd]
    _ ≤ total := hTotal

end AbcSubexp.TupleCounting
