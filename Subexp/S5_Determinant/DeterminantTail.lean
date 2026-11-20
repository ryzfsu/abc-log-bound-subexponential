/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S4_TupleCounting.AuxiliaryPrimeCutoff
public import Subexp.S5_Determinant.SimplexRows
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform numerical estimates for the determinant

The two full degree simplices have a fixed row-count ratio at fixed exponent.
The logarithm of the contact prime grows at least linearly in the radical
logarithm. The transverse and displacement errors also tend to zero on the
native contact, including the factor-three window of the fresh primes.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real Filter
open scoped Topology

/-- The normalized combinatorial error for the full simplex row counts. -/
def Contact.determinantEntropy {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t) : ℝ :=
  let m := dimension ε
  let n := c.depth
  let B := (simplexRows m ⌈degreeMargin ε * n⌉₊).card
  let N := (simplexRows m n).card + B
  ((N : ℝ) / B) * (20 * m * (m + 1 : ℝ) * log 2 + log N / n) / log c.prime

private theorem eventual_comparison_errors (e A C M : ℝ) (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, A / x < e / 40 ∧
      C * (1 / log x + log 3 / x) < e / 40 ∧
      M * sqrt ((2 / e) * (x * exp (-(3 * e) * x))) < e / 40 := by
  have h₁ : Tendsto (fun x : ℝ => A / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun x : ℝ => 1 / log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hl' : Tendsto (fun x : ℝ => log 3 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h₂ : Tendsto (fun x : ℝ => C * (1 / log x + log 3 / x)) atTop (𝓝 0) := by
    simpa using (hl.add hl').const_mul C
  have hg : Tendsto (fun x : ℝ => x * exp (-(3 * e) * x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3 * e) (by positivity)
  have h₃ : Tendsto (fun x : ℝ => M * sqrt ((2 / e) * (x * exp (-(3 * e) * x)))) atTop (𝓝 0) := by
    simpa using ((hg.const_mul (2 / e)).sqrt).const_mul M
  have hpos : 0 < e / 40 := by positivity
  exact (h₁.eventually_lt_const hpos).and ((h₂.eventually_lt_const hpos).and
    (h₃.eventually_lt_const hpos))

/-- On a single exponent-dependent tail, the three error terms each cost
strictly less than one fortieth of the working exponent. The last estimate
applies to every displacement admitted by the native box height bound. -/
theorem eventual_determinant_errors {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical →
      c.determinantEntropy < exponent ε / 40 ∧
      3 * (dimension ε : ℝ) ^ 2 * (t.thirdLogRadical / log t.thirdLogRadical + log 3) / log c.cutoff < exponent ε / 40 ∧
      ∀ J : ℝ, J ≤ (1 + 2 * (dimension ε : ℝ)) *
          sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) * AbcTwoNinths.Basic.rationalHeight c.source →
        J / ((c.depth : ℝ) * log c.prime) < exponent ε / 40 := by
  let e := exponent ε
  let b := degreeMargin ε
  let m := dimension ε
  let β := e ^ 2 / 10
  let R := 1 + ((m : ℝ) / b) ^ m
  let L := 20 * (m : ℝ) * (m + 1) * log 2 + (log 2 + m)
  let M := (1 + 2 * (m : ℝ)) / (2 * e)
  have he : 0 < e := lt_min hε (by norm_num)
  have he' : e ≤ 1 / 10 := min_le_right _ _
  have hb : 0 < b := by change 0 < e / 10; positivity
  have hb' : b ≤ 1 := by change e / 10 ≤ 1; linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hm : 0 < m := by
    have hw : 0 < windowWidth ε := by
      change 0 < e / ((depthParameter ε : ℝ) + 1)
      positivity
    exact Nat.ceil_pos.mpr (div_pos (by positivity) hw)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hln2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hln3 : 0 ≤ log 3 := log_nonneg (by norm_num)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 (eventual_comparison_errors e (R * L / e)
    (3 * (m : ℝ) ^ 2 / β) M he)
  refine ⟨max (max 2 (20 / e ^ 2)) X, ?_⟩
  intro t c ht
  obtain ⟨hent, htrans, hdisp⟩ := hX t.thirdLogRadical ((le_max_right _ _).trans ht)
  have hx2 : 2 ≤ t.thirdLogRadical := (le_max_of_le_left (le_max_left _ _)).trans ht
  have hx : 0 < t.thirdLogRadical := by linarith
  have hlogx : 0 < log t.thirdLogRadical := log_pos (by linarith)
  have h20 := (div_le_iff₀ (pow_pos he 2)).mp ((le_max_of_le_left (le_max_right _ _)).trans ht)
  have hcmp := TupleCounting.auxiliaryPrimeCutoffBounds he he' (Nat.cast_pos.mpr c.prime_isPrime.pos)
    (by linarith only [h20] : 20 ≤ e ^ 2 * t.thirdLogRadical) (by convert c.log_lower using 1; ring)
    c.log_upper c.axial_height_lower
  have hcut : c.cutoff = TupleCounting.auxiliaryPrimeCutoff e t.thirdLogRadical c.prime (AbcTwoNinths.Basic.rationalHeight c.source) := by
    simp only [Contact.cutoff, TupleCounting.auxiliaryPrimeCutoff, sqrt_eq_rpow, auxiliaryRate,
      e]
  have hcut₁ : β * t.thirdLogRadical ≤ log c.cutoff := by rw [hcut]; exact hcmp.2.2.2.1
  have hcut₂ : log c.cutoff ≤ t.thirdLogRadical := by rw [hcut]; exact hcmp.2.2.2.2.1
  have hlogcut := (mul_pos hβ hx).trans_le hcut₁
  have hheight : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have hshare : 0 < (c.depth : ℝ) * log c.prime :=
    (mul_pos (mul_pos zero_lt_two he) hheight).trans c.depth_share
  have hlogp : e * t.thirdLogRadical ≤ log c.prime := by
    have h := c.log_lower
    change (3 - 6 / 100) * e * t.thirdLogRadical < _ at h
    nlinarith only [h, mul_pos he hx]
  have hn : 0 < c.depth := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hshare
  refine ⟨?_, ?_, ?_⟩
  · let B := (simplexRows m ⌈b * c.depth⌉₊).card
    let N := (simplexRows m c.depth).card + B
    have hr : (N : ℝ) / B ≤ R := simplexRows_ratio_le hm hn hb
    have hl : 20 * (m : ℝ) * (m + 1) * log 2 + log N / c.depth ≤ L :=
      add_le_add_right (log_card_simplexRows_add_div_le hn hb') _
    calc
      c.determinantEntropy ≤ R * L / log c.prime :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity) |>.trans
          (mul_le_mul_of_nonneg_right hr hL)) ((mul_pos he hx).le.trans hlogp)
      _ ≤ R * L / (e * t.thirdLogRadical) := div_le_div_of_nonneg_left (mul_nonneg hR hL) (mul_pos he hx) hlogp
      _ = (R * L / e) / t.thirdLogRadical := (div_div _ _ _).symm
      _ < _ := hent
  · calc
      _ ≤ 3 * (m : ℝ) ^ 2 * (t.thirdLogRadical / log t.thirdLogRadical + log 3) / (β * t.thirdLogRadical) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hβ hx) hcut₁
      _ = (3 * (m : ℝ) ^ 2 / β) * (1 / log t.thirdLogRadical + log 3 / t.thirdLogRadical) := by
        field_simp
      _ < _ := htrans
  · intro J hJ
    have hsmall : log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source ≤
        (2 / e) * (t.thirdLogRadical * exp (-(3 * e) * t.thirdLogRadical)) := by
      calc
        _ ≤ t.thirdLogRadical / AbcTwoNinths.Basic.rationalHeight c.source := div_le_div_of_nonneg_right hcut₂ hheight.le
        _ ≤ t.thirdLogRadical / ((e / 2) * exp (3 * e * t.thirdLogRadical)) :=
          div_le_div_of_nonneg_left hx.le (by positivity) c.axial_height_lower
        _ = _ := by rw [neg_mul, exp_neg]; ring
    have hrad := sqrt_le_sqrt hsmall
    have hnon : 0 ≤ (1 + 2 * (m : ℝ)) * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) *
        AbcTwoNinths.Basic.rationalHeight c.source := by positivity
    calc
      _ ≤ ((1 + 2 * (m : ℝ)) * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) * AbcTwoNinths.Basic.rationalHeight c.source) /
          ((c.depth : ℝ) * log c.prime) := div_le_div_of_nonneg_right hJ hshare.le
      _ ≤ _ / (2 * e * AbcTwoNinths.Basic.rationalHeight c.source) :=
        div_le_div_of_nonneg_left hnon (by positivity) c.depth_share.le
      _ = M * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) := by dsimp [M]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hrad hM
      _ < _ := hdisp

/-- Including the axial error at the real place, the normalized total error
in the height upper bound is strictly below the second-block degree margin. -/
theorem eventual_determinant_error_sum_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical → ∀ J : ℝ,
      J ≤ (1 + 2 * (dimension ε : ℝ)) * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) *
          AbcTwoNinths.Basic.rationalHeight c.source →
      |log (|(c.source : ℝ)|)| / AbcTwoNinths.Basic.rationalHeight c.source +
        3 * (dimension ε : ℝ) ^ 2 * (t.thirdLogRadical / log t.thirdLogRadical + log 3) / log c.cutoff +
        J / ((c.depth : ℝ) * log c.prime) + c.determinantEntropy < degreeMargin ε := by
  obtain ⟨X, hX⟩ := eventual_determinant_errors hε
  refine ⟨X, ?_⟩
  intro t c ht J hJ
  obtain ⟨hentropy, htrans, hdisp⟩ := hX t c ht
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have hreal := (div_le_iff₀ hh).mpr c.real_contact
  unfold degreeMargin
  linarith only [hreal, hentropy, htrans, hdisp J hJ, he]

end AbcSubexp
