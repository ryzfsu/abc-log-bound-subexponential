/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.NativeWindow

/-!
# Radius margin for the hitting window

The logarithmic cutoff bound leaves room in the simplex for the rounded
degree and the full third-window endpoint in Section 6.

## Main results
* `AbcSubexp.Contact.degree_add_hittingWindow_le_radius`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real

/-- The cutoff margin and the depth threshold absorb the rounding losses in
the native hitting window and simplex radius. -/
theorem Contact.degree_add_hittingWindow_le_radius {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}
    (c : Contact ε t) (hε : 0 < ε) (hcutoff_pos : 0 < log c.cutoff)
    (hcutoff : log c.cutoff ≤ (1 - 14 * exponent ε / 5) * log (c.prime : ℝ))
    (hdepth : 4 * ((dimension ε : ℝ) + 2) ≤ exponent ε * (c.depth : ℝ)) :
    c.degree + c.hittingWindow ≤ c.radius := by
  let e := exponent ε
  let k : ℝ := depthParameter ε
  let m : ℝ := dimension ε
  let n : ℝ := c.depth
  let P := log (c.prime : ℝ)
  let L := log c.cutoff
  have he : 0 < e := lt_min hε (by norm_num)
  have he_upper : e ≤ 1 / 10 := min_le_right _ _
  have hP : 0 < P := by
    apply log_pos
    have hprime := c.prime_gt_five
    exact_mod_cast (show 1 < c.prime by omega)
  have hL : 0 < L := hcutoff_pos
  have hdim : 0 < m + 1 := by positivity
  have hdepth' : 4 * (m + 2) ≤ e * n := hdepth
  have hn : 0 < n := by
    have hs : 0 < e * n := (by positivity : 0 < 4 * (m + 2)).trans_le hdepth'
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos he.le hn)) hs
  have hk_lower : 2 / e ≤ k := Nat.le_ceil _
  have hk : 0 < k := (by positivity : 0 < 2 / e).trans_le hk_lower
  have hrecip : 1 / k ≤ e / 2 := by
    have hek := (div_le_iff₀ he).mp hk_lower
    apply (div_le_iff₀ hk).mpr
    linarith
  have hden : 0 < 1 + 1 / k := by positivity

  have hbudget_coeff : (1 + 2 * e) * ((1 + 1 / k) * L) ≤ (1 - e / 5) * P := calc
    _ ≤ (1 + 2 * e) * ((1 + e / 2) * ((1 - 14 * e / 5) * P)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (by linarith) hcutoff hL.le (by positivity)) (by positivity)
    _ = ((1 + 2 * e) * (1 - 14 * e / 5)) * (1 + e / 2) * P := by ring
    _ ≤ (1 - 4 * e / 5) * (1 + e / 2) * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg e]) (by positivity)) hP.le
    _ ≤ (1 - e / 5) * P := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg e]) hP.le
  have hbudget :
      (m + 1) * (c.transverseBudget / L) = (1 - e / 5) * n * P / ((1 + 1 / k) * L) := by
    change (m + 1) * (((1 - e / 5) * n * P / ((m + 1) * (1 + 1 / k))) / L) = _
    field_simp [hdim.ne', hden.ne', hk.ne', hL.ne']
  have hbudget_lower : (1 + 2 * e) * n ≤ (m + 1) * (c.transverseBudget / L) := by
    rw [hbudget]
    apply (le_div_iff₀ (mul_pos hden hL)).mpr
    calc
      _ = ((1 + 2 * e) * ((1 + 1 / k) * L)) * n := by ring
      _ ≤ ((1 - e / 5) * P) * n := mul_le_mul_of_nonneg_right hbudget_coeff hn.le
      _ = _ := by ring
  have hshift : c.transverseBudget / L < (c.shift : ℝ) + 1 := Nat.lt_floor_add_one _
  have hradius : (1 + 2 * e) * n < (c.radius : ℝ) + (m + 1) := calc
    _ ≤ (m + 1) * (c.transverseBudget / L) := hbudget_lower
    _ < (m + 1) * ((c.shift : ℝ) + 1) := mul_lt_mul_of_pos_left hshift hdim
    _ = _ := by
      simp only [Contact.radius, Nat.cast_mul, Nat.cast_add, Nat.cast_one, m]
      ring

  have hdegree_arg : 0 < (1 + e / 10) * n := by positivity
  have hdegree_ceil : 1 ≤ ⌈(1 + e / 10) * n⌉₊ := by
    have hcast : 0 < (⌈(1 + e / 10) * n⌉₊ : ℝ) := hdegree_arg.trans_le (Nat.le_ceil _)
    have hnat : 0 < ⌈(1 + e / 10) * n⌉₊ := by exact_mod_cast hcast
    exact hnat
  have hdegree : (c.degree : ℝ) ≤ (1 + e / 10) * n := by
    change ((⌈(1 + e / 10) * n⌉₊ - 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_sub hdegree_ceil, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hdegree_arg.le]
  have hwindow_ratio : 3 / (k + 1) ≤ 3 * e / 2 := calc
    _ ≤ 3 / k := div_le_div_of_nonneg_left (by norm_num) hk (by linarith)
    _ = 3 * (1 / k) := by ring
    _ ≤ _ := by linarith
  have hwindow : (c.hittingWindow : ℝ) < (3 * e / 2) * ((1 + e / 10) * n) + 1 := by
    have hround : (c.hittingWindow : ℝ) < 3 * (c.degree : ℝ) / (k + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    rw [mul_comm 3 (c.degree : ℝ), mul_div_assoc, mul_comm (c.degree : ℝ)] at hround
    exact hround.trans_le (add_le_add
      (mul_le_mul hwindow_ratio hdegree (by positivity) (by positivity)) le_rfl)
  have hdegree_window :
      (c.degree : ℝ) + (c.hittingWindow : ℝ) ≤ (1 + 7 * e / 4) * n + 1 := calc
    _ ≤ (1 + e / 10) * n + ((3 * e / 2) * ((1 + e / 10) * n) + 1) :=
      add_le_add hdegree hwindow.le
    _ = ((1 + e / 10) * (1 + 3 * e / 2)) * n + 1 := by ring
    _ ≤ _ := by
      have he_quadratic := mul_nonneg he.le (sub_nonneg.mpr he_upper)
      have hcoeff : (1 + e / 10) * (1 + 3 * e / 2) ≤ 1 + 7 * e / 4 := by
        nlinarith
      exact add_le_add (mul_le_mul_of_nonneg_right hcoeff hn.le) le_rfl
  have hreal : (c.degree : ℝ) + (c.hittingWindow : ℝ) ≤ (c.radius : ℝ) := by
    linarith
  exact_mod_cast hreal

end AbcSubexp
