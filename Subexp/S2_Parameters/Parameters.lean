/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S1_Statement.Statement

/-!
# Fixed parameters

These parameters determine the rank, exponent, and tolerance in the logarithmic height bound.

## Main results

* `AbcSubexp.Parameters.fixedParameterBounds`
* `AbcSubexp.Parameters.boxWidthBounds`
* `AbcSubexp.Parameters.transverseRadiusMargin`
* `AbcSubexp.Parameters.thirdWindowFits`
* `AbcSubexp.Parameters.determinantMargin`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.Parameters

/-- The working exponent in Section 2. -/
def exponent (ε : ℝ) : ℝ := min ε (1 / 10)

/-- The contact rate in Section 2. -/
def contactRate (ε : ℝ) : ℝ := exponent ε / 100

/-- The depth parameter in Section 2. -/
def depthParameter (ε : ℝ) : ℕ := ⌈2 / exponent ε⌉₊

/-- The lower bound for the width of the circle window in Section 2. -/
def windowWidth (ε : ℝ) : ℝ := exponent ε / (depthParameter ε + 1)

/-- The number of transverse generators per list in the parameter table of Section 2. -/
def dimension (ε : ℝ) : ℕ := ⌈2 * (depthParameter ε + 1) / windowWidth ε⌉₊

/-- The rank of the lattice used for the determinant in Section 2. -/
def latticeRank (ε : ℝ) : ℕ := dimension ε + 1

/-- The error tolerance for each coordinate of the hitting slope in Section 2. -/
def phaseTolerance (ε : ℝ) : ℝ := windowWidth ε / (4 * (depthParameter ε + 1))

/-- The extra exponent in the auxiliary-prime cutoff in Section 2. -/
def auxiliaryRate (ε : ℝ) : ℝ := (exponent ε) ^ 2 / 10

/-- The first degree margin in the two blocks of Section 5. -/
def degreeMargin (ε : ℝ) : ℝ := exponent ε / 10

/-- The rate for the fixed-rank short-vector threshold in Section 2. -/
def shortVectorRate (ε : ℝ) : ℝ := auxiliaryRate ε / ((latticeRank ε : ℝ) + 3)

variable {ε : ℝ}

/-- The normalized exponent has the range required in Section 2. -/
theorem exponentBounds (hε : 0 < ε) :
    0 < exponent ε ∧ exponent ε ≤ ε ∧ exponent ε ≤ 1 / 10 := by
  exact ⟨lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _⟩

/-- Truncation at `1 / 10` preserves positivity of the input exponent. -/
theorem exponentPos (hε : 0 < ε) : 0 < exponent ε := (exponentBounds hε).1

/-- Rounding the depth parameter up preserves the lower bound `2 / exponent ε`. -/
theorem depthParameterLower (ε : ℝ) : 2 / exponent ε ≤ (depthParameter ε : ℝ) :=
  Nat.le_ceil _

/-- A positive input exponent gives a positive depth parameter. -/
theorem depthParameterPos (hε : 0 < ε) : 0 < depthParameter ε := by
  have hpos := lt_of_lt_of_le (div_pos (by norm_num) (exponentPos hε)) (depthParameterLower ε)
  exact_mod_cast hpos

private theorem depthReciprocal (hε : 0 < ε) :
    1 / (depthParameter ε : ℝ) ≤ exponent ε / 2 := by
  have he := exponentPos hε
  have hk : 0 < (depthParameter ε : ℝ) := by exact_mod_cast depthParameterPos hε
  have hlower := (div_le_iff₀ he).mp (depthParameterLower ε)
  apply (div_le_iff₀ hk).mpr
  nlinarith only [hlower]

/-- The prescribed lower bound for the axial window width is positive. -/
theorem windowWidthPos (hε : 0 < ε) : 0 < windowWidth ε := by
  unfold windowWidth
  exact div_pos (exponentPos hε) (by positivity)

/-- The prescribed window width is at most the exponent cap `1 / 10`. -/
theorem windowWidthLe (hε : 0 < ε) : windowWidth ε ≤ 1 / 10 := by
  unfold windowWidth
  calc
    _ ≤ exponent ε := div_le_self (exponentPos hε).le
      (by linarith only [Nat.cast_nonneg (α := ℝ) (depthParameter ε)])
    _ ≤ 1 / 10 := (exponentBounds hε).2.2

/-- Rounding the tuple dimension up preserves its lower bound in terms of the window width. -/
theorem dimensionLower (ε : ℝ) :
    2 * ((depthParameter ε : ℝ) + 1) / windowWidth ε ≤ dimension ε := by
  exact Nat.le_ceil _

/-- Each list has at least one transverse generator. -/
theorem dimensionPos (hε : 0 < ε) : 0 < dimension ε := by
  have hnum : 0 < 2 * ((depthParameter ε : ℝ) + 1) := by positivity
  have hpos := lt_of_lt_of_le (div_pos hnum (windowWidthPos hε)) (dimensionLower ε)
  exact_mod_cast hpos

/-- The phase tolerance lies strictly between zero and half a turn. -/
theorem phaseToleranceBounds (hε : 0 < ε) :
    0 < phaseTolerance ε ∧ phaseTolerance ε < 1 / 2 := by
  have hpos : 0 < 4 * ((depthParameter ε : ℝ) + 1) := by positivity
  unfold phaseTolerance
  refine ⟨div_pos (windowWidthPos hε) hpos, (div_lt_iff₀ hpos).mpr ?_⟩
  nlinarith only [windowWidthLe hε, Nat.cast_nonneg (α := ℝ) (depthParameter ε)]

/-- Twice the depth parameter plus two, divided by the tuple dimension, fits in the window. -/
theorem colorWidthMargin (hε : 0 < ε) :
    2 * ((depthParameter ε : ℝ) + 1) / dimension ε ≤ windowWidth ε := by
  have hd : 0 < (dimension ε : ℝ) := by exact_mod_cast dimensionPos hε
  apply (div_le_iff₀ hd).mpr
  simpa only [mul_comm (windowWidth ε)] using
    (div_le_iff₀ (windowWidthPos hε)).mp (dimensionLower ε)

/-- The phase error at depth parameter plus one uses a quarter of the prescribed width. -/
theorem phaseFittingMargin (ε : ℝ) :
    ((depthParameter ε : ℝ) + 1) * phaseTolerance ε = windowWidth ε / 4 := by
  unfold phaseTolerance
  have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  field_simp

/-- The fixed parameters of Section 2 are positive and satisfy the interpolation margins. -/
theorem fixedParameterBounds (hε : 0 < ε) :
    0 < contactRate ε ∧ 0 < auxiliaryRate ε ∧ 0 < degreeMargin ε ∧
    0 < depthParameter ε ∧ 0 < windowWidth ε ∧ 0 < dimension ε ∧ 0 < latticeRank ε ∧
    0 < phaseTolerance ε ∧ phaseTolerance ε < 1 / 2 ∧ 0 < shortVectorRate ε ∧
    2 * ((depthParameter ε : ℝ) + 1) / dimension ε ≤ windowWidth ε ∧
    ((depthParameter ε : ℝ) + 1) * phaseTolerance ε = windowWidth ε / 4 := by
  have he := exponentPos hε
  have hr : 0 < auxiliaryRate ε := by
    unfold auxiliaryRate
    positivity
  exact ⟨div_pos he (by norm_num), hr, div_pos he (by norm_num), depthParameterPos hε,
    windowWidthPos hε, dimensionPos hε, Nat.succ_pos _, (phaseToleranceBounds hε).1,
    (phaseToleranceBounds hε).2, div_pos hr (by positivity), colorWidthMargin hε,
    phaseFittingMargin ε⟩

/-- The axial width from Section 5 is at least the prescribed width from Section 2
and is strictly less than a full turn. -/
theorem boxWidthBounds (hε : 0 < ε) {δ : ℝ}
    (hδ : 2 * exponent ε ≤ δ) (hδUpper : δ ≤ 2) :
    windowWidth ε ≤ (1 - exponent ε / 5) * δ / ((depthParameter ε : ℝ) + 1) ∧
      (1 - exponent ε / 5) * δ / ((depthParameter ε : ℝ) + 1) < 1 := by
  have he := exponentPos hε
  have heUpper := (exponentBounds hε).2.2
  have hscale : 9 / 10 ≤ 1 - exponent ε / 5 := by linarith
  have hk : 2 ≤ (depthParameter ε : ℝ) + 1 := by
    have hk := depthParameterPos hε
    exact_mod_cast (show 2 ≤ depthParameter ε + 1 by omega)
  have hden : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  constructor
  · unfold windowWidth
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      exponent ε ≤ (9 / 10) * (2 * exponent ε) := by linarith
      _ ≤ (1 - exponent ε / 5) * δ :=
        mul_le_mul hscale hδ (by linarith) (by linarith)
  · apply (div_lt_iff₀ hden).mpr
    rw [one_mul]
    calc
      (1 - exponent ε / 5) * δ ≤ (1 - exponent ε / 5) * 2 := by
        exact mul_le_mul_of_nonneg_left hδUpper (by linarith)
      _ < 2 := by linarith
      _ ≤ (depthParameter ε : ℝ) + 1 := hk

/-- The transverse budget leaves more than `2e` relative slack before taking floors. -/
theorem degreeBudgetRatio (hε : 0 < ε) :
    1 + 2 * exponent ε < (1 - exponent ε / 5) /
      ((1 + 1 / (depthParameter ε : ℝ)) * (1 + degreeMargin ε) *
        (1 - (14 / 5) * exponent ε)) := by
  have he := exponentPos hε
  have heUpper := (exponentBounds hε).2.2
  have hk : 0 < (depthParameter ε : ℝ) := by exact_mod_cast depthParameterPos hε
  have hcut : 0 < 1 - (14 / 5) * exponent ε := by linarith
  unfold degreeMargin
  have hden : 0 < (1 + 1 / (depthParameter ε : ℝ)) * (1 + exponent ε / 10) *
      (1 - (14 / 5) * exponent ε) := by positivity
  apply (lt_div_iff₀ hden).mpr
  have hproduct : (1 + 1 / (depthParameter ε : ℝ)) * (1 + exponent ε / 10) *
      (1 - (14 / 5) * exponent ε) ≤ 1 - (11 / 5) * exponent ε := by
    have hreciprocal : 1 + 1 / (depthParameter ε : ℝ) ≤ 1 + exponent ε / 2 :=
      add_le_add_right (depthReciprocal hε) 1
    calc
      _ ≤ (1 + exponent ε / 2) * (1 + exponent ε / 10) *
          (1 - (14 / 5) * exponent ε) := by
        apply mul_le_mul_of_nonneg_right _ hcut.le
        exact mul_le_mul_of_nonneg_right hreciprocal (by positivity)
      _ ≤ _ := by
        nlinarith only [sq_nonneg (exponent ε), pow_nonneg he.le 3]
  calc
    _ ≤ (1 + 2 * exponent ε) * (1 - (11 / 5) * exponent ε) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ < _ := by nlinarith only [pow_pos he 2]

/-- After coordinatewise rounding, the simplex radius still exceeds the degree by
the relative margin in Section 5. -/
theorem transverseRadiusMargin (hε : 0 < ε) {D L : ℝ} (hD : 0 < D)
    (hround : (latticeRank ε : ℝ) < exponent ε * D / 10)
    (hbudget : (1 - exponent ε / 5) /
      ((1 + 1 / (depthParameter ε : ℝ)) * (1 + degreeMargin ε) *
        (1 - (14 / 5) * exponent ε)) * D - latticeRank ε ≤ L) :
    (1 + (19 / 10) * exponent ε) * D < L := by
  have hratio := mul_lt_mul_of_pos_right (degreeBudgetRatio hε) hD
  linarith only [hratio, hround, hbudget]

/-- The enlarged simplex for the prime window of Section 6 fits in the simplex from Section 5. -/
theorem thirdWindowFits (hε : 0 < ε) {D L : ℕ}
    (hD : 10 / exponent ε < (D : ℝ))
    (hL : (1 + (19 / 10) * exponent ε) * (D : ℝ) < (L : ℝ)) :
    D + ⌈3 * (D : ℝ) / ((depthParameter ε : ℝ) + 1)⌉₊ ≤ L := by
  have he := exponentPos hε
  have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
  have hsize := (div_lt_iff₀ he).mp hD
  have hcoeff : 3 * (D : ℝ) / ((depthParameter ε : ℝ) + 1) ≤ (3 / 2) * exponent ε * D := by
    have hdepth : 2 ≤ ((depthParameter ε : ℝ) + 1) * exponent ε := by
      have hdepth := (div_le_iff₀ he).mp (depthParameterLower ε)
      nlinarith only [hdepth, he]
    apply (div_le_iff₀ hk).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hdepth (Nat.cast_nonneg (α := ℝ) D)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 3 * (D : ℝ) /
    ((depthParameter ε : ℝ) + 1) by positivity)
  have hfit : (D : ℝ) + (⌈3 * (D : ℝ) / ((depthParameter ε : ℝ) + 1)⌉₊ : ℝ) < L := by
    nlinarith only [hcoeff, hsize, hceil, hL]
  exact (by exact_mod_cast hfit : D + ⌈3 * (D : ℝ) / ((depthParameter ε : ℝ) + 1)⌉₊ < L).le

/-- The local determinant margin in Section 5 exceeds the global budget with its error term. -/
theorem determinantMargin (hε : 0 < ε) {δ : ℝ} (hδ : δ < degreeMargin ε) :
    1 - exponent ε / 5 + δ <
      1 - (dimension ε : ℝ) * degreeMargin ε / latticeRank ε := by
  let m : ℝ := dimension ε
  have hden : 0 < m + 1 := by positivity
  have he := exponentPos hε
  simp only [latticeRank, Nat.cast_add, Nat.cast_one, degreeMargin]
  change 1 - exponent ε / 5 + δ < 1 - m * (exponent ε / 10) / (m + 1)
  change δ < exponent ε / 10 at hδ
  have hratio : m * (exponent ε / 10) / (m + 1) ≤ exponent ε / 10 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [he]
  linarith

end AbcSubexp.Parameters
