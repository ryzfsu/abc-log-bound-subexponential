/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.LatticeTranslateOverlap
public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import AbcTwoNinths.Paper.S5_Selection.RoofPeak
public import Subexp.Prerequisites.PrimitiveTaggedLattice
public import Subexp.Prerequisites.WeightedBallDimension

/-!
# The projected prime lattice

The two complementary logarithmic masses give a large exponent coordinate on the
primitive axis. Projection along this coordinate bounds the measure of the
signed-residue tori in Section 4.

## Main results
* `AbcSubexp.TupleCounting.exists_large_roof_coordinate`
* `AbcSubexp.TupleCounting.exists_projected_domain_mass_le`
* `AbcSubexp.TupleCounting.small_ball_embeds_of_shear`
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace AbcSubexp.TupleCounting

/-- The primitive axis has a coordinate of magnitude at least `h / (2x)`
when the error in the complementary logarithmic masses is at most a quarter. -/
theorem exists_large_roof_coordinate (t : AbcTwoNinths.Basic.Triple) {S : Finset ℕ}
    (hS : S ⊆ (t.a * t.b * t.c).primeFactors) (hS' : S.Nonempty)
    (v : {q // q ∈ S} → ℤ) {h E : ℝ} (hh : 0 ≤ h) (hx : 0 < t.thirdLogRadical)
    (hE : E ≤ 1 / 4)
    (hmass : 2 * (1 - E) * h ≤
      ∑ q : {q // q ∈ S}, ((v q).natAbs : ℝ) * Real.log (q.val : ℝ)) :
    ∃ j, (∀ i, (v i).natAbs ≤ (v j).natAbs) ∧ h / (2 * t.thirdLogRadical) ≤ |(v j : ℝ)| := by
  classical
  obtain ⟨p, hp⟩ := hS'
  have hidx : (Finset.univ : Finset {q // q ∈ S}).Nonempty := ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun q => (v q).natAbs) hidx
  have hpeak i := hj i (Finset.mem_univ i)
  refine ⟨j, hpeak, (div_le_iff₀ (by positivity)).2 ?_⟩
  have hb := AbcTwoNinths.Selection.peakMassSubtypeLe t hS v hpeak
  rw [Nat.cast_natAbs, Int.cast_abs] at hb
  nlinarith [mul_le_mul_of_nonneg_right hE hh]

/-- The total measure over all labeled copies of the projected fundamental
domain is at most `xp/h`, as in Section 4. -/
theorem exists_projected_domain_mass_le {I G : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup G] [Finite G] {p : ℕ} (red : AbcTwoNinths.ExteriorE2.Old I →+ G)
    (hcard : (Nat.card G : ℝ) = ((p : ℝ) - 1) / 2)
    (s : red.ker) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hroof : h / (2 * x) ≤ |((s : AbcTwoNinths.ExteriorE2.Old I) (.inl ()) : ℝ)|)
    (hprim : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a) :
    ∃ D : Set (AbcTwoNinths.ExteriorE2.Coord I), IsAddFundamentalDomain
        (AbcTwoNinths.ExteriorE2.projected red (s : AbcTwoNinths.ExteriorE2.Old I)).toAddSubgroup D volume ∧
      MeasurableSet D ∧ volume D < ⊤ ∧
      volume.real D = (Nat.card red.range : ℝ) / |((s : AbcTwoNinths.ExteriorE2.Old I) (.inl ()) : ℝ)| ∧
      (AbcTwoNinths.ExteriorE2.taggedMeasure (C := AbcSubexp.Prerequisites.Tag red) D volume).real Set.univ ≤ x * (p : ℝ) / h := by
  let k := (s : AbcTwoNinths.ExteriorE2.Old I) (.inl ())
  have hk : 0 < |(k : ℝ)| := (div_pos hh (by positivity)).trans_le hroof
  have hkn : k ≠ 0 := by
    intro he
    simp [he] at hk
  obtain ⟨D, hD, hmeas, hfin, hvol, htags⟩ := AbcSubexp.Prerequisites.fundamental_of_primitive red s hkn hprim
  refine ⟨D, hD, hmeas, hfin, hvol, ?_⟩
  rw [htags, hcard, div_div]
  change ((p : ℝ) - 1) / (2 * |(k : ℝ)|) ≤ x * p / h
  rw [div_le_div_iff₀ (by positivity) hh]
  have hm := (div_le_iff₀ (by positivity)).mp hroof
  change h ≤ |(k : ℝ)| * (2 * x) at hm
  nlinarith [mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]

/-- Under the projected shear bound the transverse ball of Section 4 embeds and
has volume at least `(1/(3 log x))^s` in ordinary exponent coordinates. -/
theorem small_ball_embeds_of_shear {I G : Type*} [Fintype I] [AddCommGroup G]
    (red : AbcTwoNinths.ExteriorE2.Old I →+ G) (s : AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    {x : ℝ} (hx : 1 < x) (hbudget : ∑ i, weight i ≤ 3 * x)
    (sep : ∀ w ∈ red.ker, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s w) < 2*x / Real.log x → AbcTwoNinths.ExteriorE2.project s w = 0)
    (center : AbcTwoNinths.ExteriorE2.Coord I) :
    ENNReal.ofReal ((1 / (3 * Real.log x)) ^ Fintype.card I) ≤
        volume (AbcTwoNinths.ExteriorE2.ball weight center (x / Real.log x / 2)) ∧
    ∀ a ∈ AbcTwoNinths.ExteriorE2.ball weight center (x / Real.log x / 2), ∀ b ∈ AbcTwoNinths.ExteriorE2.ball weight center (x / Real.log x / 2),
      ∀ l : (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup, l +ᵥ a = b → l = 0 := by
  have hu : x / Real.log x ≤ 2 * x / Real.log x :=
    div_le_div_of_nonneg_right (by linarith) (Real.log_pos hx).le
  refine ⟨?_, AbcTwoNinths.ExteriorE2.ballOrbitInjective red s weight hw center (x / Real.log x)
    (fun w hw' hwlt => sep w hw' (hwlt.trans_le hu))⟩
  have hlog := Real.log_pos hx
  have hvol := AbcSubexp.Prerequisites.sourceWeightedBallVolumeLower weight hw
    (α := 1 / Real.log x) (by positivity) (zero_lt_one.trans hx) hbudget center
  convert hvol using 1 <;> congr 2 <;> ring

end AbcSubexp.TupleCounting
