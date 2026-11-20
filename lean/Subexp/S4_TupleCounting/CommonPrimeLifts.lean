/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.CommonTaggedBall
public import AbcTwoNinths.Paper.S6_Diamond.SameSourceOverlapCounting
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Simultaneous old lifts in a common ball

In the common family of Section 4, every ordered pair has a fixed old lift with
small transverse cost and trivial corrected residue.

## Main results
* `AbcSubexp.TupleCounting.existsCommonPairLifts`
* `AbcSubexp.TupleCounting.existsCommonPrimeLifts`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace AbcSubexp.TupleCounting

/-- Every ordered pair of a specified family in one common tagged ball admits
a simultaneously fixed correction on the old coordinates. -/
theorem pairLifts_of_commonCenter {I G : Type*} [Fintype I] [AddCommGroup G]
    (red : AbcTwoNinths.ExteriorE2.Old I →+ G) (s : AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (r : ℝ) (P : Finset ℕ) (label : ℕ → G) {D : Set (AbcTwoNinths.ExteriorE2.Coord I)}
    (rep : AbcSubexp.Prerequisites.Tag red → G) (center : ℕ → AbcTwoNinths.ExteriorE2.Old I)
    (hc : ∀ j, label j = rep (AbcSubexp.Prerequisites.tag red (label j)) + red (center j))
    (z : AbcSubexp.Prerequisites.Tag red × AbcTwoNinths.ExteriorE2.Coord I)
    (hz : ∀ q ∈ P, z.1 = AbcSubexp.Prerequisites.tag red (label q) ∧
      z.2 ∈ AbcTwoNinths.ExteriorE2.wrapped (L := (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup) D
        (AbcTwoNinths.ExteriorE2.ball weight (AbcTwoNinths.ExteriorE2.project s (center q)) (r / 2))) :
    ∃ lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old I, ∀ i ∈ P, ∀ j ∈ P,
      AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s (lift i j)) < r ∧ red (lift i j) + label i - label j = 0 := by
  classical
  have hpair (i : ℕ) (hi : i ∈ P) (j : ℕ) (hj : j ∈ P) :
      ∃ w : AbcTwoNinths.ExteriorE2.Old I, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s w) < r ∧ red w + label i - label j = 0 := by
    obtain ⟨hzi, hBi⟩ := hz i hi
    obtain ⟨hzj, hBj⟩ := hz j hj
    let π := (AbcTwoNinths.ExteriorE2.project s).toAddMonoidHom
    let B := AbcTwoNinths.Diamond.weightedPatch s weight (r / 2)
    obtain ⟨qz, hqi, hqj⟩ := AbcTwoNinths.Diamond.quotientOverlapOfOrbit
      red.toMultiplicative π (B (center i)) (B (center j))
      (AbcTwoNinths.ExteriorE2.orbitOfWrappedOverlap ⟨hBi, hBj⟩)
    have htag : AbcSubexp.Prerequisites.tag red (label j) = AbcSubexp.Prerequisites.tag red (label i) := hzj.symm.trans hzi
    have hpatch : AbcTwoNinths.Diamond.PatchInput red.toMultiplicative π
        (fun q => Multiplicative.ofAdd (label q)) B i j :=
      ⟨center i, center j, Multiplicative.ofAdd (rep (AbcSubexp.Prerequisites.tag red (label i))), qz,
        hc i, htag ▸ hc j, hqi, hqj⟩
    obtain ⟨w, hwcost, hwred⟩ := AbcTwoNinths.Diamond.weightedWitness
      s red.toMultiplicative _ weight hw hpatch
    refine ⟨w, hwcost.trans_eq (by ring), ?_⟩
    change red w + (label i - label j) = 0 at hwred
    rwa [add_sub_assoc]
  choose! lift hlift using hpair
  exact ⟨lift, hlift⟩

/-- Choose the corrections for all ordered pairs in the same counted family. -/
theorem existsCommonPairLifts {I G : Type*} [Fintype I] [AddCommGroup G] [Finite G]
    (red : AbcTwoNinths.ExteriorE2.Old I →+ G) (s : AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (r : ℝ) (Q : Finset ℕ) (label : ℕ → G) {D : Set (AbcTwoNinths.ExteriorE2.Coord I)}
    (hD : IsAddFundamentalDomain (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup D volume)
    (hDm : MeasurableSet D) (hDf : volume D < ⊤)
    (hshort : ∀ w ∈ red.ker, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s w) < r → AbcTwoNinths.ExteriorE2.project s w = 0)
    (hvol : volume.real D = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)|) :
    ∃ (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old I), P ⊆ Q ∧
      ⌈(Q.card : ℝ) * (volume : Measure (AbcTwoNinths.ExteriorE2.Coord I)).real (AbcTwoNinths.ExteriorE2.ball weight 0 (r / 2)) /
        ((Nat.card G : ℝ) / |(s (.inl ()) : ℝ)|)⌉₊ ≤ P.card ∧
      ∀ i ∈ P, ∀ j ∈ P, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s (lift i j)) < r ∧
        red (lift i j) + label i - label j = 0 := by
  classical
  obtain ⟨rep, center, hc⟩ := AbcSubexp.Prerequisites.choose_centers red label
  obtain ⟨z, P, hP, hcard, hz⟩ := existsCommonTaggedBall red s weight hw r Q label
    (fun q => AbcTwoNinths.ExteriorE2.project s (center q)) hD hDm hDf hshort hvol
  obtain ⟨lift, hlift⟩ := pairLifts_of_commonCenter red s weight hw r P label rep center hc z hz
  exact ⟨P, lift, hP, hcard, hlift⟩

/-- For the signed prime reduction, every chosen old lift cancels the fresh label difference. -/
theorem existsCommonPrimeLifts {I : Type*} [Fintype I]
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)] (red : AbcTwoNinths.ExteriorE2.Old I →+ AbcSubexp.Prerequisites.Residue p)
    (s : AbcTwoNinths.ExteriorE2.Old I)
    (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j) (r : ℝ) (Q : Finset ℕ)
    {D : Set (AbcTwoNinths.ExteriorE2.Coord I)}
    (hD : IsAddFundamentalDomain (AbcTwoNinths.ExteriorE2.projected (G := AbcSubexp.Prerequisites.Residue p) red s).toAddSubgroup D volume)
    (hDm : MeasurableSet D) (hDf : volume D < ⊤)
    (hvol : volume.real D = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)|)
    (hshort : ∀ w ∈ red.ker,
      AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s w) < r → AbcTwoNinths.ExteriorE2.project s w = 0) :
    ∃ (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old I), P ⊆ Q ∧
      ⌈(Q.card : ℝ) * (volume : Measure (AbcTwoNinths.ExteriorE2.Coord I)).real (AbcTwoNinths.ExteriorE2.ball weight 0 (r / 2)) /
        (((p : ℝ) - 1) / (2 * |(s (.inl ()) : ℝ)|))⌉₊ ≤ P.card ∧
      ∀ i ∈ P, ∀ j ∈ P, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s (lift i j)) < r ∧
        red (lift i j) + AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0 := by
  have : Finite (AbcSubexp.Prerequisites.Residue p) :=
    inferInstanceAs (Finite ((ZMod p)ˣ ⧸ AbcTwoNinths.ExteriorE2.signs p))
  rw [← AbcSubexp.Prerequisites.native_normalization (p := p) (s (.inl ()))]
  apply existsCommonPairLifts (I := I) (G := AbcSubexp.Prerequisites.Residue p) (D := D) red s
    weight hw r Q (AbcSubexp.Prerequisites.freshLabel p)
  · exact hD
  · exact hDm
  · exact hDf
  · exact hshort
  · exact hvol

end AbcSubexp.TupleCounting
