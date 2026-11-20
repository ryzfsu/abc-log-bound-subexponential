/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.LatticeTranslateOverlap
public import Mathlib.MeasureTheory.Integral.Average
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# A common ball for auxiliary primes

Integration of the covering multiplicity gives the single-center lower bound in Section 4.
The tagged torus normalization and patch mass use the projected residue lattice.

## Main results
* `AbcSubexp.TupleCounting.existsCommonPatchFamily`
* `AbcSubexp.TupleCounting.existsCommonTaggedBall`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace AbcSubexp.TupleCounting

/-- A point belongs to at least the ceiling of the mean number of covering patches. -/
theorem existsCommonPatchFamily {X : Type*} [Nonempty X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Q : Finset ℕ) (A : ℕ → Set X)
    (hA : ∀ q ∈ Q, MeasurableSet (A q)) (W : ℝ) (hmass : ∀ q ∈ Q, μ.real (A q) = W) :
    ∃ (z : X) (P : Finset ℕ), P ⊆ Q ∧
      ⌈(Q.card : ℝ) * W / μ.real univ⌉₊ ≤ P.card ∧ ∀ q ∈ P, z ∈ A q := by
  classical
  by_cases hμ : μ = 0
  · exact ⟨Classical.arbitrary X, ∅, Finset.empty_subset _, by simp [hμ], by simp⟩
  have hI (q : ℕ) (hq : q ∈ Q) :
      Integrable ((A q).indicator (1 : X → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator (hA q hq)
  obtain ⟨z, hz⟩ := exists_average_le hμ
    (show Integrable (AbcTwoNinths.ExteriorE2.multiplicity Q A) μ from integrable_finsetSum Q hI)
  let P := Q.filter (fun q => z ∈ A q)
  refine ⟨z, P, Finset.filter_subset _ _, Nat.ceil_le.mpr ?_, fun q hq => (Finset.mem_filter.mp hq).2⟩
  have hint : (∫ x, AbcTwoNinths.ExteriorE2.multiplicity Q A x ∂μ) = (Q.card : ℝ) * W := by
    unfold AbcTwoNinths.ExteriorE2.multiplicity
    rw [integral_finsetSum Q hI]
    calc
      _ = ∑ _q ∈ Q, W :=
        Finset.sum_congr rfl fun q hq => (integral_indicator_one (hA q hq)).trans (hmass q hq)
      _ = _ := by simp
  have hcard : AbcTwoNinths.ExteriorE2.multiplicity Q A z = (P.card : ℝ) := by
    simp [AbcTwoNinths.ExteriorE2.multiplicity, P, Set.indicator_apply, Finset.sum_boole]
  simpa only [average_eq, smul_eq_mul, hint, hcard, div_eq_inv_mul] using hz


/-- A single tagged torus point lies in all patches of the averaged family. -/
theorem existsCommonTaggedBall {I G : Type*} [Fintype I] [AddCommGroup G] [Finite G]
    (red : AbcTwoNinths.ExteriorE2.Old I →+ G) (s : AbcTwoNinths.ExteriorE2.Old I) (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (r : ℝ) (Q : Finset ℕ) (label : ℕ → G) (center : ℕ → AbcTwoNinths.ExteriorE2.Coord I) {D : Set (AbcTwoNinths.ExteriorE2.Coord I)}
    (hD : IsAddFundamentalDomain (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup D volume)
    (hDm : MeasurableSet D) (hDf : volume D < ⊤)
    (hshort : ∀ w ∈ red.ker, AbcTwoNinths.ExteriorE2.cost weight (AbcTwoNinths.ExteriorE2.project s w) < r → AbcTwoNinths.ExteriorE2.project s w = 0)
    (hvol : volume.real D = (Nat.card red.range : ℝ) / |(s (.inl ()) : ℝ)|) :
    ∃ (z : AbcSubexp.Prerequisites.Tag red × AbcTwoNinths.ExteriorE2.Coord I) (P : Finset ℕ), P ⊆ Q ∧
      ⌈(Q.card : ℝ) * (volume : Measure (AbcTwoNinths.ExteriorE2.Coord I)).real (AbcTwoNinths.ExteriorE2.ball weight 0 (r / 2)) /
        ((Nat.card G : ℝ) / |(s (.inl ()) : ℝ)|)⌉₊ ≤ P.card ∧
      ∀ q ∈ P, z.1 = AbcSubexp.Prerequisites.tag red (label q) ∧
        z.2 ∈ AbcTwoNinths.ExteriorE2.wrapped (L := (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup) D (AbcTwoNinths.ExteriorE2.ball weight (center q) (r / 2)) := by
  classical
  let L := (AbcTwoNinths.ExteriorE2.projected red s).toAddSubgroup
  let μ : Measure (AbcSubexp.Prerequisites.Tag red × AbcTwoNinths.ExteriorE2.Coord I) := AbcTwoNinths.ExteriorE2.taggedMeasure D volume
  let A (q : ℕ) : Set (AbcSubexp.Prerequisites.Tag red × AbcTwoNinths.ExteriorE2.Coord I) :=
    {AbcSubexp.Prerequisites.tag red (label q)} ×ˢ AbcTwoNinths.ExteriorE2.wrapped (L := L) D (AbcTwoNinths.ExteriorE2.ball weight (center q) (r / 2))
  have : Countable L := AbcSubexp.Prerequisites.projected_countable red s
  let _ : Fintype (AbcSubexp.Prerequisites.Tag red) := Fintype.ofFinite _
  have : IsFiniteMeasure μ := ⟨by
    change AbcTwoNinths.ExteriorE2.taggedMeasure (C := AbcSubexp.Prerequisites.Tag red) D volume univ < ⊤
    rw [AbcTwoNinths.ExteriorE2.taggedMeasureUniv hDf]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hDf⟩
  obtain ⟨z, P, hsub, hcard, hmem⟩ := existsCommonPatchFamily μ Q A
    (fun q _ => (measurableSet_singleton _).prod
      (AbcTwoNinths.ExteriorE2.measurableWrapped (L := L) hDm (AbcTwoNinths.ExteriorE2.ballOpen weight (center q) _).measurableSet)) _
    (fun q _ => AbcSubexp.Prerequisites.native_component_mass red s weight hw (center q) r (AbcSubexp.Prerequisites.tag red (label q))
      hD hDm hDf hshort)
  rw [show μ.real univ = _ from AbcSubexp.Prerequisites.normalization red hDf hvol] at hcard
  exact ⟨z, P, hsub, hcard, hmem⟩

end AbcSubexp.TupleCounting
