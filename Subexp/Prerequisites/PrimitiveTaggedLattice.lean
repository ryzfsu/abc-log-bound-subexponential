/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice

/-!
# Tagged patches in the projected residue lattice

Cosets of the image of the old prime coordinates label the projected
fundamental domains. Counting the tags converts the covolume into a measure
on their disjoint union. The separation hypothesis makes each ball project
with its full volume into the corresponding domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set AbcTwoNinths.ExteriorE2
open scoped ENNReal Pointwise

namespace AbcSubexp.Prerequisites

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The residue image partitions the label group into tags. -/
abbrev Tag {G : Type*} [AddCommGroup G] (red : Old I →+ G) := G ⧸ red.range

/-- Assign the residue image coset containing a label. -/
def tag {G : Type*} [AddCommGroup G] (red : Old I →+ G) : G →+ Tag red :=
  QuotientAddGroup.mk' red.range

/-- Use the discrete measurable space on the set of tags. -/
instance tagMeasurable {G : Type*} [AddCommGroup G] (red : Old I →+ G) :
    MeasurableSpace (Tag red) := ⊤

/-- A single tag is measurable in the discrete tag space. -/
instance tagMeasurableSingleton {G : Type*} [AddCommGroup G] (red : Old I →+ G) :
    MeasurableSingletonClass (Tag red) :=
  ⟨fun _ => trivial⟩

omit [DecidableEq I] in
/-- One tag per old-residue coset, with the unweighted coordinate measure on each. -/
theorem normalization {G : Type*} [AddCommGroup G] [Finite G] (red : Old I →+ G)
    {D : Set (Coord I)} {k : ℤ} (hD : volume D < ⊤)
    (hvol : volume.real D = (Nat.card red.range : ℝ) / |(k : ℝ)|) :
    (taggedMeasure (C := Tag red) D volume).real Set.univ =
      (Nat.card G : ℝ) / |(k : ℝ)| := by
  classical
  let : Fintype (Tag red) := Fintype.ofFinite _
  have hi := red.range.index_mul_card
  rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card (α := Tag red)] at hi
  rw [measureReal_def, taggedMeasureUniv hD, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ← measureReal_def, hvol, ← mul_div_assoc]
  exact congrArg (fun t : ℝ => t / |(k : ℝ)|) (by exact_mod_cast hi)

/-- Signed nonzero residue classes at the contact prime, written additively. -/
abbrev Residue (p : ℕ) := Additive (AbcTwoNinths.ExteriorE2.Label p)

/-- The complete projected model for one actual signed prime residue map. -/
theorem fundamental_of_primitive {G : Type*} [AddCommGroup G] [Finite G]
    (red : Old I →+ G) (s : red.ker) (hs : (s : Old I) (.inl ()) ≠ 0)
    (primitive : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a) :
    ∃ D : Set (Coord I), IsAddFundamentalDomain (projected red (s : Old I)).toAddSubgroup D volume ∧
      MeasurableSet D ∧ volume D < ⊤ ∧
      volume.real D = (Nat.card red.range : ℝ) / |((s : Old I) (.inl ()) : ℝ)| ∧
      (taggedMeasure (C := Tag red) D volume).real Set.univ =
        (Nat.card G : ℝ) / |((s : Old I) (.inl ()) : ℝ)| := by
  have hne : s ≠ 0 := fun he => hs (by rw [he]; rfl)
  obtain ⟨b, hb⟩ := existsSourceBasis red s hne primitive
  obtain ⟨D, hD, hDm, hDf, hvol⟩ :=
    fundamentalData red s hs b (congrArg Subtype.val hb)
  exact ⟨D, hD, hDm, hDf, hvol, normalization red hDf hvol⟩

/-- The mass on the actual quotient tags is the signed residue cardinality
divided by the absolute roof coordinate. -/
theorem native_normalization {p : ℕ} [Fact p.Prime] [Fact (2 < p)] (k : ℤ) :
    (Nat.card (Residue p) : ℝ) / |(k : ℝ)| = ((p : ℝ) - 1) / (2 * |(k : ℝ)|) := by
  change (Nat.card (AbcTwoNinths.ExteriorE2.Label p) : ℝ) / _ = _
  rw [labelCardReal, div_div, mul_comm (2 : ℝ)]

omit [Fintype I] [DecidableEq I] in
/-- Coset representatives and old-coordinate lifts for a family of labels. -/
theorem choose_centers {G : Type*} [AddCommGroup G] (red : Old I →+ G) (q : ℕ → G) :
    ∃ (rep : Tag red → G) (center : ℕ → Old I),
      ∀ j, q j = rep (tag red (q j)) + red (center j) := by
  classical
  have hs : Function.Surjective (tag red) := QuotientAddGroup.mk'_surjective red.range
  choose rep hrep using hs
  have hx (j : ℕ) : ∃ a : Old I, red a = q j - rep (tag red (q j)) := by
    apply AddMonoidHom.mem_range.mp
    apply (QuotientAddGroup.eq_zero_iff (N := red.range) _).mp
    change tag red (q j - rep (tag red (q j))) = 0
    rw [map_sub, hrep, sub_self]
  choose center hcenter using hx
  refine ⟨rep, center, fun j => ?_⟩
  rw [hcenter]
  abel

/-- A fresh prime below the contact prime has its actual signed residue. -/
noncomputable def freshLabel (p : ℕ) [Fact p.Prime] (q : ℕ) : Residue p :=
  Additive.ofMul (if h : (q : ZMod p) = 0 then 1
    else QuotientGroup.mk' (AbcTwoNinths.ExteriorE2.signs p) (Units.mk0 (q : ZMod p) h))

/-- A prime below the contact prime lifts to a unit representing its label. -/
theorem freshLabel_nonzero {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q < p) :
    ∃ u : (ZMod p)ˣ, (u : ZMod p) = q ∧
      freshLabel p q = Additive.ofMul (QuotientGroup.mk' (AbcTwoNinths.ExteriorE2.signs p) u) := by
  have h : (q : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hd => (not_le_of_gt hqp) (Nat.le_of_dvd hq.pos hd)
  exact ⟨Units.mk0 _ h, rfl, by simp [freshLabel, h]⟩

omit [DecidableEq I] in
/-- The projected lattice is a countable image of the integer kernel. -/
theorem projected_countable {G : Type*} [AddCommGroup G] (red : Old I →+ G) (s : Old I) :
    Countable (projected red s).toAddSubgroup := by
  let l (w : red.ker) : (projected red s).toAddSubgroup :=
    ⟨project s w, (memProjected red s _).mpr ⟨w, w.property, rfl⟩⟩
  have hl : Function.Surjective l := by
    rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := (memProjected red s y).mp hy
    exact ⟨⟨w, hw⟩, rfl⟩
  exact hl.countable

omit [DecidableEq I] in
/-- A wrapped ball in a single tag has the volume of the original ball. -/
theorem native_component_mass {G : Type*} [AddCommGroup G] (red : Old I →+ G)
    (s : Old I) (weight : I → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (center : Coord I) (r : ℝ) (c : Tag red) {D : Set (Coord I)}
    (hD : IsAddFundamentalDomain (projected red s).toAddSubgroup D volume)
    (hDm : MeasurableSet D) (hDf : volume D < ⊤)
    (hshort : ∀ w ∈ red.ker, cost weight (project s w) < r → project s w = 0) :
    (taggedMeasure D volume).real
      ({c} ×ˢ wrapped (L := (projected red s).toAddSubgroup) D (ball weight center (r / 2))) =
    (volume : Measure (Coord I)).real (ball weight 0 (r / 2)) := by
  have : Countable (projected red s).toAddSubgroup := projected_countable red s
  rw [measureReal_def,
    componentMass hD hDm hDf (ballOpen weight center (r / 2)).measurableSet
      (ballOrbitInjective red s weight hw center r hshort), ← measureReal_def]
  exact ballMassEq weight center (r / 2)

end AbcSubexp.Prerequisites
