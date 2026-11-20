/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.ContactCoordinates
public import Subexp.S4_TupleCounting.ProjectedPrimeLattice
public import Subexp.S4_TupleCounting.WeightedShear
public import Subexp.Basic.ContactValuation
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Projection along the contact unit

The contact unit gives a primitive axis and a maximal roof coordinate.
Projection along this axis yields the separated lattice and the measure bound
of Section 4.

## Main results

* `AbcSubexp.TupleCounting.existsContactRoof`
* `AbcSubexp.TupleCounting.ContactRoof.separation`
* `AbcSubexp.TupleCounting.ContactRoof.fundamentalDomain`
-/

@[expose] public section

noncomputable section

open Real MeasureTheory
open scoped ENNReal

namespace AbcSubexp.TupleCounting

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)

local notation "base" => AbcTwoNinths.ExteriorE2.base c.source.num.natAbs c.source.den
local notation "prime" => AbcTwoNinths.ExteriorE2.prime c.source.num.natAbs c.source.den

variable [Fact c.prime.Prime] [Fact (2 < c.prime)]

local notation "res" => AbcTwoNinths.ExteriorE2.residue base prime (contactSupportAvoid c)
local notation "γ" => AbcTwoNinths.ExteriorE2.gammaStar res (AbcTwoNinths.ExteriorE2.monomial base prime)

omit [Fact c.prime.Prime] [Fact (2 < c.prime)] in
/-- Every old prime divides the triple product, in either order of the addends. -/
theorem contactSupportWithinProduct :
    c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors ⊆
      (t.a * t.b * t.c).primeFactors := by
  intro p hp
  have hprime : p.Prime := prime ⟨p, hp⟩
  by_contra hmiss
  have hnonzero := (ContactPrime.source_prime_support_iff c hprime).1 hp
  apply hnonzero
  apply c.valuation_eq_zero_of_fresh hprime
  intro hd
  have hR : 0 < t.radical := Finset.prod_pos (fun _ hq => (Nat.prime_of_mem_primeFactors hq).pos)
  apply hmiss
  have hmem := Nat.mem_primeFactors.mpr ⟨hprime, hd, hR.ne'⟩
  rw [AbcTwoNinths.Basic.Triple.radical, AbcTwoNinths.Basic.radical, Nat.primeFactors_prod_primeFactors] at hmem
  exact hmem

/-- A primitive contact axis with a maximal nonzero exponent coordinate. -/
structure ContactRoof where
  axis : AbcTwoNinths.ExteriorE2.Kernel res
  axis_eq : (γ axis : ℚ) = c.source
  primitive (k : ℕ) (v : AbcTwoNinths.ExteriorE2.Kernel res) : v ^ k = axis → k = 1
  roof : ContactSupport c
  roof_ne_zero : axis.val.toAdd roof ≠ 0
  roof_max (i : ContactSupport c) : (axis.val.toAdd i).natAbs ≤ (axis.val.toAdd roof).natAbs
  roof_lower : AbcTwoNinths.Basic.rationalHeight c.source / (2 * t.thirdLogRadical) ≤ |(axis.val.toAdd roof : ℝ)|

/-- The exact coefficient mass and the real contact inequality yield a
maximal nonzero roof with the required size. -/
theorem existsContactRoof (hε : 0 < ε) (hx : 0 < t.thirdLogRadical) :
    Nonempty (ContactRoof c) := by
  classical
  let e := Parameters.exponent ε
  have he : 0 < e := lt_min hε (by norm_num)
  have heCap : e ≤ 1 / 10 := min_le_right _ _
  have hHeight : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (half_pos he) (Real.exp_pos _)).trans_le c.axial_height_lower
  obtain ⟨s, hs, hsource, hprimitive⟩ := existsContactAxis c
  let S := c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
  have hm : 2 * (1 - e / 100) * AbcTwoNinths.Basic.rationalHeight c.source ≤
      ∑ i : ContactSupport c, ((s.val.toAdd i).natAbs : ℝ) * Real.log (i.val : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs, hs]
    rw [contactAxisMass c]
    have hContact := c.real_contact
    change |Real.log (|(c.source : ℝ)|)| ≤ e / 50 * AbcTwoNinths.Basic.rationalHeight c.source at hContact
    linarith only [hContact]
  have hNonempty : S.Nonempty := by
    by_contra h
    have hEmpty : IsEmpty (ContactSupport c) := ⟨fun i => h ⟨i.val, i.property⟩⟩
    let : IsEmpty (ContactSupport c) := hEmpty
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    have hfactor : 0 < 2 * (1 - e / 100) := by linarith
    exact (mul_pos hfactor hHeight).not_ge hm
  obtain ⟨j, hmax, hj⟩ := exists_large_roof_coordinate t
    (contactSupportWithinProduct c) hNonempty s.val.toAdd hHeight.le hx
    (E := e / 100) (by linarith) hm
  have hjne : s.val.toAdd j ≠ 0 := by
    intro h
    have hpos := div_pos hHeight (show 0 < 2 * t.thirdLogRadical by positivity)
    rw [h, Int.cast_zero, abs_zero] at hj
    exact hpos.not_ge hj
  exact ⟨⟨s, hsource, hprimitive, j, hjne, hmax, hj⟩⟩

namespace ContactRoof

variable {c} (a : ContactRoof c)

/-- The old coordinates other than the roof. -/
abbrev Transverse := {i : ContactSupport c // i ≠ a.roof}

/-- Put the roof at the distinguished coordinate of the projected lattice. -/
def index : Unit ⊕ a.Transverse ≃ ContactSupport c := by
  classical
  let : Unique {i : ContactSupport c // i = a.roof} :=
    ⟨⟨⟨a.roof, rfl⟩⟩, fun i => Subtype.ext i.property⟩
  exact (Equiv.sumCongr (Equiv.ofUnique Unit _) (Equiv.refl a.Transverse)).trans
    (Equiv.sumCompl (fun i : ContactSupport c => i = a.roof))

/-- The distinguished coordinate is sent to the roof prime. -/
theorem index_roof : a.index (.inl ()) = a.roof := by
  simp [index, Equiv.ofUnique, Equiv.sumCompl]
  exact (default : {i : ContactSupport c // i = a.roof}).property

/-- The remaining coordinates keep their prime labels. -/
theorem index_transverse (i : a.Transverse) : a.index (.inr i) = i.val := by
  simp [index, Equiv.sumCompl]

/-- The actual signed reduction on the old coordinates with the roof first. -/
def reduction : AbcTwoNinths.ExteriorE2.Old a.Transverse →+ AbcSubexp.Prerequisites.Residue c.prime :=
  AbcTwoNinths.ExteriorE2.residueLatticeReduction (base ∘ a.index) (fun i => prime (a.index i))
    (fun i => contactSupportAvoid c (a.index i))

/-- The valuation-axis vector on the reindexed coordinates. -/
def reindexedAxis : a.reduction.ker :=
  ⟨a.axis.val.toAdd ∘ a.index,
    (AbcTwoNinths.Diamond.reindexedReductionMemKernel a.index base prime (contactSupportAvoid c)
      (a.axis.val.toAdd ∘ a.index)).2
      (by simp [Function.comp_assoc])⟩

/-- Logarithmic weights on the transverse coordinates. -/
def weight (i : a.Transverse) : ℝ := Real.log (base (a.index (.inr i)) : ℝ)

/-- The character coordinates agree with the valuations of the contact source. -/
theorem axisCoordinate (i : ContactSupport c) : a.axis.val.toAdd i = padicValRat i.val c.source := by
  exact (AbcTwoNinths.ExteriorE2.signedCoordinate base prime Subtype.val_injective
    (contactSupportAvoid c) a.axis i).symm.trans
    (congrArg (padicValRat i.val) a.axis_eq)

/-- The roof appears as the nonzero first coordinate of the reindexed axis. -/
theorem reindexedAxisRoof : (a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) (.inl ()) =
    padicValRat a.roof.val c.source := by
  change a.axis.val.toAdd (a.index (.inl ())) = _
  rw [a.index_roof, a.axisCoordinate]

/-- Primitivity is preserved by reindexing into the additive residue kernel. -/
theorem reindexedPrimitive (k : ℤ) (u : a.reduction.ker)
    (hu : k • u = a.reindexedAxis) : IsUnit k := by
  let v : AbcTwoNinths.ExteriorE2.Kernel res :=
    ⟨Multiplicative.ofAdd ((u : AbcTwoNinths.ExteriorE2.Old a.Transverse) ∘ a.index.symm),
      (AbcTwoNinths.Diamond.reindexedReductionMemKernel a.index base prime (contactSupportAvoid c) _).1
        u.property⟩
  have hpow : v ^ k = a.axis := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun w : a.reduction.ker => (w : AbcTwoNinths.ExteriorE2.Old a.Transverse) (a.index.symm i)) hu
    change k * (u : AbcTwoNinths.ExteriorE2.Old a.Transverse) (a.index.symm i) =
      a.axis.val.toAdd (a.index (a.index.symm i)) at hi
    rw [a.index.apply_symm_apply] at hi
    change k * (u : AbcTwoNinths.ExteriorE2.Old a.Transverse) (a.index.symm i) = _
    exact hi
  let w := if k < 0 then v⁻¹ else v
  have hw : w ^ k.natAbs = v ^ k := by
    cases k <;> simp [w, inv_pow, zpow_negSucc]
  have hk := a.primitive k.natAbs w (hw.trans hpow)
  exact Int.isUnit_iff.mpr (by simpa using Int.natAbs_eq_iff.mp hk)

/-- The transverse lattice is separated at the Section 4 radius. -/
theorem separation (hε : 0 < ε) (hx : 12 ≤ t.thirdLogRadical)
    (honset : 112896 < (Parameters.exponent ε) ^ 4 * Real.log t.thirdLogRadical) :
    ∀ w ∈ a.reduction.ker,
      AbcTwoNinths.ExteriorE2.cost a.weight (AbcTwoNinths.ExteriorE2.project (a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) w) <
          2 * t.thirdLogRadical / Real.log t.thirdLogRadical →
        AbcTwoNinths.ExteriorE2.project (a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) w = 0 := by
  have he : 0 < Parameters.exponent ε := lt_min hε (by norm_num)
  have heCap : Parameters.exponent ε ≤ 1 / 10 := min_le_right _ _
  have hHeight : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (half_pos he) (Real.exp_pos _)).trans_le c.axial_height_lower
  have hRoof : 2 * Parameters.exponent ε * t.thirdLogRadical ≤ Real.log (c.prime : ℝ) := by
    have hp := c.log_lower
    nlinarith only [hp, mul_nonneg he.le (show 0 ≤ t.thirdLogRadical by linarith)]
  have hShare : 2 * Parameters.exponent ε * AbcTwoNinths.Basic.rationalHeight (γ a.axis : ℚ) ≤
      (padicValRat c.prime ((γ a.axis : ℚ) - 1) : ℝ) * Real.log (c.prime : ℝ) := by
    rw [a.axis_eq, c.depth_eq, Int.cast_natCast]
    exact c.depth_share.le
  have hCap : Real.log (AbcTwoNinths.Basic.rationalHeight (γ a.axis : ℚ)) ≤ 2 * t.thirdLogRadical := by
    rw [a.axis_eq]
    have h := Real.log_le_log hHeight (c.axial_height_upper.trans c.height_cap)
    rw [Real.log_exp] at h
    linarith
  exact projectedSeparation base prime (contactSupportAvoid c) a.index
    (show 5 ≤ c.prime from c.prime_gt_five.le) Subtype.val_injective a.axis
    (by rw [a.index_roof]; exact a.roof_ne_zero) he heCap hx hRoof hShare hCap honset

omit [Fact c.prime.Prime] [Fact (2 < c.prime)] in
private theorem heightPositive (hε : 0 < ε) : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
  (mul_pos (half_pos (lt_min hε (by norm_num))) (Real.exp_pos _)).trans_le c.axial_height_lower

private theorem labelCard : (Nat.card (AbcSubexp.Prerequisites.Residue c.prime) : ℝ) = ((c.prime : ℝ) - 1) / 2 :=
  AbcTwoNinths.ExteriorE2.labelCardReal c.prime

private theorem reindexedRoofLower :
    AbcTwoNinths.Basic.rationalHeight c.source / (2 * t.thirdLogRadical) ≤ |((a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) (.inl ()) : ℝ)| := by
  change AbcTwoNinths.Basic.rationalHeight c.source / (2 * t.thirdLogRadical) ≤ |(a.axis.val.toAdd (a.index (.inl ())) : ℝ)|
  rw [a.index_roof]
  exact a.roof_lower

set_option linter.defProp false in
/-- Specialize the projected-domain bound with the measure instances inferred
from the generic result. -/
@[no_expose] def fundamentalDomainProof (hε : 0 < ε) (hx : 0 < t.thirdLogRadical) :=
  exists_projected_domain_mass_le (I := a.Transverse) (G := AbcSubexp.Prerequisites.Residue c.prime)
    (p := c.prime) (h := AbcTwoNinths.Basic.rationalHeight c.source) (x := t.thirdLogRadical)
    a.reduction (labelCard (c := c)) a.reindexedAxis hx (heightPositive (c := c) hε)
    a.reindexedRoofLower a.reindexedPrimitive

/-- The projected residue tori have total measure at most `xp/h`. -/
theorem fundamentalDomain (hε : 0 < ε) (hx : 0 < t.thirdLogRadical) :
    type_of% (a.fundamentalDomainProof hε hx) :=
  a.fundamentalDomainProof hε hx

/-- The transverse logarithmic weights fit into the old prime budget. -/
theorem weightBudget :
    (∀ i, 0 ≤ a.weight i) ∧ ∑ i, a.weight i ≤ 3 * t.thirdLogRadical := by
  classical
  have hPos (i : ContactSupport c) : 0 ≤ Real.log (i.val : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (prime i).one_le)
  have hWeight (i : a.Transverse) : a.weight i = Real.log (i.val.val : ℝ) := by
    unfold weight AbcTwoNinths.ExteriorE2.base
    rw [a.index_transverse]
  refine ⟨fun i => hWeight i ▸ hPos i.val, ?_⟩
  rw [show (∑ i, a.weight i) = ∑ i : a.Transverse, Real.log (i.val.val : ℝ) by
    exact Finset.sum_congr rfl (fun i _ => hWeight i)]
  have hSub := Fintype.sum_subtype_add_sum_subtype (fun i : ContactSupport c => i ≠ a.roof)
    (fun i => Real.log (i.val : ℝ))
  have hIncl : (∑ i : a.Transverse, Real.log (i.val.val : ℝ)) ≤
      ∑ i : ContactSupport c, Real.log (i.val : ℝ) := by
    rw [← hSub]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hPos i.val))
  refine hIncl.trans ?_
  change (∑ i : ↥(c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors),
    Real.log (i.val : ℝ)) ≤ 3 * t.thirdLogRadical
  rw [Finset.sum_coe_sort _ (fun q : ℕ => Real.log (q : ℝ))]
  exact AbcTwoNinths.Selection.logWeightLeThreeX t (contactSupportWithinProduct c)

end ContactRoof

end AbcSubexp.TupleCounting
