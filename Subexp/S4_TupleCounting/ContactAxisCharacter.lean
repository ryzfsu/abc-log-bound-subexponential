/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.ContactCluster
public import AbcTwoNinths.Paper.S6_Diamond.PivotFirstCoordinates

/-!
# The signed character of the contact axis

The contact axis on the old prime support has the prescribed integer coordinates
and its rational character is the contact source.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting.ContactRoof


private theorem character_eq_of_base_eq {I : Type*} [Fintype I]
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)] {b b' : I → ℕ}
    {hb : ∀ i, (b i).Prime} {ha : ∀ i, p ≠ b i}
    {hb' : ∀ i, (b' i).Prime} {ha' : ∀ i, p ≠ b' i}
    (hbase : b = b') (w : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha) (w' : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b' hb' ha')
    (hw : w.val.toAdd = w'.val.toAdd) : AbcTwoNinths.Diamond.character b hb ha w = AbcTwoNinths.Diamond.character b' hb' ha' w' := by
  subst b'
  exact congrArg (AbcTwoNinths.Diamond.character b hb ha) (Subtype.ext (Multiplicative.toAdd.injective hw))

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}
variable [Fact c.prime.Prime] [Fact (2 < c.prime)] (a : ContactRoof c)

local notation "S" => c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
local notation "b" => oldSupportPrime S a.roof.val
local notation "base" => AbcTwoNinths.ExteriorE2.base c.source.num.natAbs c.source.den
local notation "prime" => AbcTwoNinths.ExteriorE2.prime c.source.num.natAbs c.source.den

/-- The signed residue lattice point defined by the old-support contact axis. -/
def tallSignedAxis (hp : ∀ i, (b i).Prime) (ha : ∀ i, c.prime ≠ b i) : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hp ha := by
  refine ⟨Multiplicative.ofAdd a.tallAxis.val, ?_⟩
  change a.tallAxis.val ∈ (AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.residue b hp ha)).toAdditive.ker
  rw [← a.tallResidue_eq hp ha]
  exact a.tallAxis.property

/-- Its signed integer coordinates are the coordinates of the contact axis. -/
@[simp] theorem tallSignedAxis_apply (hp : ∀ i, (b i).Prime) (ha : ∀ i, c.prime ≠ b i)
    (i : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) :
    (a.tallSignedAxis hp ha).val.toAdd i = a.tallAxis.val i := rfl

/-- The signed character of the old-support axis recovers the contact source. -/
theorem tallSignedAxis_character (hp : ∀ i, (b i).Prime) (ha : ∀ i, c.prime ≠ b i) :
    (AbcTwoNinths.Diamond.character b hp ha (a.tallSignedAxis hp ha) : ℚ) = c.source := by
  let oldAxis := AbcTwoNinths.Diamond.reindexLattice a.tallIndex base prime (contactSupportAvoid c) a.axis
  have hchar : AbcTwoNinths.Diamond.character (base ∘ a.tallIndex) (fun i => prime (a.tallIndex i))
      (fun i => contactSupportAvoid c (a.tallIndex i)) oldAxis =
        AbcTwoNinths.Diamond.character base prime (contactSupportAvoid c) a.axis :=
    AbcTwoNinths.Diamond.reindexCharacter a.tallIndex base prime (contactSupportAvoid c) a.axis
  have heq : AbcTwoNinths.Diamond.character (base ∘ a.tallIndex) (fun i => prime (a.tallIndex i))
      (fun i => contactSupportAvoid c (a.tallIndex i)) oldAxis =
        AbcTwoNinths.Diamond.character b hp ha (a.tallSignedAxis hp ha) :=
    character_eq_of_base_eq (funext a.tallIndexPrime) oldAxis (a.tallSignedAxis hp ha) rfl
  rw [← heq, hchar]
  exact a.axis_eq

end AbcSubexp.TupleCounting.ContactRoof
