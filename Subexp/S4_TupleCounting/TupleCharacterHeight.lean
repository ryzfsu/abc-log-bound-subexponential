/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S4_TupleCounting.RationalPrimeGenerators
public import Subexp.S4_TupleCounting.ShortTupleCount
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Height of a tuple character

The signed axial unit keeps its value when extended by zero fresh exponents.
The augmented exponent vector computes the height of every tuple product.

## Main results
* `AbcSubexp.TupleCounting.ratHeight_tupleCharacter`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.TupleCounting


variable {O F : Type*} [Fintype O] [Fintype F]

/-- In a prime product, zero exponents on the fresh coordinates leave only the old factors. -/
theorem eval_extendOld {G : Type*} [CommGroup G] (b : O ⊕ F → G) (v : O → ℤ) :
    AbcTwoNinths.ExteriorE2.eval b (Multiplicative.ofAdd (Sum.elim v (fun _ => 0))) =
      AbcTwoNinths.ExteriorE2.eval (fun i => b (.inl i)) (Multiplicative.ofAdd v) := by
  change (∏ i, b i ^ Sum.elim v (fun _ => 0) i) = ∏ i, b (.inl i) ^ v i
  rw [Fintype.prod_sum_type]
  simp

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

/-- Extend an old signed-kernel element by zero on all fresh coordinates. -/
def extendOldAxis (b : O ⊕ F → ℕ) (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i)
    (v : AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => b (.inl i)) (fun i => hb (.inl i)) (fun i => ha (.inl i))) :
    AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha := by
  refine ⟨Multiplicative.ofAdd (Sum.elim v.val.toAdd (fun _ => 0)), ?_⟩
  have hr : AbcTwoNinths.ExteriorE2.residue b hb ha
      (Multiplicative.ofAdd (Sum.elim v.val.toAdd (fun _ => 0))) =
      AbcTwoNinths.ExteriorE2.residue (fun i => b (.inl i)) (fun i => hb (.inl i))
        (fun i => ha (.inl i)) v.val :=
    eval_extendOld (AbcTwoNinths.ExteriorE2.residueUnit b hb ha) v.val.toAdd
  change QuotientGroup.mk' _ (AbcTwoNinths.ExteriorE2.residue b hb ha _) = 1
  rw [hr]
  exact v.property

/-- The signed character retains the original value of the axial element. -/
theorem character_extendOldAxis (b : O ⊕ F → ℕ) (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i)
    (v : AbcTwoNinths.Diamond.LatticeSelectedPlaneData (fun i => b (.inl i)) (fun i => hb (.inl i)) (fun i => ha (.inl i))) :
    AbcTwoNinths.Diamond.character b hb ha (extendOldAxis b hb ha v) =
      AbcTwoNinths.Diamond.character (fun i => b (.inl i)) (fun i => hb (.inl i)) (fun i => ha (.inl i)) v := by
  let s := extendOldAxis b hb ha v
  have hr : AbcTwoNinths.ExteriorE2.residue b hb ha s.val =
      AbcTwoNinths.ExteriorE2.residue (fun i => b (.inl i)) (fun i => hb (.inl i))
        (fun i => ha (.inl i)) v.val :=
    eval_extendOld (AbcTwoNinths.ExteriorE2.residueUnit b hb ha) v.val.toAdd
  have hm : AbcTwoNinths.ExteriorE2.monomial b hb s.val =
      AbcTwoNinths.ExteriorE2.monomial (fun i => b (.inl i)) (fun i => hb (.inl i)) v.val :=
    eval_extendOld (AbcTwoNinths.ExteriorE2.ratUnit b hb) v.val.toAdd
  change AbcTwoNinths.ExteriorE2.signUnit (AbcTwoNinths.ExteriorE2.residue b hb ha) s *
    AbcTwoNinths.ExteriorE2.monomial b hb s.val = _
  simp only [AbcTwoNinths.Diamond.character, AbcTwoNinths.ExteriorE2.gammaStar, MonoidHom.coe_mk, OneHom.coe_mk,
    AbcTwoNinths.ExteriorE2.signUnit, hr, hm]

variable {Q : Type*} {n : ℕ} {ε : ℝ} {tr : AbcTwoNinths.Basic.Triple} (c : Contact ε tr)

/-- The actual axial source and corrected prime ratios have exactly the height
of their integral tuple combination. -/
theorem ratHeight_tupleCharacter [Fact c.prime.Prime] [Fact (2 < c.prime)]
    (q : O → ℕ) (prime : Q → ℕ) (t : Q × (Fin n → Q))
    (hb : ∀ i, (tuplePrimes q prime t i).Prime) (ha : ∀ i, c.prime ≠ tuplePrimes q prime t i)
    (hinj : Function.Injective (tuplePrimes q prime t))
    (v : AbcTwoNinths.Diamond.LatticeSelectedPlaneData q (fun i => hb (.inl i)) (fun i => ha (.inl i)))
    (hsource : (AbcTwoNinths.Diamond.character q (fun i => hb (.inl i)) (fun i => ha (.inl i)) v : ℚ) = c.source)
    (lift : Q → Q → O → ℤ)
    (hlift : ∀ j : Fin n,
      (AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.residue q
        (fun i => hb (.inl i)) (fun i => ha (.inl i)))).toAdditive (lift (t.2 j) t.1) +
        AbcSubexp.Prerequisites.freshLabel c.prime (prime (t.2 j)) -
        AbcSubexp.Prerequisites.freshLabel c.prime (prime t.1) = 0)
    (a : ℤ) (y : Fin n → ℤ) :
    let b := tuplePrimes q prime t
    let u := fun j : Fin n =>
      rawPrimeGenerator b hb ha (lift (t.2 j) t.1) (.inr j) (.inl ()) (hlift j)
    AbcTwoNinths.Basic.rationalHeight (c.source ^ a * ∏ j, (AbcTwoNinths.Diamond.character b hb ha (u j) : ℚ) ^ y j) =
      AbcTwoNinths.Diamond.height b (tupleCombination v.val.toAdd lift t a y) := by
  classical
  intro b u
  let s := extendOldAxis b hb ha v
  have hs : (AbcTwoNinths.Diamond.character b hb ha s : ℚ) = c.source :=
    (congrArg (fun z : ℚˣ => (z : ℚ)) (character_extendOldAxis b hb ha v)).trans hsource
  rw [← hs, height_generatorProduct b hb ha hinj s u a y]
  congr 1
  funext i
  rcases i with i | (i | i)
  · simp [s, u, extendOldAxis, rawPrimeGenerator, freshRatioExponents, tupleCombination,
      oldCombination, Finset.sum_apply, zsmul_eq_mul]
  · cases i
    simp [s, u, extendOldAxis, rawPrimeGenerator, freshRatioExponents, tupleCombination,
      Finset.sum_neg_distrib]
  · simp [s, u, extendOldAxis, rawPrimeGenerator, freshRatioExponents, tupleCombination,
      Pi.single_apply]

end AbcSubexp.TupleCounting
