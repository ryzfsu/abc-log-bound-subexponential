/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S7_Terminal.OldSupportCharacterHeight
public import AbcTwoNinths.Paper.S6_Diamond.LatticeTranslateOverlap
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Rational generators from signed residue corrections

The old correction and a fresh prime ratio determine a principal rational unit.
The same prime alphabet measures the height of all products of the generators.

## Main results
* `AbcSubexp.TupleCounting.rawPrimeGenerator`
* `AbcSubexp.TupleCounting.rawPrimeGenerator_spec`
* `AbcSubexp.TupleCounting.height_generatorProduct`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.TupleCounting


variable {O F : Type*} [Fintype O] [Fintype F] [DecidableEq F]

/-- The old exponents with fresh coordinates equal to the difference of two basis vectors. -/
def freshRatioExponents (w : O → ℤ) (j a : F) : AbcTwoNinths.ExteriorE2.Exponents (O ⊕ F) :=
  Multiplicative.ofAdd (Sum.elim w (Pi.single j 1 - Pi.single a 1))

private theorem evalRatio {G : Type*} [CommGroup G] (b : O ⊕ F → G)
    (w : O → ℤ) (j a : F) :
    AbcTwoNinths.ExteriorE2.eval b (freshRatioExponents w j a) =
      AbcTwoNinths.ExteriorE2.eval (fun i => b (.inl i)) (Multiplicative.ofAdd w) * (b (.inr j) / b (.inr a)) := by
  classical
  change (∏ i, b i ^ (Sum.elim w (Pi.single j 1 - Pi.single a 1) i)) = _
  rw [Fintype.prod_sum_type]
  congr 1
  have hs (k : F) : (∏ i : F, b (.inr i) ^ ((Pi.single k 1 : F → ℤ) i)) = b (.inr k) := by
    rw [Finset.prod_eq_single k]
    · simp
    · intro i _ hik
      simp [Pi.single_eq_of_ne hik]
    · simp
  change (∏ i, b (.inr i) ^ ((Pi.single j 1 : F → ℤ) i - (Pi.single a 1 : F → ℤ) i)) = _
  simp only [zpow_sub, ← div_eq_mul_inv, Finset.prod_div_distrib, hs]

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

omit [Fact (2 < p)] in
private theorem primeLabel_eq {ι : Type*} (b : ι → ℕ) (hb : ∀ i, (b i).Prime)
    (ha : ∀ i, p ≠ b i) (i : ι) :
    AbcSubexp.Prerequisites.freshLabel p (b i) = Additive.ofMul (QuotientGroup.mk' (AbcTwoNinths.ExteriorE2.signs p)
      (AbcTwoNinths.ExteriorE2.residueUnit b hb ha i)) := by
  have h : (b i : ZMod p) ≠ 0 := (AbcTwoNinths.ExteriorE2.residueUnit b hb ha i).ne_zero
  simp [AbcSubexp.Prerequisites.freshLabel, h, AbcTwoNinths.ExteriorE2.residueUnit]

omit [Fact (2 < p)] in
/-- An old correction that cancels the fresh label difference makes the
combined exponent vector a member of the signed residue kernel. -/
theorem freshRatioExponents_mem_kernel (b : O ⊕ F → ℕ)
    (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i)
    (w : O → ℤ) (j a : F) (hw :
      (AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.residue (fun i => b (.inl i))
        (fun i => hb (.inl i)) (fun i => ha (.inl i)))).toAdditive w +
        AbcSubexp.Prerequisites.freshLabel p (b (.inr j)) - AbcSubexp.Prerequisites.freshLabel p (b (.inr a)) = 0) :
    freshRatioExponents w j a ∈
      AbcTwoNinths.ExteriorE2.Kernel (AbcTwoNinths.ExteriorE2.residue b hb ha) := by
  change AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.eval (AbcTwoNinths.ExteriorE2.residueUnit b hb ha)) _ = 1
  rw [AbcTwoNinths.Diamond.reductionEval, evalRatio]
  rw [primeLabel_eq b hb ha (.inr j), primeLabel_eq b hb ha (.inr a)] at hw
  let r := AbcTwoNinths.ExteriorE2.residue (fun i => b (.inl i)) (fun i => hb (.inl i)) (fun i => ha (.inl i))
  change (AbcTwoNinths.ExteriorE2.reduction r (Multiplicative.ofAdd w) *
    QuotientGroup.mk' _ (AbcTwoNinths.ExteriorE2.residueUnit b hb ha (.inr j))) /
    QuotientGroup.mk' _ (AbcTwoNinths.ExteriorE2.residueUnit b hb ha (.inr a)) = 1 at hw
  dsimp only [r] at hw
  rw [AbcTwoNinths.ExteriorE2.residue, AbcTwoNinths.Diamond.reductionEval] at hw
  rw [mul_div_assoc] at hw
  exact hw

/-- A corrected ratio as a point of the signed residue kernel on the joint prime alphabet. -/
def rawPrimeGenerator (b : O ⊕ F → ℕ) (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i)
    (w : O → ℤ) (j a : F) (hw :
      (AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.residue (fun i => b (.inl i))
        (fun i => hb (.inl i)) (fun i => ha (.inl i)))).toAdditive w +
        AbcSubexp.Prerequisites.freshLabel p (b (.inr j)) - AbcSubexp.Prerequisites.freshLabel p (b (.inr a)) = 0) :
    AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha :=
  ⟨freshRatioExponents w j a, freshRatioExponents_mem_kernel b hb ha w j a hw⟩

private theorem principal_of_signed {ι : Type*} [Fintype ι] (b : ι → ℕ)
    (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i) (x : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha) :
    AbcTwoNinths.Basic.RatPrincipalUnit p (AbcTwoNinths.Diamond.character b hb ha x : ℚ) := by
  let z : ℚ := AbcTwoNinths.Diamond.character b hb ha x
  have hn : z ≠ 0 := (AbcTwoNinths.Diamond.character b hb ha x).ne_zero
  have h := AbcTwoNinths.ExteriorE2.signedLiftPrincipal b hb ha x
  have hu : ‖(z : ℚ_[p])‖ = 1 := AbcTwoNinths.Basic.principalNorm h
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hv : padicValRat p z = 0 := by
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_ratCast,
      ← zpow_zero (p : ℝ)] at hu
    have := (zpow_right_strictMono₀ hp).injective hu
    omega
  refine ⟨hn, hv, ?_⟩
  by_cases hz : z = 1
  · exact Or.inl hz
  · right
    have hl : ‖((z - 1 : ℚ) : ℚ_[p])‖ < 1 := by
      simpa [z, AbcTwoNinths.Diamond.character, AbcTwoNinths.Basic.PrincipalPrincipalUnitData] using h
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast sub_ne_zero.mpr hz),
      Padic.valuation_ratCast, ← zpow_zero (p : ℝ)] at hl
    have := (zpow_right_strictMono₀ hp).lt_iff_lt.mp hl
    change 0 < padicValRat p (z - 1)
    omega

private theorem signedValuationOutside {ι : Type*} [Fintype ι] (b : ι → ℕ)
    (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i) (x : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha)
    {q : ℕ} (hq : q.Prime) (hout : ∀ i, q ≠ b i) :
    padicValRat q (AbcTwoNinths.Diamond.character b hb ha x : ℚ) = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  have hm : padicValRat q (AbcTwoNinths.ExteriorE2.monomial b hb x.val : ℚ) = 0 := by
    change ((AbcTwoNinths.ExteriorE2.valuation q) (∏ i, AbcTwoNinths.ExteriorE2.ratUnit b hb i ^ x.val.toAdd i)).toAdd = 0
    rw [map_prod]
    change ∑ i, ((AbcTwoNinths.ExteriorE2.valuation q) (AbcTwoNinths.ExteriorE2.ratUnit b hb i ^ x.val.toAdd i)).toAdd = 0
    apply Finset.sum_eq_zero
    intro i _
    have : Fact (b i).Prime := ⟨hb i⟩
    change padicValRat q ((AbcTwoNinths.ExteriorE2.ratUnit b hb i ^ x.val.toAdd i : ℚˣ) : ℚ) = 0
    simp [Units.val_zpow_eq_zpow_val, AbcTwoNinths.ExteriorE2.ratUnit, padicValNat_primes (hout i)]
  rcases AbcTwoNinths.ExteriorE2.signCharacterization (AbcTwoNinths.ExteriorE2.residue b hb ha)
    (AbcTwoNinths.ExteriorE2.monomial b hb) x with ⟨_, hx⟩
  change padicValRat q (AbcTwoNinths.ExteriorE2.gammaStar _ _ _ : ℚ) = 0
  rw [hx]
  split <;> simpa using hm

/-- The rational character of a corrected pair has its signed formula and exact prime valuations. -/
theorem rawPrimeGenerator_spec (b : O ⊕ F → ℕ) (hb : ∀ i, (b i).Prime)
    (ha : ∀ i, p ≠ b i) (hinj : Function.Injective b)
    (w : O → ℤ) (j a : F) (hja : j ≠ a) (hw) :
    let x := rawPrimeGenerator b hb ha w j a hw
    let u : ℚ := AbcTwoNinths.Diamond.character b hb ha x
    let m : ℚ := AbcTwoNinths.ExteriorE2.monomial (fun i => b (.inl i)) (fun i => hb (.inl i))
      (Multiplicative.ofAdd w)
    (u = m * ((b (.inr j) : ℚ) / b (.inr a)) ∨ u = -(m * ((b (.inr j) : ℚ) / b (.inr a)))) ∧
    AbcTwoNinths.Basic.RatPrincipalUnit p u ∧ padicValRat (b (.inr j)) u = 1 ∧
    padicValRat (b (.inr a)) u = -1 ∧ (∀ i, padicValRat (b (.inl i)) u = w i) ∧
    ∀ q : ℕ, q.Prime → (∀ i, q ≠ b (.inl i)) → q ≠ b (.inr j) → q ≠ b (.inr a) →
      padicValRat q u = 0 := by
  classical
  intro x u m
  have hcoord (i : O ⊕ F) : padicValRat (b i) u = (freshRatioExponents w j a).toAdd i :=
    AbcTwoNinths.ExteriorE2.signedCoordinate b hb hinj ha x i
  have hsingle (i : F) : padicValRat (b (.inr i)) u =
      (Pi.single j 1 : F → ℤ) i - (Pi.single a 1 : F → ℤ) i := hcoord _
  have hm : (AbcTwoNinths.ExteriorE2.monomial b hb x.val : ℚ) = m * ((b (.inr j) : ℚ) / b (.inr a)) := by
    change ((AbcTwoNinths.ExteriorE2.eval (AbcTwoNinths.ExteriorE2.ratUnit b hb) (freshRatioExponents w j a) : ℚˣ) : ℚ) = _
    rw [evalRatio, Units.val_mul, Units.val_div_eq_div_val]
    rfl
  refine ⟨?_, principal_of_signed b hb ha x, by simpa [hja] using hsingle j,
    by simpa [hja.symm] using hsingle a, fun i => hcoord (.inl i), ?_⟩
  · obtain ⟨_, hx⟩ := AbcTwoNinths.ExteriorE2.signCharacterization
      (AbcTwoNinths.ExteriorE2.residue b hb ha) (AbcTwoNinths.ExteriorE2.monomial b hb) x
    change (AbcTwoNinths.ExteriorE2.gammaStar _ _ x : ℚ) = _ ∨ (AbcTwoNinths.ExteriorE2.gammaStar _ _ x : ℚ) = _
    rw [hx]
    split <;> simp [hm]
  · intro q hq ho hj ha'
    by_cases h : ∃ k, q = b (.inr k)
    · obtain ⟨k, rfl⟩ := h
      have hkj : k ≠ j := fun he => hj (he ▸ rfl)
      have hka : k ≠ a := fun he => ha' (he ▸ rfl)
      simpa [hkj, hka] using hsingle k
    · exact signedValuationOutside b hb ha x hq (fun i => by
        cases i with
        | inl k => exact ho k
        | inr k => exact fun he => h ⟨k, he⟩)

/-- The exact height of an arbitrary axial power times a finite product of signed generators. -/
theorem height_generatorProduct {ι J : Type*} [Fintype ι] [Fintype J] (b : ι → ℕ)
    (hb : ∀ i, (b i).Prime) (ha : ∀ i, p ≠ b i) (hinj : Function.Injective b)
    (s : AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha) (u : J → AbcTwoNinths.Diamond.LatticeSelectedPlaneData b hb ha) (c : ℤ) (y : J → ℤ) :
    AbcTwoNinths.Basic.rationalHeight ((AbcTwoNinths.Diamond.character b hb ha s : ℚ) ^ c * ∏ j, (AbcTwoNinths.Diamond.character b hb ha (u j) : ℚ) ^ y j) =
      AbcTwoNinths.Diamond.height b (fun i => c * s.val.toAdd i + ∑ j, y j * (u j).val.toAdd i) := by
  classical
  let z := s ^ c * ∏ j, u j ^ y j
  have hchar : (AbcTwoNinths.Diamond.character b hb ha z : ℚ) = _ :=
    show (AbcTwoNinths.Diamond.character b hb ha z : ℚ) = (AbcTwoNinths.Diamond.character b hb ha s : ℚ) ^ c *
      ∏ j, (AbcTwoNinths.Diamond.character b hb ha (u j) : ℚ) ^ y j by
      simp [z, map_prod]
  rw [← hchar]
  change Real.log (AbcTwoNinths.Terminal.rowHeightMax (AbcTwoNinths.Diamond.character b hb ha z : ℚ) : ℝ) = _
  rw [AbcTwoNinths.Terminal.logRowHeightMaxCharacter b hb ha hinj]
  congr 1
  funext i
  simp [z, toAdd_prod, zsmul_eq_mul, Finset.sum_apply]

end AbcSubexp.TupleCounting
