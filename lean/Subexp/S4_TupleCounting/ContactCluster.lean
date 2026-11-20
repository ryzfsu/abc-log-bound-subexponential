/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ContactValuation
public import Subexp.S4_TupleCounting.ContactProjection
public import Subexp.S4_TupleCounting.TallPrimeFamily
public import AbcTwoNinths.Paper.S7_Terminal.OldSupportCharacterHeight
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Auxiliary prime families for the contact axis

The actual contact roof and its signed residue character supply the growing
family of Section 4. The onset is uniform in the triple and its old support.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.TupleCounting

open Real Filter

namespace ContactRoof

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}
variable [Fact c.prime.Prime] [Fact (2 < c.prime)] (a : ContactRoof c)

local notation "S" => c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
local notation "base" => AbcTwoNinths.ExteriorE2.base c.source.num.natAbs c.source.den
local notation "prime" => AbcTwoNinths.ExteriorE2.prime c.source.num.natAbs c.source.den

/-- Identify the erased prime support with the transverse coordinates. -/
def transverseEquiv : AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val ≃ a.Transverse where
  toFun i :=
    ⟨⟨i.val, (Finset.mem_erase.mp i.property).2⟩,
      fun h => (Finset.mem_erase.mp i.property).1 (congrArg Subtype.val h)⟩
  invFun i := ⟨i.val.val, Finset.mem_erase.mpr
    ⟨fun h => i.property (Subtype.ext h), i.val.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Keep the roof coordinate and reindex the remaining coordinates by the erased support. -/
def coordinateEquiv : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val ≃ Unit ⊕ a.Transverse :=
  Equiv.sumCongr (Equiv.refl Unit) a.transverseEquiv

/-- Index the contact coordinates by the roof and the erased prime support. -/
def tallIndex : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val ≃ ContactSupport c :=
  a.coordinateEquiv.trans a.index

/-- The prime at an index is its value in the old support. -/
theorem tallIndexPrime (i : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) :
    base (a.tallIndex i) = oldSupportPrime S a.roof.val i := by
  rcases i with i | i
  · cases i
    change base (a.index (.inl ())) = a.roof.val
    rw [a.index_roof]
    rfl
  · change base (a.index (.inr (a.transverseEquiv i))) = i.val
    rw [a.index_transverse]
    rfl

/-- The unit character on the old support in the roof-first enumeration. -/
def tallResidue : AbcTwoNinths.ExteriorE2.Exponents (Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) →* (ZMod c.prime)ˣ :=
  AbcTwoNinths.ExteriorE2.residue (base ∘ a.tallIndex) (fun i => prime (a.tallIndex i))
    (fun i => contactSupportAvoid c (a.tallIndex i))

/-- The character can be written directly with the primes in the erased support. -/
theorem tallResidue_eq (hp : ∀ i, (oldSupportPrime S a.roof.val i).Prime)
    (ha : ∀ i, c.prime ≠ oldSupportPrime S a.roof.val i) :
    a.tallResidue = AbcTwoNinths.ExteriorE2.residue (oldSupportPrime S a.roof.val) hp ha := by
  unfold tallResidue
  congr 1
  exact funext a.tallIndexPrime

/-- Roof-first reindexing preserves membership in the signed residue kernel. -/
theorem tallKernel_iff {w : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val)} :
    w ∈ (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker ↔
      Multiplicative.ofAdd (w ∘ a.tallIndex.symm) ∈
        AbcTwoNinths.ExteriorE2.Kernel (AbcTwoNinths.ExteriorE2.residue base prime (contactSupportAvoid c)) :=
  AbcTwoNinths.Diamond.reindexedReductionMemKernel a.tallIndex base prime (contactSupportAvoid c) w

/-- The actual valuation axis in the kernel of the roof-first unit character. -/
def tallAxis : (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker :=
  ⟨a.axis.val.toAdd ∘ a.tallIndex, a.tallKernel_iff.mpr (by simp [Function.comp_assoc])⟩

/-- The axis coordinates are the valuations of the contact unit. -/
theorem tallAxisCoordinate (i : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) :
    a.tallAxis.val i =
      padicValRat (oldSupportPrime S a.roof.val i) c.source := by
  change a.axis.val.toAdd (a.tallIndex i) = _
  rw [a.axisCoordinate, ← a.tallIndexPrime]
  rfl

private theorem toRoofKernel {w : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val)}
    (hw : w ∈ (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker) :
    w ∘ a.coordinateEquiv.symm ∈ a.reduction.ker := by
  apply (AbcTwoNinths.Diamond.reindexedReductionMemKernel a.index base prime (contactSupportAvoid c) _).2
  exact a.tallKernel_iff.mp hw

private theorem tallPrimitive (n : ℤ)
    (w : (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker)
    (hn : n • w = a.tallAxis) : IsUnit n := by
  let u : a.reduction.ker := ⟨w.val ∘ a.coordinateEquiv.symm,
    a.toRoofKernel w.property⟩
  apply a.reindexedPrimitive n u
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker =>
    z.val (a.coordinateEquiv.symm i)) hn
  change n * w.val (a.coordinateEquiv.symm i) =
    a.axis.val.toAdd (a.tallIndex (a.coordinateEquiv.symm i)) at hi
  change n * w.val (a.coordinateEquiv.symm i) =
    a.axis.val.toAdd (a.index i)
  simpa only [tallIndex, Equiv.trans_apply, Equiv.apply_symm_apply] using hi

private theorem tallSeparated (hε : 0 < ε) (hx : 12 ≤ t.thirdLogRadical)
    (hon : 112896 < Parameters.exponent ε ^ 4 * log t.thirdLogRadical) :
    ∀ w ∈ (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive.ker,
      AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ))
          (AbcTwoNinths.ExteriorE2.project a.tallAxis.val w) < t.thirdLogRadical / log t.thirdLogRadical →
        AbcTwoNinths.ExteriorE2.project a.tallAxis.val w = 0 := by
  intro w hw hcost
  let u := w ∘ a.coordinateEquiv.symm
  have hproj (i : AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) :
      AbcTwoNinths.ExteriorE2.project (a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) u (a.transverseEquiv i) =
        AbcTwoNinths.ExteriorE2.project a.tallAxis.val w i := by
    change (w (a.coordinateEquiv.symm (.inr (a.transverseEquiv i))) : ℝ) -
      (w (a.coordinateEquiv.symm (.inl ())) : ℝ) /
        (a.axis.val.toAdd (a.index (.inl ())) : ℝ) *
        (a.axis.val.toAdd (a.index (.inr (a.transverseEquiv i))) : ℝ) = _
    have hi : a.coordinateEquiv.symm (.inr (a.transverseEquiv i)) = .inr i :=
      a.coordinateEquiv.symm_apply_apply (.inr i)
    rw [hi]
    rfl
  have hweight (i : AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val) :
      a.weight (a.transverseEquiv i) = log (i.val : ℝ) := by
    unfold weight
    rw [a.index_transverse]
    rfl
  have hcost' : AbcTwoNinths.ExteriorE2.cost a.weight (AbcTwoNinths.ExteriorE2.project (a.reindexedAxis : AbcTwoNinths.ExteriorE2.Old a.Transverse) u) =
      AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ))
        (AbcTwoNinths.ExteriorE2.project a.tallAxis.val w) := by
    unfold AbcTwoNinths.ExteriorE2.cost
    symm
    exact Fintype.sum_equiv a.transverseEquiv _ _ (fun i => by rw [hproj, hweight])
  have hle : t.thirdLogRadical / log t.thirdLogRadical ≤ 2 * t.thirdLogRadical / log t.thirdLogRadical :=
    div_le_div_of_nonneg_right (by linarith) (log_nonneg (by linarith))
  have hzero := a.separation hε hx hon u (a.toRoofKernel hw)
    ((hcost'.trans_lt hcost).trans_le hle)
  funext i
  exact (hproj i).symm.trans (congrFun hzero (a.transverseEquiv i))

private theorem tallAxisHeight :
    AbcTwoNinths.Diamond.height (oldSupportPrime S a.roof.val) a.tallAxis.val =
      AbcTwoNinths.Basic.rationalHeight c.source := by
  have h := AbcTwoNinths.Terminal.logRowHeightMaxCharacter base prime (contactSupportAvoid c)
    Subtype.val_injective a.axis
  change AbcTwoNinths.Basic.rationalHeight ((AbcTwoNinths.ExteriorE2.gammaStar (AbcTwoNinths.ExteriorE2.residue base prime (contactSupportAvoid c))
    (AbcTwoNinths.ExteriorE2.monomial base prime) a.axis : ℚˣ) : ℚ) =
      AbcTwoNinths.Diamond.height base a.axis.val.toAdd at h
  rw [a.axis_eq] at h
  rw [h]
  have hside (f : ContactSupport c → ℤ) :
      AbcTwoNinths.Diamond.side (oldSupportPrime S a.roof.val) (f ∘ a.tallIndex) = AbcTwoNinths.Diamond.side base f := by
    unfold AbcTwoNinths.Diamond.side
    exact Fintype.sum_equiv a.tallIndex _ _ (fun i => by rw [← a.tallIndexPrime]; rfl)
  exact congrArg₂ max (hside _) (hside (-a.axis.val.toAdd))

end ContactRoof

/-- The cutoff in the contact data is the cutoff used in the prime count. -/
theorem contactCutoff_eq {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t) :
    auxiliaryPrimeCutoff (Parameters.exponent ε) t.thirdLogRadical (c.prime : ℝ) (AbcTwoNinths.Basic.rationalHeight c.source) =
      c.cutoff := by
  rw [auxiliaryPrimeCutoff, Contact.cutoff, Parameters.auxiliaryRate, Real.sqrt_eq_rpow]

/-- The contact cutoff is positive and stays below half the contact prime. -/
theorem contactCutoff_window {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t) (hε : 0 < ε)
    (hon : 20 ≤ Parameters.exponent ε ^ 2 * t.thirdLogRadical) :
    0 < c.cutoff ∧ c.cutoff < (c.prime : ℝ) / 2 := by
  have hp : 0 < (c.prime : ℝ) := by exact_mod_cast c.prime_isPrime.pos
  have hc : (2.94 * Parameters.exponent ε) * t.thirdLogRadical < log (c.prime : ℝ) := by
    simpa only [show (3 - 6 / 100 : ℝ) = 2.94 by norm_num] using c.log_lower
  have h := auxiliaryPrimeCutoffBounds (lt_min hε (by norm_num))
    (min_le_right _ _) hp hon hc c.log_upper c.axial_height_lower
  rw [← contactCutoff_eq c]
  exact ⟨mul_pos (exp_pos _) ((rpow_pos_of_pos hp _).trans_le (le_max_left _ _)),
    h.2.2.2.2.2⟩

/-- A uniform onset gives actual old corrections and a growing family of
auxiliary primes whose nonzero integral combinations have large height. -/
theorem exists_contactTallFamily {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 0 < X ∧ ∀ {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)
      [Fact c.prime.Prime] [Fact (2 < c.prime)] (a : ContactRoof c),
      X ≤ t.thirdLogRadical →
      let S := c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
      let q := oldSupportPrime S a.roof.val
      let v := a.tallAxis.val
      ∃ (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val))
        (f : Fin (Parameters.dimension ε * ⌊t.thirdLogRadical ^ (1/3:ℝ)⌋₊ + 1) ↪ P),
        P ⊆ auxiliaryFreshPrimes t.radical c.cutoff ∧
        (∀ i ∈ P, ∀ j ∈ P, AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ)) (AbcTwoNinths.ExteriorE2.project v (lift i j)) < t.thirdLogRadical/log t.thirdLogRadical ∧
          (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive (lift i j) +
            AbcSubexp.Prerequisites.freshLabel c.prime i - AbcSubexp.Prerequisites.freshLabel c.prime j = 0) ∧
        ∀ (n : ℤ) (y : Fin (Parameters.dimension ε * ⌊t.thirdLogRadical ^ (1/3:ℝ)⌋₊) → ℤ),
          (n ≠ 0 ∨ y ≠ 0) →
          exp (sqrt t.thirdLogRadical) < AbcTwoNinths.Diamond.height (tuplePrimes q Subtype.val (anchoredTuple f))
            (tupleCombination v (fun i j : P => lift i.val j.val) (anchoredTuple f) n y) := by
  let e := Parameters.exponent ε
  have he : 0 < e := lt_min hε (by norm_num)
  have heCap : e ≤ 1/10 := min_le_right _ _
  obtain ⟨Y, hY, hfamily⟩ := exists_tall_prime_family he heCap
    (Parameters.dimension ε) (Parameters.dimensionPos hε)
  have hLim : Tendsto (fun x : ℝ => e ^ 4 * log x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : 0 < e ^ 4)).2 tendsto_log_atTop
  obtain ⟨Z, hZ⟩ := eventually_atTop.1 (hLim.eventually_gt_atTop 112896)
  refine ⟨max Y (max 12 Z), hY.trans_le (le_max_left _ _), ?_⟩
  intro t c _ _ a hx
  dsimp only
  let S := c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have hdiv (p : ℕ) (hp : p ∈ S) : p ∣ t.radical := by
    by_contra h
    exact (ContactPrime.source_prime_support_iff c (hS p hp)).1 hp
      (c.valuation_eq_zero_of_fresh (hS p hp) h)
  have hR : 0 < t.radical := Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hlogR : log (t.radical : ℝ) = 3 * t.thirdLogRadical := by unfold AbcTwoNinths.Basic.Triple.thirdLogRadical AbcTwoNinths.Basic.Triple.logRadical; ring
  have hroof : AbcTwoNinths.Basic.rationalHeight c.source / (2 * t.thirdLogRadical) ≤
      |(a.tallAxis.val (.inl ()) : ℝ)| := by
    change AbcTwoNinths.Basic.rationalHeight c.source / (2 * t.thirdLogRadical) ≤
      |(a.axis.val.toAdd (a.index (.inl ())) : ℝ)|
    rw [a.index_roof]
    exact a.roof_lower
  have hfam := hfamily t.thirdLogRadical ((le_max_left _ _).trans hx) S a.roof.val t.radical
    c.prime a.tallResidue a.tallAxis
  dsimp only at hfam
  rw [a.tallAxisHeight] at hfam
  rw [contactCutoff_eq c] at hfam
  exact hfam hR hlogR a.roof.property hS hdiv
    (by simpa [e, show (3 - 6 / 100 : ℝ) = 2.94 by norm_num] using c.log_lower)
    c.log_upper c.axial_height_lower hroof a.tallPrimitive
    (a.tallSeparated hε ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
      (hZ t.thirdLogRadical ((le_max_right _ _).trans ((le_max_right _ _).trans hx))))

end AbcSubexp.TupleCounting
