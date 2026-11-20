/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S3_ContactPrime.Contact
public import Subexp.S4_TupleCounting.GroupedSelection
public import Subexp.S5_Box.BoxData
public import Subexp.S5_Determinant.VanishingPolynomial
public import Subexp.S6_HittingPrime.HittingPrime
public import Subexp.S7_Interpolation.PhaseInterpolation
public import Subexp.Conclusion.RadicalBound

/-!
# Assembly of the logarithmic height bound

The determinant and interpolation arguments exclude high triples for large
radicals. The baseline estimate bounds the logarithmic height on the
remaining range.

## Main results
* `AbcSubexp.assembledSubexp`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

namespace Assembly

/-- The height cap from Section 2 gives a uniform bound on the bounded radical range. -/
theorem exists_baseline_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.logHeight ≤ C * (t.radical : ℝ) ^ ((5 : ℝ) / 18) :=
  AbcSubexp.exists_baseline_bound

/-- A sufficiently large ordered high triple has a contact source as in Section 3. -/
theorem exists_contact (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → t.a ≤ t.b → High ε t → Nonempty (Contact ε t) :=
  ContactPrime.exists_contact ε hε

/-- Sufficiently large contact data yields the grouped auxiliary tuples of Section 4. -/
theorem exists_grouped_tuple (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical → Nonempty (GroupedTuple c) :=
  AbcSubexp.exists_grouped_tuple ε hε

/-- The selected list admits the lattice box and its translation in Section 5. -/
theorem exists_box_data (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c) (q : HittingPrime g),
      X ≤ t.thirdLogRadical → BoxData q :=
  Box.existsBoxData ε hε

/-- The determinant and elimination in Section 5 give a nonzero vanishing polynomial. -/
theorem exists_vanishing_polynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c) (q : HittingPrime g),
      X ≤ t.thirdLogRadical → BoxData q →
      ∃ P : MvPolynomial (Fin (dimension ε)) ℚ, P ≠ 0 ∧ P.totalDegree ≤ c.degree ∧
        ∀ z ∈ q.points c.radius, MvPolynomial.eval (fun i => (z i : ℚ)) P = 0 :=
  AbcSubexp.exists_vanishing_polynomial ε hε

/-- For sufficiently large radicals, Section 6 supplies an interpolation prime
and one list whose slopes simultaneously meet all coordinate targets. -/
theorem exists_hitting_prime (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c),
      X ≤ t.thirdLogRadical → Nonempty (HittingPrime g) :=
  AbcSubexp.exists_hitting_prime ε hε

/-- The residue blocks and Lucas lifting give injectivity on the smaller simplex in Section 7. -/
theorem interpolation_injective (hε : 0 < ε) (q : HittingPrime g) (hwidth : windowWidth ε ≤ c.width)
    (P : MvPolynomial (Fin (dimension ε)) ℚ) (hdegree : P.totalDegree ≤ c.degree)
    (hvanish : ∀ z ∈ q.points (c.degree + q.prime), MvPolynomial.eval (fun i => (z i : ℚ)) P = 0) :
    P = 0 :=
  AbcSubexp.interpolation_injective hε q hwidth P hdegree hvanish

/-- The bounded and large radical ranges supply the single constant in Theorem 1.1. -/
theorem bound_of_eventual_exclusion (ε : ℝ) (hε : 0 < ε)
    (hbaseline : ∃ C : ℝ, 0 < C ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.logHeight ≤ C * (t.radical : ℝ) ^ ((5 : ℝ) / 18))
    (htail : ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → t.a ≤ t.b → t.logHeight < exp (3 * exponent ε * t.thirdLogRadical)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
      Real.log c ≤ C * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε :=
  AbcSubexp.bound_of_eventual_exclusion ε hε hbaseline htail

/-- A polynomial vanishing on the box also vanishes on the smaller interpolation simplex
for the same selected list. Injectivity then excludes high triples for large radicals. -/
theorem eventual_exclusion (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → t.a ≤ t.b → t.logHeight < exp (3 * exponent ε * t.thirdLogRadical) := by
  obtain ⟨Xcontact, hcontact⟩ := exists_contact ε hε
  obtain ⟨Xtuple, htuple⟩ := exists_grouped_tuple ε hε
  obtain ⟨Xbox, hbox⟩ := exists_box_data ε hε
  obtain ⟨Xdet, hdet⟩ := exists_vanishing_polynomial ε hε
  obtain ⟨Xprime, hprime⟩ := exists_hitting_prime ε hε
  refine ⟨max (max Xcontact Xtuple) (max Xbox (max Xdet Xprime)), ?_⟩
  intro t hX hord
  by_contra! hhigh
  have hleft := (le_max_left _ _).trans hX
  have hright := (le_max_right _ _).trans hX
  have hdetPrime := (le_max_right _ _).trans hright
  obtain ⟨c⟩ := hcontact t ((le_max_left _ _).trans hleft) hord hhigh
  obtain ⟨g⟩ := htuple t c ((le_max_right _ _).trans hleft)
  obtain ⟨q⟩ := hprime t c g ((le_max_right _ _).trans hdetPrime)
  have b := hbox t c g q ((le_max_left _ _).trans hright)
  obtain ⟨P, hne, hdegree, hvanish⟩ := hdet t c g q ((le_max_left _ _).trans hdetPrime) b
  apply hne
  apply interpolation_injective hε q b.width_lower P hdegree
  intro z hz
  exact hvanish z ⟨hz.1.trans q.radius_le, hz.2⟩

end Assembly

/-- The assembled subpower radical bound before the public package endpoint. -/
theorem assembledSubexp : subexpStatement := by
  intro ε hε
  exact Assembly.bound_of_eventual_exclusion ε hε Assembly.exists_baseline_bound
    (Assembly.eventual_exclusion ε hε)

end AbcSubexp
