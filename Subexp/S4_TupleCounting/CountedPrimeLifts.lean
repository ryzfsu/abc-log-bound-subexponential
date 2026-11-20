/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.CommonPrimeCount
public import Subexp.S4_TupleCounting.CommonPrimeLifts
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Signed corrections on a counted family of primes

The same family satisfies the Section 4 lower bound and admits simultaneously chosen old
corrections for every ordered pair, as required in the subsequent tuple count.

## Main results
* `AbcSubexp.TupleCounting.exists_countedPrimeLifts`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real

private theorem exists_countedPairLifts (S : Finset ℕ) (roof : ℕ) {R p : ℕ}
    {G : Type*} [AddCommGroup G] [Finite G] (label : ℕ → G)
    (hp : 0 < p) (hcard : (Nat.card G : ℝ) = ((p : ℝ)-1)/2) (hR : 0 < R)
    (hS : ∀ q ∈ S, q.Prime) (hdiv : ∀ q ∈ S, q ∣ R)
    {e x h : ℝ} (hx : exp 1 ≤ x) (hxR : log R = 3*x) (hh : 0 < h)
    (ht : 0 < log (auxiliaryPrimeCutoff e x p h))
    (htx : log (auxiliaryPrimeCutoff e x p h) ≤ x)
    (hsupply : auxiliaryPrimeCutoff e x p h / (8*log (auxiliaryPrimeCutoff e x p h)) ≤
      ((auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h)).card : ℝ))
    (red : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof) →+ G) (s : red.ker)
    (hroof : h/(2*x) ≤ |((s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (.inl ()) : ℝ)|)
    (hprim : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a)
    (hshort : ∀ w ∈ red.ker,
      AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ)) (AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w) < x/log x →
        AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w = 0) :
    ∃ (Q : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)),
      Q ⊆ auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h) ∧
      exp ((e^2/10)*x - 12*x*log (3*log x)/log x) / (4*x^2) ≤ Q.card ∧
      ∀ i ∈ Q, ∀ j ∈ Q,
        AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ)) (AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (lift i j)) < x/log x ∧
        red (lift i j) + label i - label j = 0 := by
  classical
  obtain ⟨rep, center, hc⟩ := AbcSubexp.Prerequisites.choose_centers red label
  obtain ⟨D, z, Q, _, hsub, hsize, hmem⟩ := exists_commonPrimeFamily S roof hR
    hp hS hdiv hx hxR hh ht htx hsupply red hcard s hroof hprim hshort label
    (fun q => AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (center q))
  have hw (j : AbcTwoNinths.ExteriorE2.OldIndex S roof) : 0 ≤ log (j.val : ℝ) :=
    log_nonneg (by exact_mod_cast (hS j.val (Finset.mem_erase.mp j.property).2).one_le)
  obtain ⟨lift, hlift⟩ := pairLifts_of_commonCenter (D := D) red (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof))
    _ hw (x/log x) Q label rep center hc z hmem
  exact ⟨Q, lift, hsub, hsize, hlift⟩

/-- Select a single counted prime family and fix its pair corrections before
any tuple is chosen. -/
theorem exists_countedPrimeLifts (S : Finset ℕ) (roof : ℕ) {R p : ℕ}
    [Fact p.Prime] [Fact (2 < p)] (hR : 0 < R)
    (hS : ∀ q ∈ S, q.Prime) (hdiv : ∀ q ∈ S, q ∣ R)
    {e x h : ℝ} (hx : exp 1 ≤ x) (hxR : log R = 3*x) (hh : 0 < h)
    (ht : 0 < log (auxiliaryPrimeCutoff e x p h))
    (htx : log (auxiliaryPrimeCutoff e x p h) ≤ x)
    (hsupply : auxiliaryPrimeCutoff e x p h / (8*log (auxiliaryPrimeCutoff e x p h)) ≤
      ((auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h)).card : ℝ))
    (red : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof) →+ AbcSubexp.Prerequisites.Residue p) (s : red.ker)
    (hroof : h/(2*x) ≤ |((s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (.inl ()) : ℝ)|)
    (hprim : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a)
    (hshort : ∀ w ∈ red.ker,
      AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ)) (AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w) < x/log x →
        AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w = 0) :
    ∃ (Q : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)),
      Q ⊆ auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h) ∧
      exp ((e^2/10)*x - 12*x*log (3*log x)/log x) / (4*x^2) ≤ Q.card ∧
      ∀ i ∈ Q, ∀ j ∈ Q,
        AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ)) (AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (lift i j)) < x/log x ∧
        red (lift i j) + AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0 := by
  have : Finite (AbcSubexp.Prerequisites.Residue p) :=
    inferInstanceAs (Finite ((ZMod p)ˣ ⧸ AbcTwoNinths.ExteriorE2.signs p))
  have hcard : (Nat.card (AbcSubexp.Prerequisites.Residue p) : ℝ) = ((p : ℝ)-1)/2 := by
    simpa only [Int.cast_one, abs_one, div_one, mul_one] using AbcSubexp.Prerequisites.native_normalization (p := p) 1
  have h := exists_countedPairLifts (G := AbcSubexp.Prerequisites.Residue p) (R := R) (p := p) (e := e) (x := x) (h := h)
    S roof (AbcSubexp.Prerequisites.freshLabel p) (Fact.out : p.Prime).pos
    hcard hR hS hdiv hx hxR hh ht htx hsupply red s hroof hprim hshort
  exact h

end AbcSubexp.TupleCounting
