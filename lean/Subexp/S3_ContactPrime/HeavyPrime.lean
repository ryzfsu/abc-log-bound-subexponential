/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S1_Statement.LeastRadicalSide

/-!
# A heavy prime on the minimum-radical side

The real and finite contact estimates leave enough valuation mass above the cutoff
to select a prime by averaging against logarithmic weights.

## Main results
* `AbcSubexp.ContactPrime.heavyPrime_of_contact_mass`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime


/-- Select a contact prime with the logarithmic size and valuation bounds of (4). -/
theorem heavyPrime_of_contact_mass (t : AbcTwoNinths.Basic.Triple) {e : ℝ}
    (he : 0 < e) (he_small : e ≤ 1 / 10) (hx : 0 < t.thirdLogRadical) (hord : t.a ≤ t.b)
    (hH : Real.exp (3 * e * t.thirdLogRadical) ≤ t.logHeight)
    (hreal : AbcTwoNinths.Statement.RealContactBound (e / 100) t) (hfinite : AbcTwoNinths.Statement.SmallPrimeMassBound (3 * e / 50) (1 / 25) t) :
    let S := AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)
    ∃ p ∈ S.primeFactors,
      t.logHeight * Real.exp (-(3 * e / 50) * t.thirdLogRadical) < (p : ℝ) ∧
      (147 * e / 50) * t.thirdLogRadical < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ t.thirdLogRadical ∧
      2 * e * t.logHeight < (padicValNat p S : ℝ) * Real.log (p : ℝ) := by
  classical
  let S := AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)
  let T := t.logHeight * Real.exp (-(3 * e / 50) * t.thirdLogRadical)
  let large := S.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ T)
  let mass (p : ℕ) := (padicValNat p S : ℝ) * Real.log (p : ℝ)
  have height_pos : 0 < t.logHeight := (Real.exp_pos _).trans_le hH
  have exp_cutoff : Real.exp ((147 * e / 50) * t.thirdLogRadical) ≤ T := by
    calc
      Real.exp ((147 * e / 50) * t.thirdLogRadical) =
          Real.exp (3 * e * t.thirdLogRadical) * Real.exp (-(3 * e / 50) * t.thirdLogRadical) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hH (Real.exp_pos _).le
  have log_floor (p : ℕ) (hp : p ∈ large) :
      (147 * e / 50) * t.thirdLogRadical < Real.log (p : ℝ) := by
    have cut : T < (p : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hp).2
    rw [← Real.log_exp ((147 * e / 50) * t.thirdLogRadical)]
    exact Real.log_lt_log (Real.exp_pos _) (exp_cutoff.trans_lt cut)
  have total_weights : (∑ p ∈ S.primeFactors, Real.log (p : ℝ)) ≤ t.thirdLogRadical := by
    have prime_ne_zero (p : ℕ) (hp : p ∈ S.primeFactors) : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hproduct : 0 < ∏ p ∈ S.primeFactors, (p : ℝ) := by
      exact Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hbudget : (∏ p ∈ S.primeFactors, (p : ℝ)) ≤ Real.exp t.thirdLogRadical := by
      rw [← Nat.cast_prod]
      exact AbcTwoNinths.Statement.minSideLeScale t
    rw [← Real.log_prod prime_ne_zero, ← Real.log_exp t.thirdLogRadical]
    exact Real.log_le_log hproduct hbudget
  have nonneg_weight (p : ℕ) (hp : p ∈ S.primeFactors) : 0 ≤ Real.log (p : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have large_weights : (∑ p ∈ large, Real.log (p : ℝ)) ≤ t.thirdLogRadical :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => nonneg_weight p hp)).trans total_weights
  have full_mass : (1 - e / 100) * t.logHeight ≤ ∑ p ∈ S.primeFactors, mass p :=
    AbcTwoNinths.Statement.minSideFull t hord hreal
  have small_mass :
      (∑ p ∈ S.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T), mass p) ≤ (1 / 25) * t.logHeight :=
    hfinite
  have mass_split :
      (∑ p ∈ S.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T), mass p) +
        (∑ p ∈ large, mass p) = ∑ p ∈ S.primeFactors, mass p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have large_mass : (9 / 10) * t.logHeight < ∑ p ∈ large, mass p := by
    have bound := mul_le_mul_of_nonneg_right he_small height_pos.le
    linarith
  have selected : ∃ p ∈ large, 2 * e * t.logHeight < mass p := by
    by_contra! no_prime
    have weight_control (p : ℕ) (hp : p ∈ large) :
        mass p ≤ ((9 / 10) * t.logHeight / t.thirdLogRadical) * Real.log (p : ℝ) := by
      calc
        mass p ≤ 2 * e * t.logHeight := no_prime p hp
        _ ≤ ((9 / 10) * t.logHeight / t.thirdLogRadical) * ((147 * e / 50) * t.thirdLogRadical) := by
          rw [show ((9 / 10) * t.logHeight / t.thirdLogRadical) * ((147 * e / 50) * t.thirdLogRadical) =
              (1323 / 500) * e * t.logHeight by field_simp [hx.ne']; ring]
          nlinarith [mul_pos he height_pos]
        _ ≤ _ := mul_le_mul_of_nonneg_left (log_floor p hp).le (by positivity)
    have h := calc
      (∑ p ∈ large, mass p) ≤ ∑ p ∈ large, ((9 / 10) * t.logHeight / t.thirdLogRadical) * Real.log (p : ℝ) :=
        Finset.sum_le_sum weight_control
      _ = ((9 / 10) * t.logHeight / t.thirdLogRadical) * ∑ p ∈ large, Real.log (p : ℝ) :=
        (Finset.mul_sum ..).symm
      _ ≤ ((9 / 10) * t.logHeight / t.thirdLogRadical) * t.thirdLogRadical :=
        mul_le_mul_of_nonneg_left large_weights (by positivity)
      _ = (9 / 10) * t.logHeight := div_mul_cancel₀ _ hx.ne'
    exact (not_lt_of_ge h) large_mass
  obtain ⟨p, hp, hmass⟩ := selected
  have hp_factor := (Finset.mem_filter.mp hp).1
  have log_ceiling : Real.log (p : ℝ) ≤ t.thirdLogRadical :=
    (Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ))
      (fun q hq => nonneg_weight q hq) hp_factor).trans total_weights
  exact ⟨p, hp_factor, lt_of_not_ge (Finset.mem_filter.mp hp).2,
    log_floor p hp, log_ceiling, hmass⟩

end AbcSubexp.ContactPrime
