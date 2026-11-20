/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.FloorBudgetTrim
public import AbcTwoNinths.Paper.S1_Statement.LeastRadicalSide
public import AbcTwoNinths.Paper.S4_ExteriorE2.SmoothPartFactorization

/-!
# Smooth moduli at positive height rates

An excess of small-prime mass on the minimum-radical side supplies a modulus
with a large common depth and logarithm below the cutoff.

## Main results
* `AbcSubexp.ContactPrime.smoothModulus_of_mass_posRate`
-/

@[expose] public section

open scoped BigOperators

namespace AbcSubexp.ContactPrime


/-- For every positive height rate with `2 * sigma ≤ beta`, excess finite-place
mass on the minimum-radical side supplies a sufficiently deep smooth modulus. -/
theorem smoothModulus_of_mass_posRate {beta sigma nu : ℝ}
    (hsigma : 0 < sigma) (hbeta : 2 * sigma ≤ beta) (hnu : 0 < nu) (minDepth : ℕ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical →
      Real.exp (beta * t.thirdLogRadical) ≤ t.logHeight → ¬ AbcTwoNinths.Statement.SmallPrimeMassBound sigma nu t →
      ∃ M L : ℕ, 3 ≤ M ∧ 0 < L ∧ minDepth ≤ L ∧
        M ^ L ∣ AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t) ∧ (¬ 2 ∣ M ∨ 4 ∣ M) ∧
        (beta - sigma) * t.thirdLogRadical / 2 ≤ Real.log (M : ℝ) ∧
        Real.log (M : ℝ) ≤ Real.log t.logHeight - sigma * t.thirdLogRadical ∧
        Real.log t.logHeight ≤ 4 * Real.log (M : ℝ) ∧
        nu * (beta - sigma) / (4 * (1 + beta - sigma)) * t.logHeight ≤
          (L : ℝ) * Real.log (M : ℝ) := by
  classical
  let gap := beta - sigma
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hβ : 0 < beta := by linarith
  let depthBound := max 2 (minDepth : ℝ)
  have hd2 : 2 ≤ depthBound := le_max_left _ _
  have hdpos : 0 < depthBound := by linarith
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1
    ((Real.tendsto_exp_div_pow_atTop 1).eventually
      (Filter.eventually_ge_atTop (depthBound * (1 + 1 / beta) / nu)))
  let X := max (max 1 (Real.log 4 / gap)) (Y / beta)
  refine ⟨X, ?_, ?_⟩
  · exact zero_le_one.trans ((le_max_left _ _).trans (le_max_left _ _))
  intro t hx hrate hbad
  have hxpos : 0 < t.thirdLogRadical := zero_lt_one.trans_le
    ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hrate
  have hlogH : beta * t.thirdLogRadical ≤ Real.log t.logHeight := (Real.le_log_iff_exp_le hH).2 hrate
  have hypos : 0 < Real.log t.logHeight := (mul_pos hβ hxpos).trans_le hlogH
  have hYle : Y ≤ Real.log t.logHeight := by
    have hxY : Y / beta ≤ t.thirdLogRadical := (le_max_right _ _).trans hx
    exact ((div_le_iff₀ hβ).1 hxY).trans (mul_comm t.thirdLogRadical beta ▸ hlogH)
  let B := Real.log t.logHeight - sigma * t.thirdLogRadical
  have hgapx : gap * t.thirdLogRadical ≤ B := by
    dsimp [gap, B]
    linarith
  have hBpos : 0 < B := (mul_pos hgap hxpos).trans_le hgapx
  have hlog4 : Real.log 4 ≤ B := by
    have hx4 : Real.log 4 / gap ≤ t.thirdLogRadical :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    exact ((div_le_iff₀ hgap).1 hx4).trans (by simpa only [mul_comm] using hgapx)
  have hBadd : 0 < B + t.thirdLogRadical := add_pos hBpos hxpos
  have hupper : B + t.thirdLogRadical ≤ (1 + 1 / beta) * Real.log t.logHeight := by
    have hxlog : t.thirdLogRadical ≤ Real.log t.logHeight / beta :=
      (le_div_iff₀ hβ).2 (by simpa only [mul_comm] using hlogH)
    have hB : B ≤ Real.log t.logHeight := sub_le_self _ (mul_nonneg hsigma.le hxpos.le)
    calc
      B + t.thirdLogRadical ≤ Real.log t.logHeight + Real.log t.logHeight / beta := add_le_add hB hxlog
      _ = (1 + 1 / beta) * Real.log t.logHeight := by ring
  let r := nu * t.logHeight / (B + t.thirdLogRadical)
  have hr : depthBound ≤ r := by
    have h := hY _ hYle
    rw [pow_one, Real.exp_log hH] at h
    have h := (div_le_iff₀ hnu).1 h
    rw [div_mul_eq_mul_div] at h
    have h := (le_div_iff₀ hypos).1 h
    apply (le_div_iff₀ hBadd).2
    calc
      depthBound * (B + t.thirdLogRadical) ≤ depthBound * ((1 + 1 / beta) * Real.log t.logHeight) :=
        mul_le_mul_of_nonneg_left hupper hdpos.le
      _ ≤ nu * t.logHeight := by linarith only [h]
  let L := ⌊r⌋₊
  have hr2 : 2 ≤ r := hd2.trans hr
  have hLpos : 0 < L := Nat.floor_pos.2 (by linarith)
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hLmin : minDepth ≤ L := by
    by_cases hz : minDepth = 0
    · simp [hz]
    · exact (Nat.le_floor_iff' hz).2 ((le_max_right _ _).trans hr)
  have hLlower : r / 2 ≤ (L : ℝ) := by
    have hf := Nat.lt_floor_add_one r
    change r < (L : ℝ) + 1 at hf
    linarith
  have hLupper : (L : ℝ) ≤ r := Nat.floor_le (by linarith)
  let A := AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)
  let cutoff := t.logHeight * Real.exp (-sigma * t.thirdLogRadical)
  have hA : 0 < A := by
    dsimp [A]
    cases AbcTwoNinths.Statement.minRadicalSide t
    · exact t.apos
    · exact t.bpos
    · change 0 < t.c
      rw [← t.add]
      exact Nat.add_pos_left t.apos _
  let n := AbcTwoNinths.ExteriorE2.smoothPart A cutoff
  obtain ⟨hnA, hlogn⟩ := AbcTwoNinths.ExteriorE2.smoothPartFactorization hA cutoff
  have hn : 0 < n := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hA.ne' hnA)
  have hmass : nu * t.logHeight ≤ Real.log (n : ℝ) := by
    have hbad' : nu * t.logHeight < AbcTwoNinths.Statement.primePowerLogMass A cutoff := lt_of_not_ge hbad
    refine hbad'.le.trans_eq ?_
    rw [hlogn]
    change (∑ q ∈ AbcTwoNinths.ExteriorE2.smoothPrimeFactors A cutoff, (padicValNat q A : ℝ) * Real.log q) = _
    apply Finset.sum_congr rfl
    intro q hq
    rw [Nat.factorization_def A
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1)]
  have hprimes : n.primeFactors ⊆ AbcTwoNinths.ExteriorE2.smoothPrimeFactors A cutoff := by
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    have hd := (Nat.mem_primeFactors.mp hq).2.1
    change q ∣ ∏ j ∈ AbcTwoNinths.ExteriorE2.smoothPrimeFactors A cutoff, j ^ A.factorization j at hd
    obtain ⟨j, hj, hjd⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun j => j ^ A.factorization j)).1 hd
    have hjprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hj).1
    have hqj := ((Nat.dvd_prime hjprime).1 (hp.dvd_of_dvd_pow hjd)).resolve_left hp.ne_one
    simpa only [hqj] using hj
  have hcutoff : cutoff = Real.exp B := by
    dsimp [cutoff, B]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hH, neg_mul]
  have hcap (q : ℕ) (hq : q ∈ n.primeFactors) : Real.log (q : ℝ) ≤ B := by
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    have hqcut : (q : ℝ) ≤ cutoff := (Finset.mem_filter.1 (hprimes hq)).2
    exact (Real.log_le_iff_le_exp hqpos).2 (hcutoff ▸ hqcut)
  have hrad : ∑ q ∈ n.primeFactors, Real.log (q : ℝ) ≤ t.thirdLogRadical := by
    have hradlog := AbcTwoNinths.Statement.minSideLeScale t
    change ((∏ q ∈ A.primeFactors, q : ℕ) : ℝ) ≤ Real.exp t.thirdLogRadical at hradlog
    push_cast at hradlog
    have hqpos (q : ℕ) (hq : q ∈ A.primeFactors) : 0 < (q : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    have hprod : 0 < ∏ q ∈ A.primeFactors, (q : ℝ) :=
      Finset.prod_pos hqpos
    have hsum := (Real.log_le_iff_le_exp hprod).2 hradlog
    rw [Real.log_prod (fun q hq => (hqpos q hq).ne')] at hsum
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (fun q hq => (Finset.mem_filter.1 (hprimes hq)).1)
      (fun q hq _ => Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le))).trans hsum
  have hbudget : B ≤ Real.log (n : ℝ) / (L : ℝ) -
      ∑ q ∈ n.primeFactors, Real.log (q : ℝ) := by
    have hcapacity : B + t.thirdLogRadical ≤ Real.log (n : ℝ) / (L : ℝ) := by
      apply (le_div_iff₀ hLreal).2
      calc
        (B + t.thirdLogRadical) * (L : ℝ) ≤ r * (B + t.thirdLogRadical) := by
          rw [mul_comm (B + t.thirdLogRadical)]
          exact mul_le_mul_of_nonneg_right hLupper hBadd.le
        _ = nu * t.logHeight := div_mul_cancel₀ _ hBadd.ne'
        _ ≤ Real.log (n : ℝ) := hmass
    linarith
  obtain ⟨M, hM, hMd, hparity, hlow, hhigh⟩ :=
    AbcTwoNinths.Basic.floorBudgetTrim hn hnA hLpos hlog4 hcap hbudget
  have hM3 : 3 ≤ M := by
    by_contra! h
    have : M = 2 := by omega
    subst M
    norm_num at hparity
  have hlogRatio : Real.log t.logHeight ≤ 4 * Real.log (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hbeta hxpos.le
    dsimp [B] at hlow
    linarith only [h, hlogH, hlow]
  refine ⟨M, L, hM3, hLpos, hLmin, hMd, hparity, by linarith, hhigh,
    hlogRatio, ?_⟩
  have hrat : gap / (1 + gap) ≤ B / (B + t.thirdLogRadical) := by
    have hgapden : 0 < 1 + gap := by positivity
    apply (le_div_iff₀ hBadd).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hgapden).2
    nlinarith only [hgapx]
  calc
    nu * (beta - sigma) / (4 * (1 + beta - sigma)) * t.logHeight =
        (nu * t.logHeight / 4) * (gap / (1 + gap)) := by
      have heq : 1 + beta - sigma = 1 + gap := by dsimp [gap]; ring
      rw [heq]
      change nu * gap / (4 * (1 + gap)) * t.logHeight = _
      field_simp
    _ ≤ (nu * t.logHeight / 4) * (B / (B + t.thirdLogRadical)) :=
      mul_le_mul_of_nonneg_left hrat (by positivity)
    _ = (r / 2) * (B / 2) := by dsimp [r]; ring
    _ ≤ (L : ℝ) * Real.log (M : ℝ) :=
      mul_le_mul hLlower hlow (by positivity) hLreal.le

end AbcSubexp.ContactPrime
