/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import AbcTwoNinths.Basic.RationalGridTransport
public import AbcTwoNinths.Paper.S5_Selection.SelectedDepth

/-!
# Comparison for an integer minor

These lemmas compare a minor's prime-power divisibility with its logarithmic
size and verify that the selected source produces a nontrivial shift.
-/

public section

open scoped BigOperators

namespace AbcSubexp.Prerequisites

open AbcTwoNinths.Basic AbcTwoNinths.Statement

/-- The contributions of distinct prime powers dividing a nonzero integer
fit within the logarithmic height of that integer. -/
theorem sameIntegerArch (D : ℤ) (hD : D ≠ 0) (S : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p)
    (hd : ∀ p ∈ S, (p : ℤ) ^ e p ∣ D) :
    (∑ p ∈ S, (e p : ℝ) * Real.log (p : ℝ)) ≤ Real.log (D.natAbs : ℝ) := by
  let f := D.natAbs.factorization
  have hn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hlog (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
    cases p with
    | zero => simp
    | succ p => exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
  rw [Real.log_nat_eq_sum_factorization]
  change _ ≤ ∑ p ∈ f.support, (f p : ℝ) * Real.log (p : ℝ)
  calc
    _ ≤ ∑ p ∈ S, (f p : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hps
      apply mul_le_mul_of_nonneg_right _ (hlog p)
      have hcast : ((p ^ e p : ℕ) : ℤ) ∣ D := by simpa only [Nat.cast_pow] using hd p hps
      exact_mod_cast (Nat.Prime.pow_dvd_iff_le_factorization (hp p hps) hn).mp
        (Int.natCast_dvd.mp hcast)
    _ ≤ ∑ p ∈ S ∪ f.support, (f p : ℝ) * Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (hlog p))
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro p _ hp'
      rw [Finsupp.notMem_support_iff.mp hp', Nat.cast_zero, zero_mul]

private theorem congrZeroIntAbs {p E : ℕ} [Fact p.Prime] (Z : ℤ)
    (h : RatCongruent p E (Z : ℚ) 0) : p ^ E ∣ Z.natAbs := by
  rcases h with h | h
  · have hZ : Z = 0 := by exact_mod_cast h
    simp [hZ]
  · rw [sub_zero, padicValRat.of_int] at h
    have hd := (padicValInt_dvd_iff (p := p) E Z).mpr (Or.inr (by exact_mod_cast h))
    exact Int.natAbs_dvd_natAbs.mpr hd

/-- Scaling by a rational of valuation zero preserves the divisibility of
the resulting integer by the prescribed prime power. -/
theorem integer_divisibility_after_unit_scaling {p E : ℕ} [Fact p.Prime]
    {a u : ℚ} {Z : ℤ} (h : RatCongruent p E a 0)
    (hu : padicValRat p u = 0) (hZ : (Z : ℚ) = u * a) :
    p ^ E ∣ Z.natAbs := by
  apply congrZeroIntAbs Z
  rw [hZ, ← mul_zero u]
  exact congrScale h (le_of_eq hu.symm)

/-- Positive depth at a prime on the selected side forces a nontrivial shift. -/
theorem selected_shift_nontrivial (t : Triple) {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (sideValue t (minRadicalSide t)).primeFactors) :
    selectedSource t ≠ 1 := by
  have hd := (AbcTwoNinths.Selection.selectedSourceDepthOfMem t hp).2
  intro he
  rw [he, sub_self, padicValRat.zero] at hd
  have hv := Nat.mem_primeFactors.mp hp
  have hn := one_le_padicValNat_of_dvd hv.2.2 hv.2.1
  omega

end AbcSubexp.Prerequisites
