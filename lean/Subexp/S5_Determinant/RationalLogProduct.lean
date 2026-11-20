/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S4_ExteriorE2.Products

/-! # Logarithmic reconstruction of a signed rational on a finite prime support -/

@[expose] public section

open Finset Real

namespace AbcSubexp

/-- Sum the local orders with their real logarithmic weights over any finite prime
set containing all nonzero prime valuations. -/
theorem log_abs_rat_eq_sum_padicValRat {x : ℚ} (hx : x ≠ 0) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ p : ℕ, p.Prime → p ∉ S → padicValRat p x = 0) :
    Real.log |(x : ℝ)| = ∑ p ∈ S, (padicValRat p x : ℝ) * Real.log (p : ℝ) := by
  classical
  let n := x.num.natAbs
  let d := x.den
  let T := n.primeFactors ∪ d.primeFactors
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr (by simpa using hx)
  have hd : d ≠ 0 := x.den_ne_zero
  have heval := AbcTwoNinths.ExteriorE2.ratEval hn hd
  change ((∏ i : AbcTwoNinths.ExteriorE2.Support n d, AbcTwoNinths.ExteriorE2.ratUnit (AbcTwoNinths.ExteriorE2.base n d) (AbcTwoNinths.ExteriorE2.prime n d) i ^
    ((AbcTwoNinths.ExteriorE2.vec n d).toAdd i) : ℚˣ) : ℚ) = (n : ℚ) / d at heval
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val] at heval
  have hprod : ∏ i : T, (i.val : ℚ) ^ ((AbcTwoNinths.ExteriorE2.vec n d).toAdd i) = (n : ℚ) / d := heval
  have habs : |(x : ℝ)| = (n : ℝ) / d := by
    rw [Rat.cast_def, abs_div, abs_of_nonneg (Nat.cast_nonneg x.den : 0 ≤ (x.den : ℝ))]
    simp [n, d]
  have hval (p : ℕ) (hp : p.Prime) :
      padicValRat p x = (n.factorization p : ℤ) - d.factorization p := by
    simp only [Nat.factorization_def _ hp]
    rfl
  let w := fun p : ℕ => (padicValRat p x : ℝ) * Real.log (p : ℝ)
  have hbase : Real.log |(x : ℝ)| = ∑ p ∈ T, w p := by
    have hre := congrArg (fun z : ℚ => (z : ℝ)) hprod
    push_cast at hre
    rw [habs, ← hre, Real.log_prod]
    · rw [← Finset.sum_coe_sort T w]
      apply sum_congr rfl
      intro i _
      rw [log_zpow]
      dsimp only [w]
      rw [hval i (AbcTwoNinths.ExteriorE2.prime n d i)]
      rfl
    · intro i _
      exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (AbcTwoNinths.ExteriorE2.prime n d i).ne_zero)
  rw [hbase]
  change ∑ p ∈ T, w p = ∑ p ∈ S, w p
  calc
    _ = ∑ p ∈ T ∪ S, w p := by
      apply sum_subset subset_union_left
      intro p hp hT
      have hpS := (mem_union.mp hp).resolve_left hT
      have hn0 : n.factorization p = 0 := by
        by_contra h
        exact hT (mem_union_left _ (Finsupp.mem_support_iff.mpr h))
      have hd0 : d.factorization p = 0 := by
        by_contra h
        exact hT (mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      simp [w, hval p (hprime p hpS), hn0, hd0]
    _ = _ := by
      symm
      apply sum_subset subset_union_right
      intro p hp hpS
      have hpT := (mem_union.mp hp).resolve_right hpS
      have hP : p.Prime := by
        rcases mem_union.mp hpT with h | h <;> exact Nat.prime_of_mem_primeFactors h
      simp [w, hsupport p hP hpS]

end AbcSubexp
