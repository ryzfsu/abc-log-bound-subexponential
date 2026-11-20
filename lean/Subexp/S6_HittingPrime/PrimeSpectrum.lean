/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.NativeWindow

/-! # A single row tested by log-weighted prime sums -/

@[expose] public section

noncomputable section

open Finset Real

namespace AbcSubexp

/-- A finite trigonometric test detects a prime in the prescribed phase box
when the weighted off-constant modes cost less than the constant-term gap. -/
theorem exists_prime_hit_of_weighted_spectrum {κ : Type*} [Fintype κ] [Zero κ]
    [DecidableEq κ] (P : Finset ℕ) (hit : ℕ → Prop)
    (test : ℕ → ℝ) (coefficient node : κ → ℂ) (w : ℕ → ℝ)
    {c off err : ℝ} (hw : ∀ q ∈ P, 0 ≤ w q)
    (hmiss : ∀ q ∈ P, ¬ hit q → test q ≤ off)
    (hexp : ∀ q ∈ P, (test q : ℂ) = ∑ k, coefficient k * node k ^ q)
    (hc : coefficient 0 = (c : ℂ)) (hz : node 0 = 1)
    (herr : ∑ k ∈ (univ : Finset κ).erase 0,
      ‖coefficient k‖ * ‖∑ q ∈ P, (w q : ℂ) * node k ^ q‖ ≤ err)
    (hgap : err < (c - off) * ∑ q ∈ P, w q) :
    ∃ q ∈ P, hit q := by
  classical
  by_contra! hnone
  let A (k : κ) : ℂ := coefficient k * ∑ q ∈ P, (w q : ℂ) * node k ^ q
  have hsum : (∑ q ∈ P, w q * test q : ℝ) = (∑ k, A k).re := by
    have heq : ((∑ q ∈ P, w q * test q : ℝ) : ℂ) = ∑ k, A k := by
      push_cast
      simp_rw [A, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro q hq
      rw [hexp q hq, mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    exact congrArg Complex.re heq
  have hzero : (A 0).re = c * ∑ q ∈ P, w q := by
    simp only [A, hz, one_pow, mul_one, hc, ← Complex.ofReal_sum,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hbad : (∑ q ∈ P, w q * test q) ≤ (∑ q ∈ P, w q) * off := by
    rw [sum_mul]
    exact sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hmiss q hq (hnone q hq)) (hw q hq)
  have hrem : ‖∑ k ∈ (univ : Finset κ).erase 0, A k‖ ≤ err := by
    refine (norm_sum_le ..).trans ?_
    simpa only [A, norm_mul] using herr
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (∑ k ∈ (univ : Finset κ).erase 0, A k))).1
  rw [← add_sum_erase _ _ (mem_univ (0 : κ)), Complex.add_re, hzero] at hsum
  linarith

end AbcSubexp
