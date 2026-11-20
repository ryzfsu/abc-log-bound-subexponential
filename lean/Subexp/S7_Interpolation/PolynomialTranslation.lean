/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# Translation differences on a finite-field lattice

This module formalizes polynomial translation on the Section 7 grid.

The translation difference lowers total degree. Evaluation on natural nodes detects reduced polynomials over a prime field.

## Main results
* `AbcSubexp.totalDegree_translation_sub_le`
* `AbcSubexp.eq_zero_of_natGrid_eval`
-/

@[expose] public section

namespace AbcSubexp

open MvPolynomial

variable {ι K : Type*} [Field K]

/-- Translate each variable by the corresponding field element. -/
noncomputable def polynomialTranslation (u : ι → K) :
    MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval (fun i => X i + C (u i))

/-- Evaluating the translated polynomial at `x` equals evaluating the original at `x + u`. -/
theorem eval_polynomialTranslation (x u : ι → K) (p : MvPolynomial ι K) :
    eval x (polynomialTranslation u p) = eval (fun i => x i + u i) p := by
  change aeval x (aeval (fun i => X i + C (u i)) p) = aeval _ p
  rw [comp_aeval_apply]
  simp

private theorem monomial_translation_degree (u : ι → K) (s : ι →₀ ℕ) (c : K) :
    let p := monomial s c
    polynomialTranslation u p - p ≠ 0 →
      (polynomialTranslation u p - p).totalDegree < p.totalDegree := by
  apply induction_on_monomial
    (motive := fun p => polynomialTranslation u p - p ≠ 0 →
      (polynomialTranslation u p - p).totalDegree < p.totalDegree)
  · intro a h
    simp [polynomialTranslation] at h
  · intro p i ih h
    have hp : p ≠ 0 := by
      rintro rfl
      simp at h
    have he : polynomialTranslation u (p * X i) - p * X i =
        (polynomialTranslation u p - p) * (X i + C (u i)) + p * C (u i) := by
      simp only [map_mul, polynomialTranslation, aeval_X]
      ring
    rw [he, totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
    apply Nat.lt_succ_of_le
    apply (totalDegree_add _ _).trans
    refine max_le ?_ ((totalDegree_mul _ _).trans (by simp))
    by_cases hd : polynomialTranslation u p - p = 0
    · simp [hd]
    · apply (totalDegree_mul _ _).trans
      have hx : (X i + C (u i)).totalDegree ≤ 1 :=
        (totalDegree_add _ _).trans (by simp)
      have := ih hd
      omega

/-- Every first translation difference drops the bounded total degree by one. -/
theorem totalDegree_translation_sub_le (u : ι → K) (p : MvPolynomial ι K)
    {j : ℕ} (hp : p.totalDegree ≤ j + 1) :
    (polynomialTranslation u p - p).totalDegree ≤ j := by
  classical
  let g := fun s => monomial s (p.coeff s)
  have he : polynomialTranslation u p - p =
      ∑ s ∈ p.support, (polynomialTranslation u (g s) - g s) := by
    simp [g, Finset.sum_sub_distrib, ← map_sum]
  rw [he]
  apply totalDegree_finsetSum_le
  intro s hs
  by_cases hz : polynomialTranslation u (g s) - g s = 0
  · simp [hz]
  · have hlt := monomial_translation_degree u s (p.coeff s) hz
    have hmon := totalDegree_monomial_le s (p.coeff s)
    have hsum := le_totalDegree hs
    change (polynomialTranslation u (g s) - g s).totalDegree < (g s).totalDegree at hlt
    change (g s).totalDegree ≤ s.sum (fun _ e => e) at hmon
    omega

/-- Recover a formal polynomial of small total degree from its values on natural nodes. -/
theorem eq_zero_of_natGrid_eval {σ : Type} {q : ℕ} [Fact q.Prime] [Finite σ]
    (p : MvPolynomial σ (ZMod q)) (hp : p.totalDegree < q)
    (h : ∀ z : σ → ℕ, eval (fun i => (z i : ZMod q)) p = 0) : p = 0 := by
  apply MvPolynomial.eq_zero_of_eval_eq_zero σ (ZMod q)
  · intro v
    simpa using h (fun i => (v i).val)
  · apply MvPolynomial.restrictTotalDegree_le_restrictDegree
    apply (MvPolynomial.mem_restrictTotalDegree ..).2
    rw [ZMod.card]
    omega

end AbcSubexp
