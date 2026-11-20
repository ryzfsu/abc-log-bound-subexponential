/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Interpolation in the high digits

This module formalizes the high-digit interpolation step of Section 7.

A set detecting polynomials of degree less than the characteristic also detects
the coefficients of the corresponding multivariate integral binomial functions.

## Main results
* `AbcSubexp.highDigitCoefficients_eq_zero`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators
open MvPolynomial

variable {m q : ℕ} [Fact q.Prime]

private noncomputable def binomialFactor (i : Fin m) (n : ℕ) :
    MvPolynomial (Fin m) (ZMod q) :=
  C (n.factorial : ZMod q)⁻¹ *
    ∏ k ∈ Finset.range n, (X i - C (k : ZMod q))

private theorem eval_binomialFactor (i : Fin m) {n : ℕ} (hn : n < q)
    (y : Fin m → ℕ) :
    eval (fun j => (y j : ZMod q)) (binomialFactor i n) =
      ((y i).choose n : ZMod q) := by
  have hfac : (n.factorial : ZMod q) ≠ 0 := by
    rwa [ne_eq, ZMod.natCast_eq_zero_iff, (Fact.out : q.Prime).dvd_factorial, not_le]
  simp only [binomialFactor, map_mul, eval_C, map_prod, map_sub, eval_X]
  rw [← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc]
  simp [hfac]

private theorem degree_binomialFactor (i : Fin m) (n : ℕ) :
    (binomialFactor (q := q) i n).totalDegree ≤ n := by
  unfold binomialFactor
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, 1 := Finset.sum_le_sum fun k _ =>
      (totalDegree_sub_C_le _ _).trans (totalDegree_X (R := ZMod q) i).le
    _ = n := by simp

/-- On a witness set detecting all polynomials through degree `j < q`, a vanishing
linear combination of binomial columns of that degree has zero coefficients. -/
theorem highDigitCoefficients_eq_zero {j : ℕ} (hj : j < q)
    (H : Finset (Fin m → ℕ)) (W : (Fin m → ℕ) → Prop) (c : (Fin m → ℕ) → ZMod q)
    (hdeg : ∀ a ∈ H, ∑ i, a i ≤ j)
    (hdet : ∀ P : MvPolynomial (Fin m) (ZMod q), P.totalDegree ≤ j →
      (∀ y, W y → eval (fun i => (y i : ZMod q)) P = 0) → P = 0)
    (hrow : ∀ y, W y → ∑ a ∈ H, c a * ∏ i, ((y i).choose (a i) : ZMod q) = 0) :
    ∀ a ∈ H, c a = 0 := by
  classical
  let P : MvPolynomial (Fin m) (ZMod q) :=
    ∑ a ∈ H, C (c a) * ∏ i, binomialFactor i (a i)
  have evalP (y : Fin m → ℕ) :
      eval (fun i => (y i : ZMod q)) P =
      ∑ a ∈ H, c a * ∏ i, ((y i).choose (a i) : ZMod q) := by
    simp only [P, map_sum, map_mul, eval_C, map_prod]
    refine Finset.sum_congr rfl fun a ha => congrArg (c a * ·) ?_
    exact Finset.prod_congr rfl fun i _ => eval_binomialFactor i
      (lt_of_le_of_lt ((Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans (hdeg a ha)) hj) y
  have hP : P = 0 := by
    apply hdet
    · apply totalDegree_finsetSum_le
      intro a ha
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_finsetProd _ _).trans
        ((Finset.sum_le_sum fun i _ => degree_binomialFactor i (a i)).trans (hdeg a ha))
    · intro y hy
      rw [evalP, hrow y hy]
  intro b hb
  induction hn : ∑ i, b i using Nat.strong_induction_on generalizing b with
  | h n ih =>
    have he := evalP b
    rw [hP, map_zero] at he
    rw [Finset.sum_eq_single b] at he
    · simpa using he.symm
    · intro a ha hne
      by_cases hab : a ≤ b
      · have hx : ∃ i, a i < b i := by
          by_contra! h
          exact hne (le_antisymm hab h)
        have hs := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hab i)
          (hx.imp fun i hi => ⟨Finset.mem_univ i, hi⟩)
        rw [hn] at hs
        rw [ih _ hs a ha rfl, zero_mul]
      · have hx : ∃ i, b i < a i := by simpa [Pi.le_def] using hab
        obtain ⟨i, hi⟩ := hx
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi]),
          mul_zero]
    · exact fun h => (h hb).elim

end AbcSubexp
