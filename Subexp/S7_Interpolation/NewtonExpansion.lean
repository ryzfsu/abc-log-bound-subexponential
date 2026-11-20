/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Rational binomial expansion on the natural grid

This module formalizes the Newton expansion used in Section 7.

Expanding the powers in each monomial gives a finite linear combination of products
of binomial polynomials. The total degree bounds the sum of the coordinate indices.

## Main results

* `AbcSubexp.exists_binomialEvaluation_expansion`
* `AbcSubexp.eq_zero_of_eval_natGrid`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators
open Finset

private def powerCoefficient (d k : ℕ) : ℚ :=
  (Nat.stirlingSecond d k : ℚ) * k.factorial

private theorem pow_eq_sum_binomial (n d : ℕ) :
    (n : ℚ) ^ d = ∑ k ∈ range (d + 1), powerCoefficient d k * (AbcTwoNinths.Basic.binPoly k).eval (n : ℚ) := by
  have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n d
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, ← mul_assoc] at h
  simpa only [AbcTwoNinths.Basic.evalBinPoly, powerCoefficient] using
    (show (n : ℚ) ^ d = ∑ k ∈ range (d + 1),
      ((Nat.stirlingSecond d k : ℚ) * k.factorial) * n.choose k by exact_mod_cast h)

variable {m D : ℕ}

private def exponentBox (d : Fin m →₀ ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset fun i => range (d i + 1)

private theorem monomial_binomial_expansion (n : Fin m → ℕ) (d : Fin m →₀ ℕ) :
    (∏ i, (n i : ℚ) ^ d i) = ∑ k ∈ exponentBox d,
      (∏ i, powerCoefficient (d i) (k i)) * ∏ i, ((n i).choose (k i) : ℚ) := by
  simp_rw [pow_eq_sum_binomial, AbcTwoNinths.Basic.evalBinPoly]
  rw [prod_univ_sum]
  exact sum_congr rfl fun _ _ => prod_mul_distrib

/-- A rational polynomial of total degree at most `D` admits a rational binomial
expansion on the natural grid with all binomial multi-indices of weight at most `D`. -/
theorem exists_binomialEvaluation_expansion (P : MvPolynomial (Fin m) ℚ)
    (hP : P.totalDegree ≤ D) :
    ∃ w : (Fin m → ℕ) →₀ ℚ, (∀ k ∈ w.support, ∑ i, k i ≤ D) ∧
      ∀ n : Fin m → ℕ, MvPolynomial.eval (fun i => (n i : ℚ)) P =
        ∑ k ∈ w.support, w k * ∏ i, ((n i).choose (k i) : ℚ) := by
  classical
  let weight (d : Fin m →₀ ℕ) (k : Fin m → ℕ) :=
    P.coeff d * ∏ i, powerCoefficient (d i) (k i)
  let w : (Fin m → ℕ) →₀ ℚ := ∑ d ∈ P.support, ∑ k ∈ exponentBox d,
    Finsupp.single k (weight d k)
  refine ⟨w, ?_, ?_⟩
  · intro k hk
    by_contra! hlarge
    apply Finsupp.mem_support_iff.mp hk
    simp only [w, Finsupp.finsetSum_apply]
    refine sum_eq_zero fun d hd => sum_eq_zero fun j hj => ?_
    apply Finsupp.single_eq_of_ne
    intro heq
    subst j
    have hbox := Fintype.mem_piFinset.mp hj
    have hkd : ∑ i, k i ≤ ∑ i, d i :=
      sum_le_sum fun i _ => Nat.le_of_lt_succ (mem_range.mp (hbox i))
    have hdeg := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
    exact (Nat.not_lt_of_ge (hkd.trans (hdeg.trans hP))) hlarge
  · intro n
    let b (k : Fin m → ℕ) : ℚ := ∏ i, ((n i).choose (k i) : ℚ)
    change _ = Finsupp.linearCombination ℚ b w
    simp only [w, map_sum, Finsupp.linearCombination_single, smul_eq_mul]
    rw [MvPolynomial.eval_eq']
    refine sum_congr rfl fun d _ => ?_
    rw [monomial_binomial_expansion, mul_sum]
    exact sum_congr rfl fun k _ => (mul_assoc _ _ _).symm

/-- Vanishing at every natural point detects the zero rational polynomial. -/
theorem eq_zero_of_eval_natGrid (P : MvPolynomial (Fin m) ℚ)
    (h : ∀ n : Fin m → ℕ, MvPolynomial.eval (fun i => (n i : ℚ)) P = 0) : P = 0 := by
  apply MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℕ → ℚ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose n hn using fun i => hx i (Set.mem_univ i)
  simpa only [map_zero, ← funext hn] using h n

end AbcSubexp
