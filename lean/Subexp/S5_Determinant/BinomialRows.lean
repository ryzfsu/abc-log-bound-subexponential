/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing
public import AbcTwoNinths.Paper.S7_Terminal.InterpolationMinorNonvanishing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Multivariate binomial rows

The polynomial of a multi-index is the product of the released univariate binomial
polynomials in its coordinates. At the point indexed by the row itself the value is
one, and only coordinatewise smaller indices can have nonzero values there.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open scoped BigOperators
open MvPolynomial

variable {m : ℕ}

/-- The rational binomial polynomial used for a transverse row of the determinant. -/
def binomialRowPolynomial (k : Fin m → ℕ) : MvPolynomial (Fin m) ℚ :=
  ∏ i, Polynomial.toMvPolynomial i (AbcTwoNinths.Basic.binPoly (k i))

/-- At a natural grid point the row is the product of ordinary binomial coefficients. -/
theorem eval_binomialRowPolynomial_nat (k x : Fin m → ℕ) :
    eval (fun i => (x i : ℚ)) (binomialRowPolynomial k) =
      ∏ i, ((x i).choose (k i) : ℚ) := by
  simp only [binomialRowPolynomial, map_prod, eval_toMvPolynomial, AbcTwoNinths.Basic.evalBinPoly]

private theorem totalDegree_univariate_le (p : Polynomial ℚ) (i : Fin m) :
    (Polynomial.toMvPolynomial i p).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X]
  apply totalDegree_finsetSum_le
  intro n hn
  exact (totalDegree_mul _ _).trans (by simpa using Polynomial.le_natDegree_of_mem_supp n hn)

/-- The total degree is at most the weight of the row index. -/
theorem totalDegree_binomialRowPolynomial_le (k : Fin m → ℕ) :
    (binomialRowPolynomial k).totalDegree ≤ ∑ i, k i := by
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (totalDegree_univariate_le _ i).trans_eq
    (AbcTwoNinths.Terminal.binomialPolynomialDegree (k i))

/-- Binomial rows with pairwise distinct exponent vectors are linearly independent. -/
theorem linearIndependent_binomialRowPolynomial {I : Type*} [Fintype I]
    (k : I → Fin m → ℕ) (hk : Function.Injective k) :
    LinearIndependent ℚ (fun j => binomialRowPolynomial (k j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hzero (n : ℕ) : ∀ j, (∑ i, k j i) = n → w j = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have he := congrArg (eval (fun i => (k j i : ℚ))) hw
      simp only [map_sum, smul_eval, eval_binomialRowPolynomial_nat, map_zero] at he
      rw [Finset.sum_eq_single j] at he
      · simpa using he
      · intro l _ hlj
        by_cases hle : ∀ i, k l i ≤ k j i
        · have hlt : ∃ i, k l i < k j i := by
            by_contra! h
            exact hlj (hk (funext (fun i => le_antisymm (hle i) (h i))))
          obtain ⟨i, hi⟩ := hlt
          have hwlt : (∑ t, k l t) < ∑ t, k j t :=
            Finset.sum_lt_sum (fun t _ => hle t) ⟨i, Finset.mem_univ _, hi⟩
          rw [ih _ (hwlt.trans_eq hj) l rfl, zero_mul]
        · obtain ⟨i, hi⟩ := not_forall.mp hle
          have hprod : (∏ t, ((k j t).choose (k l t) : ℚ)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hi)])
          rw [hprod, mul_zero]
      · simp
  exact fun j => hzero _ j rfl

end AbcSubexp
