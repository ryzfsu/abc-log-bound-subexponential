/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Lucas factorization for binomial evaluation

The multivariate binomial evaluation in Section 7 factors into evaluations on the remainders
and the quotients. The remainder evaluation is triangular for the coordinatewise order.

## Main results

* `AbcSubexp.digitBinomial_split`
* `AbcSubexp.digitBinomial_split_digits`
* `AbcSubexp.digitBinomial_self`
* `AbcSubexp.digitBinomial_zero_of_not_le`
-/

@[expose] public section

namespace AbcSubexp

/-- The product of the one-variable binomial evaluations in `ZMod q`. -/
def digitBinomial (q : ℕ) {m : ℕ} (row col : Fin m → ℕ) : ZMod q :=
  ∏ i, ((row i).choose (col i) : ZMod q)

private theorem choose_cast_split {q : ℕ} [Fact q.Prime] (n k : ℕ) :
    (n.choose k : ZMod q) =
      ((n % q).choose (k % q) : ZMod q) * ((n / q).choose (k / q) : ZMod q) := by
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ q).2
    Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- Lucas factorization of the multivariate binomial entry into low and high digits. -/
theorem digitBinomial_split (q : ℕ) [Fact q.Prime] {m : ℕ} (row col : Fin m → ℕ) :
    digitBinomial q row col =
      digitBinomial q (fun i => row i % q) (fun i => col i % q) *
        digitBinomial q (fun i => row i / q) (fun i => col i / q) := by
  unfold digitBinomial
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => choose_cast_split (row i) (col i)

/-- Lucas factorization for rows and columns presented in terms of their digits. -/
theorem digitBinomial_split_digits (q : ℕ) [Fact q.Prime] {m : ℕ}
    (y u r s : Fin m → ℕ) (hr : ∀ i, r i < q) (hs : ∀ i, s i < q) :
    digitBinomial q (fun i => q * y i + r i) (fun i => q * u i + s i) =
      digitBinomial q r s * digitBinomial q y u := by
  rw [digitBinomial_split]
  simp only [Nat.mul_add_mod_self_left, Nat.mul_add_div (Fact.out : q.Prime).pos,
    fun i => Nat.mod_eq_of_lt (hr i), fun i => Nat.mod_eq_of_lt (hs i),
    fun i => Nat.div_eq_of_lt (hr i), fun i => Nat.div_eq_of_lt (hs i), Nat.add_zero]

/-- Each diagonal entry of the multivariate binomial evaluation is one. -/
theorem digitBinomial_self (q : ℕ) {m : ℕ} (row : Fin m → ℕ) :
    digitBinomial q row row = 1 := by
  simp [digitBinomial]

/-- A column that exceeds the row in any coordinate has binomial entry zero. -/
theorem digitBinomial_zero_of_not_le (q : ℕ) {m : ℕ} {row col : Fin m → ℕ}
    (h : ¬ col ≤ row) : digitBinomial q row col = 0 := by
  classical
  change ¬ (∀ i, col i ≤ row i) at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])

end AbcSubexp
