/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S7_Interpolation.GridColor
public import Subexp.S7_Interpolation.PolynomialTranslation

/-!
# Polynomial interpolation on consecutive colors

This module formalizes the consecutive-colour interpolation step of Section 7.

The color-class induction applies to ordinary multivariate polynomials evaluated at natural simplex nodes.

## Main results
* `AbcSubexp.polynomial_eq_zero_of_consecutive_colors`
-/

@[expose] public section

namespace AbcSubexp

open MvPolynomial

/-- Evaluating a polynomial on natural nodes preserves its finite-difference degree bound. -/
theorem gridDegreeLE_eval {m : ℕ} {K : Type*} [Field K] (j : ℕ)
    (p : MvPolynomial (Fin m) K) (hp : p.totalDegree ≤ j) :
    gridDegreeLE j (fun z => eval (fun i => (z i : K)) p) := by
  induction j generalizing p with
  | zero =>
    have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp)
    intro z
    rw [hC]
    simp
  | succ j ih =>
    intro i
    let u : Fin m → K := fun k => (((Pi.single i 1 : Fin m → ℕ) k : ℕ) : K)
    let d := polynomialTranslation u p - p
    have hd : d.totalDegree ≤ j := totalDegree_translation_sub_le u p hp
    convert ih d hd using 1
    funext z
    simp [d, eval_polynomialTranslation, u, Pi.add_apply]

/-- A degree-`j` polynomial over the prime field is determined by the points of
the radius-`j+1` simplex whose colors lie in any `j+1` consecutive residues. -/
theorem polynomial_eq_zero_of_consecutive_colors {m q j : ℕ} [NeZero m] [Fact q.Prime]
    (hq : j < q) (p : MvPolynomial (Fin m) (ZMod q)) (hp : p.totalDegree ≤ j)
    (a : ZMod m) (hvan : ∀ z : Fin m → ℕ, (∑ i, z i) ≤ j + 1 →
      (∃ r : ℕ, r ≤ j ∧ simplexColor z = a + (r : ZMod m)) →
      eval (fun i => (z i : ZMod q)) p = 0) : p = 0 := by
  apply eq_zero_of_natGrid_eval p (hp.trans_lt hq)
  exact gridDegreeLE_eq_zero_of_consecutive_colors _ (gridDegreeLE_eval j p hp) a hvan

end AbcSubexp
