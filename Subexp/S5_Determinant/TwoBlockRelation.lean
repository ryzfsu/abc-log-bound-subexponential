/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomial relations from vanishing maximal minors

The two blocks consist of polynomial rows and polynomial rows multiplied by
a character. A dependence of their evaluations gives two polynomials, at least
one nonzero, satisfying the corresponding relation at every column.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open scoped BigOperators
open MvPolynomial

variable {σ I J F : Type*} [Fintype I] [Fintype J] [Fintype F]

/-- Evaluation of two families of polynomials with a character on the second block. -/
def twoBlockMatrix (U : I → MvPolynomial σ ℚ) (V : J → MvPolynomial σ ℚ)
    (y : F → σ → ℚ) (γ : F → ℚ) : Matrix (I ⊕ J) F ℚ :=
  fun row col => row.elim (fun i => eval (y col) (U i))
    (fun j => γ col * eval (y col) (V j))

/-- Vanishing of all maximal minors of the two blocks supplies a nontrivial
polynomial relation with the degree bounds of the two row families. -/
theorem exists_twoBlockRelation_of_minors [DecidableEq I] [DecidableEq J]
    (U : I → MvPolynomial σ ℚ) (V : J → MvPolynomial σ ℚ)
    (hU : LinearIndependent ℚ U) (hV : LinearIndependent ℚ V)
    (y : F → σ → ℚ) (γ : F → ℚ) {d₀ d₁ : ℕ}
    (du : ∀ i, (U i).totalDegree ≤ d₀) (dv : ∀ j, (V j).totalDegree ≤ d₁)
    (hminor : ∀ f : (I ⊕ J) ↪ F, ((twoBlockMatrix U V y γ).submatrix id f).det = 0) :
    ∃ P₀ P₁ : MvPolynomial σ ℚ, (P₀ ≠ 0 ∨ P₁ ≠ 0) ∧
      P₀.totalDegree ≤ d₀ ∧ P₁.totalDegree ≤ d₁ ∧
      ∀ c, eval (y c) P₀ + γ c * eval (y c) P₁ = 0 := by
  classical
  let M := twoBlockMatrix U V y γ
  have hd : ¬ LinearIndependent ℚ M.row := by
    intro hi
    obtain ⟨f, hf⟩ := AbcTwoNinths.Basic.minorOfIndependentRows M hi
    exact hf (hminor f)
  rw [Fintype.linearIndependent_iff] at hd
  push Not at hd
  obtain ⟨w, hw, row, hrow⟩ := hd
  let P₀ := ∑ i, w (.inl i) • U i
  let P₁ := ∑ j, w (.inr j) • V j
  refine ⟨P₀, P₁, ?_, ?_, ?_, ?_⟩
  · by_contra! hz
    cases row with
    | inl i => exact hrow (Fintype.linearIndependent_iff.mp hU _ hz.1 i)
    | inr j => exact hrow (Fintype.linearIndependent_iff.mp hV _ hz.2 j)
  · exact totalDegree_finsetSum_le fun i _ => (totalDegree_smul_le _ _).trans (du i)
  · exact totalDegree_finsetSum_le fun j _ => (totalDegree_smul_le _ _).trans (dv j)
  · intro c
    have hc := congrFun hw c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type, Matrix.row, M, twoBlockMatrix, Sum.elim_inl, Sum.elim_inr] at hc
    simpa only [P₀, P₁, map_sum, smul_eval, Finset.mul_sum, mul_left_comm]
      using hc

end AbcSubexp
