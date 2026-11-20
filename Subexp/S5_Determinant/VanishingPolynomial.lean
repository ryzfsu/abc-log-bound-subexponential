/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxMinorValuation
public import Subexp.S5_Determinant.MinorComparison
public import Subexp.S5_Determinant.SelectedHeightAllowance

/-! # A vanishing polynomial on the phase-restricted simplex -/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real

/-- Beyond a threshold depending only on the requested exponent, a nonzero
polynomial of degree at most the contact degree vanishes on all phase-restricted simplex points. -/
theorem exists_vanishing_polynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c) (q : HittingPrime g),
      X ≤ t.thirdLogRadical → BoxData q →
      ∃ P : MvPolynomial (Fin (dimension ε)) ℚ, P ≠ 0 ∧ P.totalDegree ≤ c.degree ∧
        ∀ z ∈ q.points c.radius, MvPolynomial.eval (fun i => (z i : ℚ)) P = 0 := by
  classical
  obtain ⟨X, hX⟩ := eventual_boxMinor_eq_zero hε
  refine ⟨X, ?_⟩
  intro t c g q hx b
  obtain ⟨a, s, hne, _, hJ⟩ := b.translation
  let V := ⌈degreeMargin ε * c.depth⌉₊
  let I := simplexRows (dimension ε) c.depth
  let J := simplexRows (dimension ε) V
  have he := exponentPos hε
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have hn : 0 < c.depth := by
    by_contra! h
    have hd := (mul_pos (mul_pos zero_lt_two he) hh).trans c.depth_share
    simp [Nat.eq_zero_of_le_zero h] at hd
  have hzero : (0 : Fin (dimension ε) → ℕ) ∈ I := by simpa [I] using hn
  let : Nonempty (↥I ⊕ ↥J) := ⟨Sum.inl ⟨0, hzero⟩⟩
  apply q.exists_vanishing_polynomial_of_box_minors b a s (HittingPrime.columnOrigin s)
    hne I J (d₀ := c.depth - 1) (d₁ := V - 1)
  · intro i hi
    exact Nat.le_sub_one_of_lt (mem_simplexRows.mp hi)
  · intro j hj
    exact Nat.le_sub_one_of_lt (mem_simplexRows.mp hj)
  · exact c.rowDegree_sum_le hε
  · intro f
    apply hX t c hx g q b a s hJ f
    · intro hdet
      rw [← Finset.sum_coe_sort J (fun k => c.depth - ∑ i, k i)]
      exact q.boxMinor_valuation_lower b a s V f hdet
    · exact q.selected_height_allowance b a s f

end AbcSubexp
