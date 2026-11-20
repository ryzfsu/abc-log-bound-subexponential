/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S4_ExteriorE2.ResidueLattice
public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume
public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Projected height in rational prime coordinates

The sum of transverse valuations on all radical primes equals the weighted
projected cost on the old support in Section 4.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting


/-- Radical primes outside the old support contribute zero transverse height.
At the old primes, reindexing the roof first identifies the rational valuation
sum with the cost of the projected exponent vector. -/
theorem transverseValuations_eq_projectedCost (S T : Finset ℕ) (roof : ℕ)
    (axis u : ℚ) (s w : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof))
    (hST : S ⊆ T)
    (hs : s (.inl ()) = padicValRat roof axis)
    (hw : w (.inl ()) = padicValRat roof u)
    (hsi : ∀ j : AbcTwoNinths.ExteriorE2.OldIndex S roof, s (.inr j) = padicValRat j.val axis)
    (hwi : ∀ j : AbcTwoNinths.ExteriorE2.OldIndex S roof, w (.inr j) = padicValRat j.val u)
    (hzero : ∀ p ∈ T, p ∉ S → padicValRat p axis = 0 ∧ padicValRat p u = 0) :
    (∑ p ∈ T.erase roof,
      |(padicValRat p u : ℝ) - (padicValRat roof u : ℝ) / (padicValRat roof axis : ℝ) *
        (padicValRat p axis : ℝ)| * Real.log (p : ℝ)) =
      AbcTwoNinths.ExteriorE2.cost (fun j : AbcTwoNinths.ExteriorE2.OldIndex S roof => Real.log (j.val : ℝ)) (AbcTwoNinths.ExteriorE2.project s w) := by
  classical
  let f (p : ℕ) := |(padicValRat p u : ℝ) -
    (padicValRat roof u : ℝ) / (padicValRat roof axis : ℝ) * (padicValRat p axis : ℝ)| *
    Real.log (p : ℝ)
  calc
    (∑ p ∈ T.erase roof, f p) = ∑ p ∈ S.erase roof, f p := by
      symm
      apply Finset.sum_subset (Finset.erase_subset_erase roof hST)
      intro p hp ht
      have h := Finset.mem_erase.mp hp
      have hz := hzero p h.2 (fun hS => ht (Finset.mem_erase.mpr ⟨h.1, hS⟩))
      simp [f, hz.1, hz.2]
    _ = ∑ j : AbcTwoNinths.ExteriorE2.OldIndex S roof, f j.val := (Finset.sum_coe_sort (S.erase roof) f).symm
    _ = _ := by
      unfold AbcTwoNinths.ExteriorE2.cost
      apply Finset.sum_congr rfl
      intro j _
      change f j.val = Real.log (j.val : ℝ) * |(w (.inr j) : ℝ) -
        (w (.inl ()) : ℝ) / (s (.inl ()) : ℝ) * (s (.inr j) : ℝ)|
      rw [hsi, hwi, hs, hw, mul_comm]

end AbcSubexp.TupleCounting
