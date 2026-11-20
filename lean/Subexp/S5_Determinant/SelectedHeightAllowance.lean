/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.ArchimedeanBudget
public import Subexp.S5_Determinant.MinorComparison
public import Subexp.S5_Determinant.TwoBoxLocalBudget

/-!
# Height allowance for selected columns of the two boxes

Project each selected column to its base point and apply the finite- and
infinite-place bounds on that same family. Passing to the selected translate
costs one copy of the displacement height.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.HittingPrime

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

/-- The signed local maxima on the selected columns satisfy the native
height allowance used by the determinant comparison. -/
theorem selected_height_allowance {I : Type*} [Fintype I] [Nonempty I]
    (q : HittingPrime g) (b : BoxData q) (a : ℤ) (s : Fin (dimension ε) → ℤ)
    (f : I → q.BoxPoint ⊕ q.BoxPoint) :
    let γ := fun j => q.columnCharacter b a s (f j)
    minorRealBudget γ + (∑ p ∈ minorCharacterPrimes c.prime γ,
      (minorPrimeBudget γ p : ℝ) * log p) ≤ c.selectedHeightAllowance (AbcTwoNinths.Basic.rationalHeight (q.character a s)) := by
  classical
  let γ j := q.columnCharacter b a s (f j)
  let z (j : I) : q.BoxPoint := (f j).elim id id
  let A j := q.boxAxis b (z j)
  let Y j := q.boxVector (z j)
  have hbox j : q.box (A j) (Y j) := q.box_axis_mem b (z j)
  have hsel j : γ j = q.character (A j) (Y j) ∨
      γ j = q.character (A j + a) (Y j + s) := by
    cases h : f j <;> simp [γ, A, Y, z, h, columnCharacter]
  have hpr p (hp : p ∈ minorCharacterPrimes c.prime γ) : p.Prime := by
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_erase.mp hp).2
    exact (Finset.mem_union.mp hj).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have hcut : 0 < log c.cutoff :=
    log_pos ((by exact_mod_cast g.anchor_prime.one_lt : (1 : ℝ) < g.anchor).trans_le
      g.anchor_in_window.2)
  have hB : 0 ≤ c.transverseBudget := by
    have he : exponent ε ≤ 1 / 10 := min_le_right _ _
    have hl : 0 ≤ log (c.prime : ℝ) := log_nonneg (by exact_mod_cast c.prime_isPrime.one_le)
    unfold Contact.transverseBudget
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hl) (by positivity)
  apply (translated_box_budget q A Y hbox a s γ hsel _ hpr hcut hB).trans
  apply (add_le_add (add_le_add (real_box_budget q A Y hbox hcut hB) le_rfl) le_rfl).trans_eq
  unfold Contact.selectedHeightAllowance
  ring

end AbcSubexp.HittingPrime
