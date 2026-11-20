/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxLocalBudget
public import Subexp.Prerequisites.MinorComparison

/-!
# Local maxima on a translated family of columns

Taking any mixture of base and translated columns increases the sum of the
local maxima by at most the rational height of one translation.

## Main results
* `AbcSubexp.twoBox_local_budget`
* `AbcSubexp.translated_box_budget`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real
open scoped BigOperators

private theorem translation_cost (u : ℚ) (hu : u ≠ 0) (S : Finset ℕ)
    (hS : ∀ q ∈ S, Nat.Prime q) :
    max (log |(u : ℝ)|) 0 +
      ∑ p ∈ S, max (-(padicValRat p u : ℝ)) 0 * log (p : ℝ) ≤ AbcTwoNinths.Basic.rationalHeight u := by
  have hnum : 0 < u.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hu)
  have hdenR : (0 : ℝ) < u.den := Nat.cast_pos.mpr u.den_pos
  have hnumR : (0 : ℝ) < u.num.natAbs := Nat.cast_pos.mpr hnum
  have hlog : log |(u : ℝ)| = log (u.num.natAbs : ℝ) - log (u.den : ℝ) := by
    have hc : (u : ℝ) = (u.num : ℝ) / (u.den : ℝ) := by
      exact_mod_cast u.num_div_den.symm
    rw [hc, abs_div, abs_of_pos hdenR, ← Int.cast_abs, ← Nat.cast_natAbs, log_div hnumR.ne' hdenR.ne']
  have hd : (∑ p ∈ S, (padicValNat p u.den : ℝ) * log (p : ℝ)) ≤ log (u.den : ℝ) := by
    have H := AbcSubexp.Prerequisites.sameIntegerArch (u.den : ℤ) (by exact_mod_cast u.den_nz) S
      (fun p => padicValNat p u.den) hS (fun p _ => by exact_mod_cast
        (pow_padicValNat_dvd (p := p) (n := u.den)))
    simpa using H
  have hfinite : (∑ p ∈ S, max (-(padicValRat p u : ℝ)) 0 * log (p : ℝ)) ≤ log (u.den : ℝ) := by
    apply le_trans _ hd
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (log_natCast_nonneg p)
    rw [padicValRat_def, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    exact max_le (by linarith [show (0 : ℝ) ≤ padicValInt p u.num by positivity]) (by positivity)
  apply (add_le_add le_rfl hfinite).trans
  rw [hlog, ← max_add_add_right, sub_add_cancel, zero_add]
  unfold AbcTwoNinths.Basic.rationalHeight
  rw [Nat.cast_max]
  exact max_le (log_le_log hnumR (le_max_left _ _)) (log_le_log hdenR (le_max_right _ _))

/-- Columnwise choice of an untranslated or translated character costs one translation
height in the sum of all local maxima, including arbitrary signed finite maxima. -/
theorem twoBox_local_budget {I : Type*} [Fintype I] [Nonempty I]
    (base : I → ℚ) (hb : ∀ j, base j ≠ 0) (u : ℚ) (hu : u ≠ 0)
    (selected : I → ℚ) (hs : ∀ j, selected j = base j ∨ selected j = base j * u)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    minorRealBudget selected + ∑ p ∈ S, (minorPrimeBudget selected p : ℝ) * log (p : ℝ) ≤
      minorRealBudget base + (∑ p ∈ S, (minorPrimeBudget base p : ℝ) * log (p : ℝ)) + AbcTwoNinths.Basic.rationalHeight u := by
  classical
  have hreal : minorRealBudget selected ≤ minorRealBudget base + max (log |(u : ℝ)|) 0 := by
    apply Finset.sup'_le
    intro j _
    have hle : log |(base j : ℝ)| ≤ minorRealBudget base :=
      Finset.le_sup' (fun i => log |(base i : ℝ)|) (Finset.mem_univ j)
    rcases hs j with hj | hj
    · rw [hj]
      linarith [le_max_right (log |(u : ℝ)|) 0]
    · rw [hj, Rat.cast_mul, abs_mul, log_mul (abs_ne_zero.mpr (by exact_mod_cast hb j))
        (abs_ne_zero.mpr (by exact_mod_cast hu))]
      exact add_le_add hle (le_max_left _ _)
  have hplace (p : ℕ) (hp : p ∈ S) :
      (minorPrimeBudget selected p : ℝ) * log (p : ℝ) ≤
      (minorPrimeBudget base p : ℝ) * log (p : ℝ) + max (-(padicValRat p u : ℝ)) 0 * log (p : ℝ) := by
    let : Fact p.Prime := ⟨hS p hp⟩
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (log_natCast_nonneg p)
    have h : minorPrimeBudget selected p ≤ minorPrimeBudget base p + max (-padicValRat p u) 0 := by
      apply Finset.sup'_le
      intro j _
      have hle : -padicValRat p (base j) ≤ minorPrimeBudget base p :=
        Finset.le_sup' (fun i => -padicValRat p (base i)) (Finset.mem_univ j)
      rcases hs j with hj | hj
      · rw [hj]
        omega
      · rw [hj, padicValRat.mul (hb j) hu]
        omega
    exact_mod_cast h
  have hf := Finset.sum_le_sum hplace
  rw [Finset.sum_add_distrib] at hf
  linarith [translation_cost u hu S hS]

/-- Upper-bound interface for a selected square minor from the two native lattice boxes. -/
theorem translated_box_budget {I : Type*} [Fintype I] [Nonempty I]
    {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c} (q : HittingPrime g)
    (a : I → ℤ) (y : I → Fin (dimension ε) → ℤ) (hbox : ∀ j, q.box (a j) (y j))
    (a₁ : ℤ) (y₁ : Fin (dimension ε) → ℤ)
    (selected : I → ℚ) (hs : ∀ j, selected j = q.character (a j) (y j) ∨
      selected j = q.character (a j + a₁) (y j + y₁))
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (ht : 0 < log c.cutoff) (hB : 0 ≤ c.transverseBudget) :
    minorRealBudget selected + ∑ p ∈ S, (minorPrimeBudget selected p : ℝ) * log (p : ℝ) ≤
      minorRealBudget (fun j => q.character (a j) (y j)) +
        (c.width * AbcTwoNinths.Basic.rationalHeight c.source +
         (dimension ε : ℝ)^2 * c.transverseBudget / log c.cutoff * (t.thirdLogRadical / log t.thirdLogRadical) +
         (dimension ε + 1) * c.transverseBudget) + AbcTwoNinths.Basic.rationalHeight (q.character a₁ y₁) := by
  apply le_trans (twoBox_local_budget (fun j => q.character (a j) (y j))
    (fun j => q.character_ne_zero _ _) _ (q.character_ne_zero a₁ y₁) selected
    (fun j => by simpa only [q.character_add] using hs j) S hS)
  exact add_le_add (add_le_add le_rfl (finite_box_budget q a y hbox ht hB S hS)) le_rfl

end AbcSubexp
