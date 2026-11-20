/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S8_Assembly.MainTheorem
public import AbcTwoNinths.Paper.S1_Statement.RadicalScaleAndTail

/-!
# A uniform height ceiling

Specialization of the two-ninths theorem gives a height bound on bounded
radicals and a linear upper bound for the logarithm of the height on the tail.

## Main results

* `AbcSubexp.exists_height_ceiling`
* `AbcSubexp.exists_height_onset`
-/

@[expose] public section

namespace AbcSubexp

open Real

/-- A global baseline in terms of the radical, specialized at the inner exponent 1/18. -/
theorem exists_baseline_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.logHeight ≤ C * (t.radical : ℝ) ^ ((5 : ℝ) / 18) := by
  obtain ⟨C, hC, h⟩ := AbcTwoNinths.Assembly.logBound (1 / 18) (by norm_num)
  refine ⟨C, hC, fun t => ?_⟩
  have ht : AbcTwoNinths.TwoNinthsTriple t.a t.b t.c :=
    ⟨t.apos, t.bpos, t.add, t.coprime⟩
  rw [← show (2 : ℝ) / 9 + 1 / 18 = 5 / 18 by norm_num]
  exact h t.a t.b t.c ht

/-- The inner exponent (1/18) gives exponential rate (5/6) in the radical scale. -/
theorem exists_height_ceiling :
    ∃ C : ℝ, 0 < C ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.logHeight ≤ C * exp (5 * t.thirdLogRadical / 6) := by
  obtain ⟨C, hC, h⟩ := exists_baseline_bound
  refine ⟨C, hC, fun t => ?_⟩
  have hR : (1 : ℝ) ≤ t.radical := AbcTwoNinths.Statement.radicalGeOne _
  have hpow : (t.radical : ℝ) ^ ((5 : ℝ) / 18) = exp (5 * t.thirdLogRadical / 6) := by
    rw [rpow_def_of_pos (zero_lt_one.trans_le hR)]
    congr 1
    change log (t.radical : ℝ) * _ = 5 * (log (t.radical : ℝ) / 3) / 6
    ring
  rw [← hpow]
  exact h t

/-- Beyond a single absolute onset the logarithm of the height is at most the scale. -/
theorem exists_height_onset : ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → log t.logHeight ≤ t.thirdLogRadical := by
  obtain ⟨C, hC, h⟩ := exists_height_ceiling
  refine ⟨6 * log C, fun t hx => ?_⟩
  have hc : 1 < t.c := by
    have := t.apos
    have := t.bpos
    have := t.add
    omega
  have ht : 0 < t.logHeight := log_pos (by exact_mod_cast hc)
  have hb := log_le_log ht (h t)
  rw [log_mul hC.ne' (exp_pos _).ne', log_exp] at hb
  linarith

end AbcSubexp
