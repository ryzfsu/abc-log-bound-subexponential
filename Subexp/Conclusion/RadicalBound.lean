/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S2_Parameters.HeightCeiling
public import Subexp.S1_Statement.Statement

/-!
# The radical bound from its tail

The two-ninths height ceiling bounds every triple below the onset. Above
it, the tail uses an exponent at most the exponent requested by the caller.

## Main results

* `AbcSubexp.subexp_of_tail`
-/

@[expose] public section

namespace AbcSubexp

open Real

/-- A tail estimate for ordered triples and a global baseline give one constant for all triples. -/
theorem bound_of_eventual_exclusion (ε : ℝ) (hε : 0 < ε)
    (baseline : ∃ C : ℝ, 0 < C ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.logHeight ≤ C * (t.radical : ℝ) ^ ((5 : ℝ) / 18))
    (tail : ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → t.a ≤ t.b →
      t.logHeight < exp (3 * min ε (1 / 10) * t.thirdLogRadical)) :
    ∃ B : ℝ, 0 < B ∧ ∀ a b c : ℕ, AbcTwoNinths.TwoNinthsTriple a b c →
      log c ≤ B * (AbcTwoNinths.radNat (a * b * c) : ℝ) ^ ε := by
  obtain ⟨X, htail⟩ := tail
  obtain ⟨C, hC, hcap⟩ := baseline
  let B := max 1 (C * exp (3 * X) ^ ((5 : ℝ) / 18))
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, zero_lt_one.trans_le hB, ?_⟩
  intro a b c ht
  let t : AbcTwoNinths.Basic.Triple := ⟨a, b, c, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  change t.logHeight ≤ B * (t.radical : ℝ) ^ ε
  have hR : (1 : ℝ) ≤ t.radical := AbcTwoNinths.Statement.radicalGeOne _
  have hRp : (0 : ℝ) < t.radical := zero_lt_one.trans_le hR
  by_cases hx : X ≤ t.thirdLogRadical
  · have hsmall : t.logHeight < exp (3 * min ε (1 / 10) * t.thirdLogRadical) := by
      by_cases hab : a ≤ b
      · exact htail t hx hab
      · let t' : AbcTwoNinths.Basic.Triple :=
          ⟨b, a, c, ht.2.1, ht.1, (Nat.add_comm b a).trans ht.2.2.1, ht.2.2.2.symm⟩
        have heq : t'.thirdLogRadical = t.thirdLogRadical := by
          change log (AbcTwoNinths.Basic.radical (b * a * c) : ℝ) / 3 =
            log (AbcTwoNinths.Basic.radical (a * b * c) : ℝ) / 3
          rw [Nat.mul_comm b a]
        have hs := htail t' (heq.symm ▸ hx) (le_of_not_ge hab)
        rw [heq] at hs
        exact hs
    have hpower : exp (3 * min ε (1 / 10) * t.thirdLogRadical) = (t.radical : ℝ) ^ min ε (1 / 10) := by
      rw [rpow_def_of_pos hRp]
      congr 1
      change 3 * _ * (log (t.radical : ℝ) / 3) = _
      ring
    calc
      t.logHeight ≤ (t.radical : ℝ) ^ min ε (1 / 10) := hsmall.le.trans hpower.le
      _ ≤ (t.radical : ℝ) ^ ε := rpow_le_rpow_of_exponent_le hR (min_le_left _ _)
      _ ≤ B * (t.radical : ℝ) ^ ε := le_mul_of_one_le_left (rpow_nonneg hRp.le _) hB
  · have hlog : log (t.radical : ℝ) ≤ 3 * X := by
      change ¬ X ≤ log (t.radical : ℝ) / 3 at hx
      linarith
    have hscale := (log_le_iff_le_exp hRp).mp hlog
    calc
      t.logHeight ≤ C * (t.radical : ℝ) ^ ((5 : ℝ) / 18) := hcap t
      _ ≤ C * exp (3 * X) ^ ((5 : ℝ) / 18) := mul_le_mul_of_nonneg_left
        (rpow_le_rpow hRp.le hscale (by norm_num)) hC.le
      _ ≤ B := le_max_right _ _
      _ ≤ B * (t.radical : ℝ) ^ ε :=
        le_mul_of_one_le_right (zero_le_one.trans hB) (one_le_rpow hR hε.le)

/-- A uniform large-radical estimate for each capped exponent implies the public bound. -/
theorem subexp_of_tail
    (tail : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical →
      t.logHeight < exp (3 * min ε (1 / 10) * t.thirdLogRadical)) : subexpStatement := by
  intro ε hε
  obtain ⟨X, htail⟩ := tail ε hε
  exact bound_of_eventual_exclusion ε hε exists_baseline_bound ⟨X, fun t hx _ => htail t hx⟩

end AbcSubexp
