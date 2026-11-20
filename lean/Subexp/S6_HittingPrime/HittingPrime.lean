/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.GroupedSeparation
public import Subexp.S6_HittingPrime.HittingPrimeSelection
public import Subexp.S6_HittingPrime.NativeWindowTail
public import Subexp.S6_HittingPrime.SeparatedMisses

/-!
# Joint selection of an interpolation prime and a list of generators

For sufficiently large radicals, the count of times that miss every list is
smaller than the number of primes in the search window. One prime therefore
meets the phase targets for all coordinates of the same list.
-/

@[expose] public section

open Real
open AbcSubexp.Parameters

namespace AbcSubexp

/-- Above a uniform radical threshold, an interpolation prime in the prescribed
window hits every phase target for one list of generators. -/
theorem exists_hitting_prime (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c),
      X ≤ t.thirdLogRadical → Nonempty (HittingPrime g) := by
  classical
  let m := dimension ε
  let η := phaseTolerance ε
  obtain ⟨hη, hη'⟩ := phaseToleranceBounds hε
  obtain ⟨F, _, hsmall⟩ := exists_cosineDegree m hη hη'
  let a := 1 - ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2
  have hpow : 1 ≤ (2 * (F : ℝ) + 1) ^ m := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) F])
  have hinv := inv_le_one_of_one_le₀ hpow
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a < 1 := by dsimp [a]; linarith [inv_pos.mpr (zero_lt_one.trans_le hpow)]
  obtain ⟨X₁, hselect⟩ := hittingPrime_of_missed_rows_bound ε hε ha ha'
  obtain ⟨X₂, hradius⟩ := Contact.exists_hittingWindow_bounds hε
  obtain ⟨X₃, hsep⟩ := GroupedTuple.eventually_frequency_separation hε F
  refine ⟨max X₁ (max X₂ X₃), ?_⟩
  intro t c g hx
  obtain ⟨hx₁, hx₂, hx₃⟩ := (max_le_iff.mp hx).imp_right max_le_iff.mp
  apply hselect t c g hx₁ (hradius c hx₂).2 (missedTimes c.hittingWindowEnd g.hitsRow)
    (fun _ hq hm => prime_mem_missedTimes_of_forall_miss g.hitsRow hq hm)
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source := lt_of_lt_of_le
    (show 0 < exponent ε / 2 * exp (3 * exponent ε * t.thirdLogRadical) by positivity) c.axial_height_lower
  let δ := exp (sqrt t.thirdLogRadical) / (4 * AbcTwoNinths.Basic.rationalHeight c.source)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hharm : 1 / (2 * δ) = (2 * AbcTwoNinths.Basic.rationalHeight c.source) / exp (sqrt t.thirdLogRadical) := by
    dsimp [δ]
    field_simp
    ring
  have hcount := separated_missedTimes_card_le F c.hittingWindowEnd g.slope
    (fun i => (i.val : ℝ) / m) hη.le hδ hsmall.le (hsep g hx₃)
  rw [hharm] at hcount
  rw [mul_div_assoc]
  exact hcount

end AbcSubexp
