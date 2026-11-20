/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.CharacterHeight
public import Subexp.S6_HittingPrime.CutoffMargin
public import Subexp.S6_HittingPrime.FrequencySeparation

/-!
# Separation of the roof phases

The grouped height floor applied at the nearest integral axial shift separates
all bounded nonzero integer combinations of the actual roof slopes.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Real Parameters Filter
open scoped BigOperators

/-- For a fixed frequency cutoff, every nonzero bounded joint frequency stays
away from the integers on the contact tail. -/
theorem GroupedTuple.eventually_frequency_separation {ε : ℝ} (hε : 0 < ε) (F : ℕ) :
    ∃ X : ℝ, ∀ {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} (g : GroupedTuple c), X ≤ t.thirdLogRadical →
      ∀ y : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ → Fin (dimension ε) → ℤ, y ≠ 0 →
        (∑ b, ∑ i, (y b i).natAbs) ≤ ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ * dimension ε * F →
        exp (sqrt t.thirdLogRadical) / (4 * AbcTwoNinths.Basic.rationalHeight c.source) ≤
          |(∑ b, ∑ i, (y b i : ℝ) * g.slope b i) -
            round (∑ b, ∑ i, (y b i : ℝ) * g.slope b i)| := by
  obtain ⟨X₁, h₁⟩ := Contact.eventually_log_cutoff_margin hε
  obtain ⟨X₂, h₂⟩ := eventually_atTop.1 (eventually_grouped_frequency_cost (dimension ε) F)
  refine ⟨max X₁ (max X₂ (exp 1)), ?_⟩
  intro t c g hx y hy hbudget
  let s := ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊
  let phase := ∑ b, ∑ i, (y b i : ℝ) * g.slope b i
  let h := AbcTwoNinths.Basic.rationalHeight c.source
  let T := t.thirdLogRadical / log t.thirdLogRadical + 2 * log c.cutoff
  let N := ∑ b, ∑ i, |(y b i : ℝ)|
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hh : 0 < h := (show 0 < (exponent ε / 2) * exp (3 * exponent ε * t.thirdLogRadical) by
    positivity).trans_le c.axial_height_lower
  have hx₂ := (le_max_right X₁ _).trans hx
  have he₁ : exp 1 ≤ t.thirdLogRadical := (le_max_right X₂ _).trans hx₂
  have hxpos := (exp_pos 1).trans_le he₁
  have hlogx : 1 ≤ log t.thirdLogRadical := by simpa using log_le_log (exp_pos 1) he₁
  have ht : t.thirdLogRadical / log t.thirdLogRadical ≤ t.thirdLogRadical := div_le_self hxpos.le hlogx
  have hcut := (h₁ c ((le_max_left _ _).trans hx)).2
  have hp : 0 ≤ log (c.prime : ℝ) := log_nonneg (by exact_mod_cast c.prime_isPrime.one_le)
  have hcut' : log c.cutoff ≤ t.thirdLogRadical := hcut.trans <| le_trans
    (mul_le_of_le_one_left hp (by linarith)) c.log_upper
  have hT : T ≤ 3 * t.thirdLogRadical := by dsimp [T]; linarith
  have hN : N ≤ (s : ℝ) * dimension ε * F := by
    dsimp only [N]
    exact_mod_cast (show (∑ b, ∑ i, |y b i|) ≤ (s : ℤ) * dimension ε * F by
      simpa only [Nat.cast_sum, Nat.cast_mul, ← Int.abs_eq_natAbs] using
        (Int.ofNat_le.mpr hbudget))
  have hcost : T * N ≤ exp (sqrt t.thirdLogRadical) / 2 :=
    (mul_le_mul hT hN (by dsimp [N]; positivity) (by positivity)).trans
      (h₂ t.thirdLogRadical ((le_max_left _ _).trans hx₂))
  have hz : (-round phase, y) ≠ 0 := fun heq => hy (congrArg Prod.snd heq)
  have hlo := g.height_separation (-round phase) y hz
  have hup := g.character_height_le
    (Prod.fst : Fin s × Fin (dimension ε) → _) Prod.snd (-round phase)
    (fun j => y j.1 j.2)
  simp only [Fintype.prod_prod_type, Fintype.sum_prod_type, Int.cast_neg] at hup
  exact frequency_separation_of_height hh hcost (hlo.trans_le hup)

end AbcSubexp
