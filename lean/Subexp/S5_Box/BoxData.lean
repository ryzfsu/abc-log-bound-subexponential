/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Box.CharacterHeight
public import Subexp.S5_Box.CutoffBounds
public import Subexp.S5_Box.PhaseSimplex
public import Subexp.S5_Box.ShortTranslation

/-!
# Lattice column data

The generators in the selected list and their hitting prime give the phase-restricted box and the
shortest translation for the two sets of columns in Section 5.

## Main results
* `AbcSubexp.Box.existsBoxData`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.Box

open Parameters

/-- The data for the two column sets exist uniformly beyond a fixed threshold. -/
theorem existsBoxData (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c) (q : HittingPrime g),
      X ≤ t.thirdLogRadical → BoxData q := by
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hw : 0 < windowWidth ε := div_pos he (by positivity)
  have hm : 0 < dimension ε := Nat.ceil_pos.mpr (div_pos (by positivity) hw)
  obtain ⟨X, hX⟩ := eventualCutoffBounds ε hε
  refine ⟨X, ?_⟩
  intro t c g q ht
  obtain ⟨hheight, hcutoff, htransverse, hscale, hbudget⟩ := hX t c ht
  obtain ⟨hwidthLower, hwidthUpper⟩ := widthBounds (c := c) hε hheight
  refine ⟨hwidthLower, hwidthUpper, boxProjection q hcutoff hbudget, ?_⟩
  exact shortest_translation q hm hcutoff (zero_lt_one.trans_le hheight) hscale
    (fun i a n => oneGeneratorHeightBound q i a n htransverse)

end AbcSubexp.Box
