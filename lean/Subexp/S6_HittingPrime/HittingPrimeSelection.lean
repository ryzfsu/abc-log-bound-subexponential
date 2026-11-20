/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ThirdWindow
public import Subexp.S6_HittingPrime.ContactWindowScale
public import Subexp.S6_HittingPrime.MissedListTail

/-!
# Selection from the exceptional set for the actual slopes

An upper bound for the number of exceptional times supplies a single
prime and a single row whose coordinates are simultaneously in their arcs.

## Main results
* `AbcSubexp.hittingPrime_of_missed_rows_bound`
-/

@[expose] public section

open Real Filter
open AbcSubexp.Parameters

namespace AbcSubexp

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}

/-- Every slope of the chosen row lies in its prescribed arc at time `q`. -/
def GroupedTuple.hitsRow (g : GroupedTuple c) (q : ℕ)
    (b : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) : Prop :=
  ∀ i, circleDistance ((q : ℝ) * g.slope b i - (i.val : ℝ) / dimension ε) < phaseTolerance ε

/-- A majorant for the count of missed rows gives a hitting prime on the
uniform large-radical tail. The endpoint may be used for every phase. -/
theorem hittingPrime_of_missed_rows_bound (ε : ℝ) (hε : 0 < ε)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) :
    ∃ x₀ : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t) (g : GroupedTuple c),
      x₀ ≤ t.thirdLogRadical → c.degree + c.hittingWindowEnd ≤ c.radius →
      ∀ E : Finset ℕ,
        (∀ q ∈ thirdWindowPrimes c.hittingWindowEnd, (∀ b, ¬g.hitsRow q b) → q ∈ E) →
        (E.card : ℝ) ≤ (c.hittingWindowEnd : ℝ) * a ^ ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ +
          (3 : ℝ) ^ ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ * (2 * AbcTwoNinths.Basic.rationalHeight c.source) / exp (sqrt t.thirdLogRadical) →
        Nonempty (HittingPrime g) := by
  let A := ((depthParameter ε : ℝ) + 1) / (2 * exponent ε)
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_thirdWindow_card
  obtain ⟨u, hu⟩ := Contact.eventually_hittingWindowEnd_ge hε
    (max N (3 * (depthParameter ε + 2)))
  obtain ⟨v, hv⟩ := eventually_atTop.mp (eventually_missedListBound_lt_primeBudget
    ha ha' (by norm_num : 0 < (3 : ℝ)) (by positivity : 0 < 2 * A) (by norm_num : 0 < (2 : ℝ)))
  refine ⟨max (log 13) (max u v), ?_⟩
  intro t c g hx hrad E hcover hmiss
  obtain ⟨hx₁, hx'⟩ := max_le_iff.mp hx
  obtain ⟨hx₂, hx₃⟩ := max_le_iff.mp hx'
  obtain ⟨hN', hsize⟩ := max_le_iff.mp (hu t c hx₂)
  have hX : 1 < (c.hittingWindowEnd : ℝ) := by
    exact_mod_cast (show 1 < c.hittingWindowEnd by omega)
  obtain ⟨hh, hlog⟩ := c.hittingWindow_scale hε hx₁
  have hhp : 0 ≤ AbcTwoNinths.Basic.rationalHeight c.source :=
    (show 0 ≤ (exponent ε / 2) * exp (3 * exponent ε * t.thirdLogRadical) by positivity).trans
      c.axial_height_lower
  have hbudget := hv t.thirdLogRadical hx₃ c.hittingWindowEnd (2 * AbcTwoNinths.Basic.rationalHeight c.source) hX (by positivity)
    (by change AbcTwoNinths.Basic.rationalHeight c.source ≤ A * c.hittingWindowEnd * t.thirdLogRadical at hh
        linarith) hlog
  have hcard : E.card < (thirdWindowPrimes c.hittingWindowEnd).card := by
    exact_mod_cast (lt_of_le_of_lt hmiss (hbudget.trans (hN c.hittingWindowEnd hN')))
  obtain ⟨q, b, hq, hthird, hend, hhit⟩ :=
    exists_thirdWindow_prime_and_block E g.hitsRow hcard hcover
  obtain ⟨hD, hk, hsq⟩ := c.hittingWindow_degree_bounds hsize hthird
  exact ⟨⟨b, q, hq, hD, (Nat.add_le_add_left hend _).trans hrad, hk, hsq, hhit⟩⟩

end AbcSubexp
