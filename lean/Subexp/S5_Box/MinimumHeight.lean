/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.TripleAndHeight

/-!
# Minimum rational height

Every nonempty family of rational characters contains a member of minimum
logarithmic height, as used in the short translation in Section 5.

## Main results
* `AbcSubexp.Box.exists_min_ratHeight`
-/

@[expose] public section

namespace AbcSubexp.Box

/-- A nonempty predicate admits a witness of minimum rational-character height. -/
theorem exists_min_ratHeight {α : Type*} (P : α → Prop) (f : α → ℚ) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → AbcTwoNinths.Basic.rationalHeight (f a) ≤ AbcTwoNinths.Basic.rationalHeight (f b) := by
  classical
  let height (a : α) : ℕ := max (f a).num.natAbs (f a).den
  have hex : ∃ n, ∃ a, P a ∧ height a = n := by
    obtain ⟨a, ha⟩ := h
    exact ⟨height a, a, ha, rfl⟩
  obtain ⟨a, ha, hmin⟩ := Nat.find_spec hex
  refine ⟨a, ha, fun b hb => ?_⟩
  have hle : height a ≤ height b := by
    rw [hmin]
    exact Nat.find_min' hex ⟨b, hb, rfl⟩
  have hpos : 0 < height a := (f a).den_pos.trans_le (le_max_right _ _)
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

end AbcSubexp.Box
