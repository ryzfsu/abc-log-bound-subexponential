/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.ContactCluster
public import Subexp.S4_TupleCounting.SelectedPrimeGenerators

/-!
# Selection of the grouped auxiliary tuple

For every positive exponent, one threshold works for every sufficiently large contact.
The selected common anchor and its flat tuple give the required disjoint lists after
normalization of the signed rational generators.

## Main results

* `AbcSubexp.exists_grouped_tuple`
-/

@[expose] public section

namespace AbcSubexp

open TupleCounting

/-- Every sufficiently large contact admits the grouped auxiliary tuple of Section 4. -/
theorem exists_grouped_tuple (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical → Nonempty (GroupedTuple c) := by
  obtain ⟨X, hX, hfamily⟩ := exists_contactTallFamily hε
  refine ⟨X, ?_⟩
  intro t c hx
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  let : Fact (2 < c.prime) := ⟨by have := c.prime_gt_five; omega⟩
  obtain ⟨a⟩ := existsContactRoof c hε (hX.trans_le hx)
  obtain ⟨P, lift, f, hsub, hpairs, htall⟩ := hfamily c a hx
  exact groupedTupleOfSelectedPrimeFamily c a P lift f hsub hpairs htall

end AbcSubexp
