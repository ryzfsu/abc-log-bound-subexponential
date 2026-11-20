/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-!
# Prime support of the contact unit

The axial unit and auxiliary generators have the prime support used in
Sections 3 through 6.

## Main results
* `AbcSubexp.Contact.valuation_eq_zero_of_fresh`
* `AbcSubexp.GroupedTuple.valuation_eq_zero_outside_support`
-/

@[expose] public section

namespace AbcSubexp

open Parameters

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {p : ℕ}

/-- A prime outside the radical does not divide the triple product. -/
theorem not_dvd_abc_of_fresh (hp : p.Prime) (hf : ¬ p ∣ t.radical) :
    ¬ p ∣ t.a * t.b * t.c := by
  intro hd
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  apply hf
  exact Finset.dvd_prod_of_mem id <| Nat.mem_primeFactors.mpr
    ⟨hp, hd, (Nat.mul_pos (Nat.mul_pos t.apos t.bpos) hc).ne'⟩

/-- The primitive axial root has valuation zero outside the original radical. -/
theorem Contact.valuation_eq_zero_of_fresh (c : Contact ε t) (hp : p.Prime)
    (hf : ¬ p ∣ t.radical) : padicValRat p c.source = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := not_dvd_abc_of_fresh hp hf
  have ha : ¬ p ∣ t.a := fun v => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left v _) _)
  have hb : ¬ p ∣ t.b := fun v => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right v _) _)
  have hc : ¬ p ∣ t.c := fun v => h (dvd_mul_of_dvd_right v _)
  have hC : (t.c : ℚ) ≠ 0 := by exact_mod_cast (t.add ▸ Nat.add_pos_left t.apos t.b).ne'
  have hA : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
  have hB : (t.b : ℚ) ≠ 0 := by exact_mod_cast t.bpos.ne'
  have hsel : padicValRat p (AbcTwoNinths.Statement.selectedSource t) = 0 := by
    unfold AbcTwoNinths.Statement.selectedSource
    cases AbcTwoNinths.Statement.minRadicalSide t <;>
      simp [neg_div, padicValRat.div hC hA, padicValRat.div hC hB,
        padicValRat.div hA hB, padicValNat.eq_zero_of_not_dvd,
        ha, hb, hc]
  rw [← c.source_eq, padicValRat.pow] at hsel
  exact (mul_eq_zero.mp hsel).resolve_left (by exact_mod_cast c.sourcePower_pos.ne')

/-- An auxiliary generator vanishes at primes outside the radical, anchor, and its own prime. -/
theorem GroupedTuple.valuation_eq_zero_outside_support {c : Contact ε t} (g : GroupedTuple c)
    (b : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) (i : Fin (dimension ε)) (hp : p.Prime)
    (hf : ¬ p ∣ t.radical) (hanchor : p ≠ g.anchor) (hprime : p ≠ g.prime b i) :
    padicValRat p (g.unit b i) = 0 :=
  g.unit_support b i p hp hanchor hprime (c.valuation_eq_zero_of_fresh hp hf)

end AbcSubexp
