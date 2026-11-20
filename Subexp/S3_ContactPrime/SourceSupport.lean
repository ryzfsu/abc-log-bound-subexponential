/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import AbcTwoNinths.Paper.S2_PolyCap.SideProjection

/-!
# Prime support of the contact source

The primitive axial source has the same numerator and denominator prime factors
as the selected ratio. Primes outside the radical have zero axial coordinate.

## Main results
* `AbcSubexp.ContactPrime.source_prime_support_iff`
* `AbcSubexp.ContactPrime.source_prime_support_eq_selected`
* `AbcSubexp.ContactPrime.source_prime_support_subset`
* `AbcSubexp.ContactPrime.source_valuation_eq_zero_of_not_dvd_radical`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime


/-- The old prime coordinates are exactly the nonzero valuations of the axial source. -/
theorem source_prime_support_iff {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}
    (c : Contact ε t) {q : ℕ} (hq : q.Prime) :
    q ∈ c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors ↔
      padicValRat q c.source ≠ 0 := by
  have : Fact q.Prime := ⟨hq⟩
  have hn : c.source.num.natAbs ≠ 0 := by
    have hn' : c.source.num ≠ 0 := by simpa using c.source_principal.1
    exact Int.natAbs_ne_zero.mpr hn'
  have hd : c.source.den ≠ 0 := c.source.den_ne_zero
  have sep (hnq : q ∣ c.source.num.natAbs) (hdq : q ∣ c.source.den) : False :=
    hq.not_dvd_one (c.source.reduced.gcd_eq_one ▸ Nat.dvd_gcd hnq hdq)
  change q ∈ c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors ↔
    (padicValNat q c.source.num.natAbs : ℤ) - (padicValNat q c.source.den : ℤ) ≠ 0
  rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
  constructor
  · rintro (⟨_, h, _⟩ | ⟨_, h, _⟩)
    · have hp := one_le_padicValNat_of_dvd hn h
      rw [padicValNat.eq_zero_of_not_dvd (sep h), Nat.cast_zero, sub_zero]
      exact_mod_cast (by omega : padicValNat q c.source.num.natAbs ≠ 0)
    · have hp := one_le_padicValNat_of_dvd hd h
      rw [padicValNat.eq_zero_of_not_dvd (fun hnq => sep hnq h), Nat.cast_zero, zero_sub, neg_ne_zero]
      exact_mod_cast (by omega : padicValNat q c.source.den ≠ 0)
  · intro h
    by_cases hnum : q ∣ c.source.num.natAbs
    · exact Or.inl ⟨hq, hnum, hn⟩
    by_cases hden : q ∣ c.source.den
    · exact Or.inr ⟨hq, hden, hd⟩
    exact (h (by simp [padicValNat.eq_zero_of_not_dvd hnum,
      padicValNat.eq_zero_of_not_dvd hden])).elim

/-- Extracting a positive power root preserves the prime factors on each side. -/
theorem source_prime_support_eq_selected {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}
    (c : Contact ε t) :
    c.source.num.natAbs.primeFactors = (AbcTwoNinths.Statement.selectedSource t).num.natAbs.primeFactors ∧
      c.source.den.primeFactors = (AbcTwoNinths.Statement.selectedSource t).den.primeFactors := by
  rw [← c.source_eq, Rat.num_pow, Rat.den_pow, Int.natAbs_pow,
    Nat.primeFactors_pow _ c.sourcePower_pos.ne',
    Nat.primeFactors_pow _ c.sourcePower_pos.ne']
  exact ⟨rfl, rfl⟩

/-- The selected ratio uses only prime factors of the original triple. -/
theorem source_prime_support_subset {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}
    (c : Contact ε t) (hord : t.a ≤ t.b) :
    c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors ⊆
      (t.a * t.b * t.c).primeFactors := by
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos t.b
  have hm : AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t) ≠ 0 := by
    cases AbcTwoNinths.Statement.minRadicalSide t
    · exact t.apos.ne'
    · exact t.bpos.ne'
    · exact hc.ne'
  have hp := Nat.mem_primeFactors.mpr ⟨c.prime_isPrime, c.prime_dvd_side, hm⟩
  let s := AbcTwoNinths.PolyCap.selectedSideData t hp
  obtain ⟨hcop, _, _, hdvd⟩ := AbcTwoNinths.PolyCap.selectedSideProjection t hp hord
  change s.n.Coprime s.d at hcop
  change s.n * s.d ∣ t.a * t.b * t.c at hdvd
  have hdpos : 0 < (s.d : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero s.hd
  have hcop' : (s.n : ℤ).natAbs.Coprime (s.d : ℤ).natAbs := by simpa using hcop
  have hnum : ((s.n : ℚ) / s.d).num = (s.n : ℤ) := by
    simpa using Rat.num_div_eq_of_coprime hdpos hcop'
  have hden : ((s.n : ℚ) / s.d).den = s.d := by
    have h := Rat.den_div_eq_of_coprime hdpos hcop'
    push_cast at h
    exact Int.ofNat.inj h
  have hsnum : (AbcTwoNinths.Statement.selectedSource t).num.natAbs = s.n := by
    rw [s.source]
    split <;> simp [hnum]
  have hsden : (AbcTwoNinths.Statement.selectedSource t).den = s.d := by
    rw [s.source]
    split <;> simp [hden]
  obtain ⟨hsrcnum, hsrcden⟩ := source_prime_support_eq_selected c
  rw [hsrcnum, hsrcden, hsnum, hsden, ← Nat.primeFactors_mul s.hn s.hd]
  exact Nat.primeFactors_mono hdvd (mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc.ne')

/-- A fresh prime contributes no exponent to the axial source. -/
theorem source_valuation_eq_zero_of_not_dvd_radical {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}
    (c : Contact ε t) (hord : t.a ≤ t.b) {q : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ t.radical) :
    padicValRat q c.source = 0 := by
  by_contra h
  have hmem := source_prime_support_subset c hord ((source_prime_support_iff c hq).2 h)
  exact hfresh (Finset.dvd_prod_of_mem id hmem)

end AbcSubexp.ContactPrime
