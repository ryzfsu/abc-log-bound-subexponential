/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.GroupedTuple
public import Subexp.S4_TupleCounting.ContactAxisCharacter
public import Subexp.S4_TupleCounting.TallPrimeFamily
public import Subexp.S4_TupleCounting.TupleCharacterHeight
public import Subexp.S4_TupleCounting.TransverseValuations
public import Subexp.S3_ContactPrime.SourceSupport
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Rational generators of the selected prime family

Signed residue corrections for a family of fresh primes give principal rational units.
Their old valuations and their joint height determine the grouped auxiliary tuple.

## Main results
* `AbcSubexp.TupleCounting.groupedTupleOfSelectedPrimeFamily`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real Parameters

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)

private theorem contactPrimeDvdRadical : c.prime ∣ t.radical := by
  by_contra h
  apply not_dvd_abc_of_fresh c.prime_isPrime h
  have hd := c.prime_dvd_side
  cases hside : AbcTwoNinths.Statement.minRadicalSide t <;> rw [hside] at hd
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
  · exact dvd_mul_of_dvd_right hd _

private theorem selectedAlphabetInjective {O Q : Type*} {n : ℕ} {old : O → ℕ}
    (ho : Function.Injective old) (prime : Q ↪ ℕ) (f : Fin (n+1) ↪ Q)
    (hdisj : ∀ i j, old i ≠ prime (f j)) :
    Function.Injective (tuplePrimes old prime (anchoredTuple f)) := by
  rintro (i | (⟨⟩ | i)) (j | (⟨⟩ | j)) h
  · exact congrArg Sum.inl (ho h)
  · exact (hdisj i 0 h).elim
  · exact (hdisj i j.succ h).elim
  · exact (hdisj j 0 h.symm).elim
  · rfl
  · exact (Fin.succ_ne_zero j (f.injective (prime.injective h.symm))).elim
  · exact (hdisj j i.succ h.symm).elim
  · exact (Fin.succ_ne_zero i (f.injective (prime.injective h))).elim
  · exact congrArg (fun j => Sum.inr (Sum.inr j)) (Fin.succ_inj.mp (f.injective (prime.injective h)))

local notation "S" => c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors
local notation "N" => dimension ε * ⌊t.thirdLogRadical ^ (1/3:ℝ)⌋₊

private theorem groupedTupleOfOldCharacter [Fact c.prime.Prime] [Fact (2 < c.prime)]
    (roof : ℕ) (hr : roof ∈ S)
    (hp : ∀ i, (oldSupportPrime S roof i).Prime) (ha : ∀ i, c.prime ≠ oldSupportPrime S roof i)
    (hi : Function.Injective (oldSupportPrime S roof))
    (v : AbcTwoNinths.Diamond.LatticeSelectedPlaneData (oldSupportPrime S roof) hp ha)
    (hs : (AbcTwoNinths.Diamond.character (oldSupportPrime S roof) hp ha v : ℚ) = c.source)
    (hcoord : ∀ i, v.val.toAdd i = padicValRat (oldSupportPrime S roof i) c.source)
    (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (f : Fin (N+1) ↪ P)
    (hP : P ⊆ auxiliaryFreshPrimes t.radical c.cutoff)
    (hpairs : ∀ i ∈ P, ∀ j ∈ P,
      AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ))
        (AbcTwoNinths.ExteriorE2.project v.val.toAdd (lift i j)) < t.thirdLogRadical / log t.thirdLogRadical ∧
      (AbcTwoNinths.ExteriorE2.reduction (AbcTwoNinths.ExteriorE2.residue (oldSupportPrime S roof) hp ha)).toAdditive
        (lift i j) + AbcSubexp.Prerequisites.freshLabel c.prime i - AbcSubexp.Prerequisites.freshLabel c.prime j = 0)
    (htall : ∀ (n : ℤ) (y : Fin N → ℤ), (n ≠ 0 ∨ y ≠ 0) →
      exp (sqrt t.thirdLogRadical) < AbcTwoNinths.Diamond.height (tuplePrimes (oldSupportPrime S roof) Subtype.val (anchoredTuple f))
        (tupleCombination v.val.toAdd (fun i j : P => lift i.val j.val) (anchoredTuple f) n y)) :
    Nonempty (GroupedTuple c) := by
  classical
  let q := oldSupportPrime S roof
  let b := tuplePrimes q Subtype.val (anchoredTuple f)
  have hR : 0 < t.radical := Finset.prod_pos (fun _ h => (Nat.prime_of_mem_primeFactors h).pos)
  have hcut : 0 ≤ c.cutoff := mul_nonneg (exp_pos _).le ((sqrt_nonneg _).trans (le_max_left _ _))
  have fresh (j : Fin (N+1)) := (mem_auxiliaryFreshPrimes hR hcut).1 (hP (f j).property)
  have avoidR (j : Fin (N+1)) : ¬ (f j).val ∣ t.radical :=
    fun h => (fresh j).2.2.2 (dvd_mul_of_dvd_right h 2)
  have memS (i) : q i ∈ S := by
    rcases i with i | j
    · exact hr
    · exact (Finset.mem_erase.mp j.property).2
  have hST : S ⊆ t.radical.primeFactors := by
    intro p h
    have hp' : p.Prime := (Finset.mem_union.mp h).elim Nat.prime_of_mem_primeFactors
      Nat.prime_of_mem_primeFactors
    refine Nat.mem_primeFactors.mpr ⟨hp', ?_, hR.ne'⟩
    by_contra hf
    exact ((ContactPrime.source_prime_support_iff c hp').mp h) (c.valuation_eq_zero_of_fresh hp' hf)
  have hb (i) : (b i).Prime := by
    rcases i with i | (⟨⟩ | j)
    · exact hp i
    · exact (fresh 0).1
    · exact (fresh j.succ).1
  have havoid (i) : c.prime ≠ b i := by
    rcases i with i | (⟨⟩ | j)
    · exact ha i
    · intro he
      change c.prime = (f 0).val at he
      exact avoidR 0 (he ▸ contactPrimeDvdRadical c)
    · intro he
      change c.prime = (f j.succ).val at he
      exact avoidR j.succ (he ▸ contactPrimeDvdRadical c)
  have hinj : Function.Injective b := by
    apply selectedAlphabetInjective hi ⟨Subtype.val, Subtype.val_injective⟩ f
    intro i j he
    change q i = (f j).val at he
    exact avoidR j (he ▸ Nat.dvd_of_mem_primeFactors (hST (memS i)))
  let correction (j : Fin N) := lift (f j.succ).val (f 0).val
  have hlift (j : Fin N) := (hpairs _ (f j.succ).property _ (f 0).property).2
  let u (j : Fin N) : ℚ := AbcTwoNinths.Diamond.character b hb havoid
    (rawPrimeGenerator b hb havoid (correction j) (.inr j) (.inl ()) (hlift j))
  have spec (j : Fin N) := rawPrimeGenerator_spec b hb havoid hinj
    (correction j) (.inr j) (.inl ()) (by simp) (hlift j)
  have supp (j : Fin N) (p : ℕ) (hprime : p.Prime)
      (hneA : p ≠ (f 0).val) (hneJ : p ≠ (f j.succ).val) (hz : padicValRat p c.source = 0) :
      padicValRat p (u j) = 0 := by
    apply (spec j).2.2.2.2.2 p hprime _ hneJ hneA
    exact fun i he => ((ContactPrime.source_prime_support_iff c hprime).mp (he ▸ memS i)) hz
  refine ⟨groupedTupleOfRawFlat c (f 0).val roof (fresh 0).1 (avoidR 0)
    ⟨(fresh 0).2.1, (fresh 0).2.2.1⟩ (hp (.inl ())) (Nat.dvd_of_mem_primeFactors (hST hr))
    ((ContactPrime.source_prime_support_iff c (hp (.inl ()))).mp hr)
    (fun j => (f j.succ).val) (fun j => (fresh j.succ).1) (fun j => avoidR j.succ)
    (fun j he => Fin.succ_ne_zero j (f.injective (Subtype.ext he)))
    (fun i j he => Fin.succ_inj.mp (f.injective (Subtype.ext he)))
    (fun j => ⟨(fresh j.succ).2.1, (fresh j.succ).2.2.1⟩)
    u (fun j => (spec j).2.1) (fun j => (spec j).2.2.2.1) (fun j => (spec j).2.2.1)
    supp ?_ ?_⟩
  · intro j
    rw [transverseValuations_eq_projectedCost S t.radical.primeFactors roof c.source (u j)
      v.val.toAdd (correction j) hST (hcoord (.inl ())) ((spec j).2.2.2.2.1 (.inl ())).symm
      (fun i => hcoord (.inr i)) (fun i => ((spec j).2.2.2.2.1 (.inr i)).symm) (by
        intro p hpr hout
        have hprime := Nat.prime_of_mem_primeFactors hpr
        have hz := not_ne_iff.mp (fun hn => hout ((ContactPrime.source_prime_support_iff c hprime).mpr hn))
        refine ⟨hz, supp j p hprime ?_ ?_ hz⟩
        · exact fun he => avoidR 0 (he ▸ Nat.dvd_of_mem_primeFactors hpr)
        · exact fun he => avoidR j.succ (he ▸ Nat.dvd_of_mem_primeFactors hpr))]
    exact (hpairs _ (f j.succ).property _ (f 0).property).1
  · intro n y hne
    have hheight := ratHeight_tupleCharacter c q Subtype.val (anchoredTuple f) hb havoid hinj
      v hs (fun i j : P => lift i.val j.val) hlift n y
    have hny : n ≠ 0 ∨ y ≠ 0 := by
      by_contra! hz
      exact hne (Prod.ext hz.1 hz.2)
    exact (htall n y hny).trans_eq hheight.symm

/-- The flat family selected for the contact roof yields the grouped tuple of
principal rational generators with the same joint height separation. -/
theorem groupedTupleOfSelectedPrimeFamily [Fact c.prime.Prime] [Fact (2 < c.prime)]
    (a : ContactRoof c) (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S a.roof.val))
    (f : Fin (N+1) ↪ P) (hP : P ⊆ auxiliaryFreshPrimes t.radical c.cutoff)
    (hpairs : ∀ i ∈ P, ∀ j ∈ P,
      AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ))
        (AbcTwoNinths.ExteriorE2.project a.tallAxis.val (lift i j)) < t.thirdLogRadical / log t.thirdLogRadical ∧
      (AbcTwoNinths.ExteriorE2.reduction a.tallResidue).toAdditive (lift i j) +
        AbcSubexp.Prerequisites.freshLabel c.prime i - AbcSubexp.Prerequisites.freshLabel c.prime j = 0)
    (htall : ∀ (n : ℤ) (y : Fin N → ℤ), (n ≠ 0 ∨ y ≠ 0) →
      exp (sqrt t.thirdLogRadical) < AbcTwoNinths.Diamond.height (tuplePrimes (oldSupportPrime S a.roof.val) Subtype.val (anchoredTuple f))
        (tupleCombination a.tallAxis.val (fun i j : P => lift i.val j.val) (anchoredTuple f) n y)) :
    Nonempty (GroupedTuple c) := by
  let q := oldSupportPrime S a.roof.val
  have hindex (i) : (a.tallIndex i).val = q i := a.tallIndexPrime i
  have hp (i) : (q i).Prime := (hindex i) ▸ AbcTwoNinths.ExteriorE2.prime _ _ (a.tallIndex i)
  have ha (i) : c.prime ≠ q i := (hindex i) ▸ contactSupportAvoid c (a.tallIndex i)
  have hi : Function.Injective q := fun i j h =>
    a.tallIndex.injective (Subtype.ext ((hindex i).trans (h.trans (hindex j).symm)))
  let v := a.tallSignedAxis hp ha
  have hv : v.val.toAdd = a.tallAxis.val := funext (a.tallSignedAxis_apply hp ha)
  apply groupedTupleOfOldCharacter c a.roof.val a.roof.property hp ha hi v
    (a.tallSignedAxis_character hp ha) (fun i => (congrFun hv i).trans (a.tallAxisCoordinate i))
    P lift f hP
  · simpa only [hv, a.tallResidue_eq hp ha] using hpairs
  · simpa only [hv] using htall

end AbcSubexp.TupleCounting
