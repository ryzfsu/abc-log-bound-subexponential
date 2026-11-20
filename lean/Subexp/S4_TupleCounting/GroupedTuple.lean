/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ContactValuation
public import Subexp.S4_TupleCounting.NormalizedGenerators

/-!
# Grouping the auxiliary generators

The flat auxiliary tuple is partitioned into consecutive lists. Reindexing the
character over these lists preserves the height separation from Section 4.

## Main results
* `AbcSubexp.TupleCounting.groupedTupleOfFlat`
* `AbcSubexp.TupleCounting.groupedTupleOfRawFlat`
-/

@[expose] public section

open scoped BigOperators

namespace AbcSubexp.TupleCounting

open Parameters Real

/-- Construct the grouped auxiliary tuple from the flat family of normalized units. -/
noncomputable def groupedTupleOfFlat {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)
    (anchor roof : ℕ)
    (hanchorPrime : anchor.Prime) (hanchorFresh : ¬ anchor ∣ t.radical)
    (hanchorWindow : c.cutoff / 3 < anchor ∧ (anchor : ℝ) ≤ c.cutoff)
    (hroofPrime : roof.Prime) (hroofRadical : roof ∣ t.radical)
    (hroofNonzero : padicValRat roof c.source ≠ 0)
    (prime : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℕ)
    (hprime : ∀ j, (prime j).Prime) (hfresh : ∀ j, ¬ prime j ∣ t.radical)
    (havoid : ∀ j, prime j ≠ anchor) (hdistinct : Function.Injective prime)
    (hwindow : ∀ j, c.cutoff / 3 < prime j ∧ (prime j : ℝ) ≤ c.cutoff)
    (unit : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℚ)
    (hprincipal : ∀ j, AbcTwoNinths.Basic.RatPrincipalUnit c.prime (unit j))
    (hunitAnchor : ∀ j, padicValRat anchor (unit j) = -1)
    (hunitFresh : ∀ j, padicValRat (prime j) (unit j) = 1)
    (hsupport : ∀ j p, p.Prime → p ≠ anchor → p ≠ prime j →
      padicValRat p c.source = 0 → padicValRat p (unit j) = 0)
    (hnormalized : ∀ j,
      |(padicValRat roof (unit j) : ℝ) / (padicValRat roof c.source : ℝ)| ≤ 1 / 2)
    (htransverse : ∀ j,
      (∑ p ∈ t.radical.primeFactors.erase roof,
        |(padicValRat p (unit j) : ℝ) -
          ((padicValRat roof (unit j) : ℝ) / (padicValRat roof c.source : ℝ)) *
            (padicValRat p c.source : ℝ)| * log (p : ℝ)) < t.thirdLogRadical / log t.thirdLogRadical)
    (hseparation : ∀ (a : ℤ) (y : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℤ),
      (a, y) ≠ 0 → exp (sqrt t.thirdLogRadical) < AbcTwoNinths.Basic.rationalHeight (c.source ^ a * ∏ j, unit j ^ y j)) :
    GroupedTuple c := by
  let s := ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊
  let m := dimension ε
  let index : Fin s × Fin m ≃ Fin (m * s) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm s m))
  refine {
    anchor := anchor
    anchor_prime := hanchorPrime
    anchor_fresh := hanchorFresh
    anchor_in_window := hanchorWindow
    prime := fun b i => prime (index (b, i))
    prime_isPrime := fun b i => hprime (index (b, i))
    prime_fresh := fun b i => hfresh (index (b, i))
    prime_ne_anchor := fun b i => havoid (index (b, i))
    primes_distinct := hdistinct.comp index.injective
    primes_in_window := fun b i => hwindow (index (b, i))
    roof := roof
    roof_prime := hroofPrime
    roof_dvd_radical := hroofRadical
    roof_nonzero := hroofNonzero
    unit := fun b i => unit (index (b, i))
    unit_principal := fun b i => hprincipal (index (b, i))
    unit_anchor := fun b i => hunitAnchor (index (b, i))
    unit_fresh := fun b i => hunitFresh (index (b, i))
    unit_support := fun b i => hsupport (index (b, i))
    roof_normalized := fun b i => hnormalized (index (b, i))
    transverse_height := fun b i => htransverse (index (b, i))
    height_separation := ?_
  }
  intro a y hne
  let flat : Fin (m * s) → ℤ := fun j => y (index.symm j).1 (index.symm j).2
  have hflat : (a, flat) ≠ 0 := by
    intro hzero
    apply hne
    have ha : a = 0 := congrArg Prod.fst hzero
    have hy : flat = 0 := congrArg Prod.snd hzero
    refine Prod.ext ha ?_
    funext b i
    simpa [flat] using congrFun hy (index (b, i))
  have hproduct : (∏ j, unit j ^ flat j) = ∏ b, ∏ i, unit (index (b, i)) ^ y b i := by
    calc
      _ = ∏ p, unit (index p) ^ y p.1 p.2 :=
        Fintype.prod_equiv index.symm _ _ (fun j => by simp [flat])
      _ = _ := Fintype.prod_prod_type _
  rw [← hproduct]
  exact hseparation a flat hflat

/-- Normalize the flat family along the axial unit and construct its grouped tuple. -/
noncomputable def groupedTupleOfRawFlat {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)
    (anchor roof : ℕ)
    (hanchorPrime : anchor.Prime) (hanchorFresh : ¬ anchor ∣ t.radical)
    (hanchorWindow : c.cutoff / 3 < anchor ∧ (anchor : ℝ) ≤ c.cutoff)
    (hroofPrime : roof.Prime) (hroofRadical : roof ∣ t.radical)
    (hroofNonzero : padicValRat roof c.source ≠ 0)
    (prime : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℕ)
    (hprime : ∀ j, (prime j).Prime) (hfresh : ∀ j, ¬ prime j ∣ t.radical)
    (havoid : ∀ j, prime j ≠ anchor) (hdistinct : Function.Injective prime)
    (hwindow : ∀ j, c.cutoff / 3 < prime j ∧ (prime j : ℝ) ≤ c.cutoff)
    (unit : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℚ)
    (hprincipal : ∀ j, AbcTwoNinths.Basic.RatPrincipalUnit c.prime (unit j))
    (hunitAnchor : ∀ j, padicValRat anchor (unit j) = -1)
    (hunitFresh : ∀ j, padicValRat (prime j) (unit j) = 1)
    (hsupport : ∀ j p, p.Prime → p ≠ anchor → p ≠ prime j →
      padicValRat p c.source = 0 → padicValRat p (unit j) = 0)
    (htransverse : ∀ j,
      (∑ p ∈ t.radical.primeFactors.erase roof,
        |(padicValRat p (unit j) : ℝ) -
          ((padicValRat roof (unit j) : ℝ) / (padicValRat roof c.source : ℝ)) *
            (padicValRat p c.source : ℝ)| * log (p : ℝ)) < t.thirdLogRadical / log t.thirdLogRadical)
    (hseparation : ∀ (a : ℤ) (y : Fin (dimension ε * ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) → ℤ),
      (a, y) ≠ 0 → exp (sqrt t.thirdLogRadical) < AbcTwoNinths.Basic.rationalHeight (c.source ^ a * ∏ j, unit j ^ y j)) :
    GroupedTuple c := by
  letI : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  letI : Fact anchor.Prime := ⟨hanchorPrime⟩
  letI : Fact roof.Prime := ⟨hroofPrime⟩
  let normalized j := normalizedGenerator roof c.source (unit j)
  have haxis := c.source_principal.1
  refine groupedTupleOfFlat c anchor roof hanchorPrime hanchorFresh hanchorWindow
    hroofPrime hroofRadical hroofNonzero prime hprime hfresh havoid hdistinct hwindow normalized
    (fun j => normalizedGeneratorPrincipal roof c.source_principal (hprincipal j))
    ?_ ?_ ?_ (fun j => normalizedGeneratorRoof roof haxis (hprincipal j).1 hroofNonzero)
    ?_ (normalizedGeneratorHeightSeparation roof haxis unit hseparation)
  · intro j
    dsimp [normalized]
    rw [normalizedGeneratorValuation roof anchor haxis (hprincipal j).1,
      c.valuation_eq_zero_of_fresh hanchorPrime hanchorFresh, mul_zero, add_zero]
    exact hunitAnchor j
  · intro j
    let : Fact (prime j).Prime := ⟨hprime j⟩
    dsimp [normalized]
    rw [normalizedGeneratorValuation roof (prime j) haxis (hprincipal j).1,
      c.valuation_eq_zero_of_fresh (hprime j) (hfresh j), mul_zero, add_zero]
    exact hunitFresh j
  · intro j p hp hpAnchor hpFresh hzero
    let : Fact p.Prime := ⟨hp⟩
    dsimp [normalized]
    rw [normalizedGeneratorValuation roof p haxis (hprincipal j).1, hzero, mul_zero, add_zero]
    exact hsupport j p hp hpAnchor hpFresh hzero
  · intro j
    convert htransverse j using 1
    apply Finset.sum_congr rfl
    intro p hp
    let : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1⟩
    dsimp [normalized]
    rw [normalizedGeneratorTransverse roof p haxis (hprincipal j).1 hroofNonzero]

end AbcSubexp.TupleCounting
