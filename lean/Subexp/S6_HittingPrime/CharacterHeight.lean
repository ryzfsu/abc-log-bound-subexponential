/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import AbcTwoNinths.Paper.S2_PolyCap.CoprimeMonomialParts

/-!
# Height of a character of an auxiliary tuple

The axial component of a valuation vector is measured by its roof slope.
The two fresh primes contribute at most twice the logarithm of the cutoff
to the transverse cost of each generator.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Real Parameters
open scoped BigOperators

private theorem rational_monomial_height (z : ℚ) (hz : z ≠ 0) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hn : z.num.natAbs.primeFactors ⊆ S)
    (hd : z.den.primeFactors ⊆ S) :
    AbcTwoNinths.Basic.rationalHeight z = AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.PolyCap.prodMonomial (fun p : S => (p : ℕ))
      (fun p => padicValRat p z)) := by
  classical
  have hprod (n : ℕ) (hn0 : n ≠ 0) (hsub : n.primeFactors ⊆ S) :
      (∏ p : S, (p.val : ℚ) ^ n.factorization p) = (n : ℚ) := by
    rw [Finset.prod_coe_sort S (fun p : ℕ => (p : ℚ) ^ n.factorization p)]
    exact_mod_cast (calc
      ∏ p ∈ S, p ^ n.factorization p = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        (Finset.prod_subset hsub fun p _ hp => by
          rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hp
            (Nat.mem_primeFactors.mpr ⟨hS p (by assumption), h, hn0⟩)), pow_zero]).symm
      _ = n := (Nat.prod_primeFactors_pow_factorization hn0).symm)
  have he (p : S) : padicValRat p z =
      (z.num.natAbs.factorization p : ℤ) - z.den.factorization p := by
    simp only [padicValRat, padicValInt, Nat.factorization_def _ (hS p p.property)]
  have hm : AbcTwoNinths.PolyCap.prodMonomial (fun p : S => (p : ℕ)) (fun p => padicValRat p z) = |z| := by
    unfold AbcTwoNinths.PolyCap.prodMonomial
    have hne (p : S) : (p.val : ℚ) ≠ 0 := by exact_mod_cast (hS p p.property).ne_zero
    simp only [he, zpow_sub₀ (hne _), zpow_natCast]
    rw [Finset.prod_div_distrib, hprod _ (by simpa using hz) hn,
      hprod _ z.den_nz hd]
    simpa only [Rat.num_abs_eq_abs_num, Rat.den_abs_eq_den, Int.abs_eq_natAbs, Int.cast_natCast]
      using Rat.num_div_den |z|
  rw [hm]
  simp only [AbcTwoNinths.Basic.rationalHeight, Rat.num_abs_eq_abs_num, Rat.den_abs_eq_den, Int.abs_eq_natAbs,
    Int.natAbs_natCast]

private theorem source_off_radical {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t) {p : ℕ}
    (hp : p.Prime) (hoff : p ∉ t.radical.primeFactors) : padicValRat p c.source = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : t.c ≠ 0 := by
    rw [← t.add]
    exact (Nat.add_pos_left t.apos _).ne'
  have hprod := mul_ne_zero (mul_ne_zero t.apos.ne' t.bpos.ne') hc
  have hnot : ¬ p ∣ t.a * t.b * t.c := by
    intro h
    exact hoff ((Nat.primeFactors_prod_primeFactors _).symm ▸
      Nat.mem_primeFactors.mpr ⟨hp, h, hprod⟩)
  have hval (n : ℕ) (hn : n ∣ t.a * t.b * t.c) : padicValRat p (n : ℚ) = 0 := by
    simp [padicValNat.eq_zero_of_not_dvd (fun h => hnot (h.trans hn))]
  have ha := hval t.a (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hb := hval t.b (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have hcv := hval t.c (dvd_mul_left _ _)
  have ha0 : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
  have hb0 : (t.b : ℚ) ≠ 0 := by exact_mod_cast t.bpos.ne'
  have hc0 : (t.c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hv : padicValRat p (AbcTwoNinths.Statement.selectedSource t) = 0 := by
    unfold AbcTwoNinths.Statement.selectedSource
    cases AbcTwoNinths.Statement.minRadicalSide t <;>
      simp [padicValRat.div, ha, hb, hcv, ha0, hb0, hc0]
  rw [← c.source_eq, padicValRat.pow] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by exact_mod_cast c.sourcePower_pos.ne')

private theorem valuation_prod {ι : Type*} {p : ℕ} [Fact p.Prime] (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      padicValRat.mul (hf i) (Finset.prod_ne_zero_iff.mpr fun j _ => hf j), ih]

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}

private theorem transverse_sum_le (g : GroupedTuple c) (b i) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, |(padicValRat p (g.unit b i) : ℝ) -
      g.slope b i * (padicValRat p c.source : ℝ)| * log p ≤
      t.thirdLogRadical / log t.thirdLogRadical + 2 * log c.cutoff := by
  classical
  let w (p : ℕ) := |(padicValRat p (g.unit b i) : ℝ) -
    g.slope b i * (padicValRat p c.source : ℝ)| * log p
  let old := t.radical.primeFactors.erase g.roof
  let E := insert g.anchor (insert (g.prime b i) old)
  have ha : g.anchor ∉ t.radical.primeFactors :=
    fun h => g.anchor_fresh (Nat.dvd_of_mem_primeFactors h)
  have hi : g.prime b i ∉ t.radical.primeFactors :=
    fun h => g.prime_fresh b i (Nat.dvd_of_mem_primeFactors h)
  have hao : g.anchor ∉ old := fun h => ha (Finset.mem_of_mem_erase h)
  have hio : g.prime b i ∉ old := fun h => hi (Finset.mem_of_mem_erase h)
  have hra : (padicValRat g.roof c.source : ℝ) ≠ 0 := by exact_mod_cast g.roof_nonzero
  have hzero (p : ℕ) (hp : p.Prime) (hn : p ∉ E) : w p = 0 := by
    by_cases hr : p = g.roof
    · subst p
      simp [w, GroupedTuple.slope, hra]
    · have hN : p ≠ g.anchor ∧ p ≠ g.prime b i ∧ p ∉ old := by
        simpa [E] using hn
      have hs := source_off_radical c hp (fun h => hN.2.2 (Finset.mem_erase.mpr ⟨hr, h⟩))
      simp [w, hs, g.unit_support b i p hp hN.1 hN.2.1 hs]
  have ha' : w g.anchor = log g.anchor := by
    simp [w, source_off_radical c g.anchor_prime ha, g.unit_anchor]
  have hi' : w (g.prime b i) = log (g.prime b i) := by
    simp [w, source_off_radical c (g.prime_isPrime b i) hi, g.unit_fresh]
  have hpos (p : ℕ) (hp : p ∈ E) : 0 ≤ w p := by
    have hprime : p.Prime := by
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact g.anchor_prime
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact g.prime_isPrime b i
      exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    exact mul_nonneg (abs_nonneg _) (log_nonneg (by exact_mod_cast hprime.one_le))
  have hsub : ∑ p ∈ S, w p ≤ ∑ p ∈ E, w p := calc
    _ = ∑ p ∈ S ∩ E, w p := (Finset.sum_subset Finset.inter_subset_left
      (fun p hp hn => hzero p (hS p hp) (fun h => hn (Finset.mem_inter.mpr ⟨hp, h⟩)))).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun p hp _ => hpos p hp)
  have hE : ∑ p ∈ E, w p = log g.anchor + (log (g.prime b i) + ∑ p ∈ old, w p) := by
    have hne := (g.prime_ne_anchor b i).symm
    simp only [E, Finset.sum_insert (show g.anchor ∉ insert (g.prime b i) old by
      simp [hne, hao]), Finset.sum_insert hio, ha', hi']
  have ho : ∑ p ∈ old, w p < t.thirdLogRadical / log t.thirdLogRadical := g.transverse_height b i
  have hal := log_le_log (by exact_mod_cast g.anchor_prime.pos) g.anchor_in_window.2
  have hil := log_le_log (by exact_mod_cast (g.prime_isPrime b i).pos) (g.primes_in_window b i).2
  change ∑ p ∈ S, w p ≤ _
  linarith

/-- The height of an integral character is bounded by its axial projection and
the sum of the transverse costs of its generators. -/
theorem GroupedTuple.character_height_le (g : GroupedTuple c) {ι : Type*} [Fintype ι]
    (b : ι → Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) (i : ι → Fin (dimension ε)) (a : ℤ) (y : ι → ℤ) :
    AbcTwoNinths.Basic.rationalHeight (c.source ^ a * ∏ j, g.unit (b j) (i j) ^ y j) ≤
      2 * AbcTwoNinths.Basic.rationalHeight c.source * |(a : ℝ) + ∑ j, (y j : ℝ) * g.slope (b j) (i j)| +
      (t.thirdLogRadical / log t.thirdLogRadical + 2 * log c.cutoff) * ∑ j, |(y j : ℝ)| := by
  classical
  let u (j : ι) := g.unit (b j) (i j)
  let z := c.source ^ a * ∏ j, u j ^ y j
  have hu (j : ι) : u j ≠ 0 := (g.unit_principal _ _).1
  have hz : z ≠ 0 := mul_ne_zero (zpow_ne_zero _ c.source_principal.1)
    (Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hu j))
  let S := (z.num.natAbs.primeFactors ∪ z.den.primeFactors) ∪
    (c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := by
    simp only [S, Finset.mem_union] at hp
    rcases hp with (hp | hp) | (hp | hp) <;> exact Nat.prime_of_mem_primeFactors hp
  let P (p : S) : ℕ := p.val
  have hP (p : S) : (P p).Prime := hS p p.property
  have hI : Function.Injective P := Subtype.val_injective
  let V (p : S) := (padicValRat (P p) c.source : ℝ)
  let E (p : S) := (padicValRat (P p) z : ℝ)
  let L (p : S) := log (P p)
  have hL (p : S) : 0 ≤ L p := log_nonneg (by exact_mod_cast (hP p).one_le)
  let r (j : ι) (p : S) := (padicValRat (P p) (u j) : ℝ) - g.slope (b j) (i j) * V p
  let A := (a : ℝ) + ∑ j, (y j : ℝ) * g.slope (b j) (i j)
  let T := t.thirdLogRadical / log t.thirdLogRadical + 2 * log c.cutoff
  have hchar : AbcTwoNinths.Basic.rationalHeight z ≤ ∑ p : S, |E p| * L p := by
    rw [rational_monomial_height z hz S hS
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (Finset.subset_union_right.trans Finset.subset_union_left)]
    exact (AbcTwoNinths.PolyCap.ratHeightProdMonomial P hP hI _).2
  have hax : ∑ p : S, |V p| * L p ≤ 2 * AbcTwoNinths.Basic.rationalHeight c.source := by
    rw [rational_monomial_height c.source c.source_principal.1 S hS
      (Finset.subset_union_left.trans Finset.subset_union_right)
      (Finset.subset_union_right.trans Finset.subset_union_right),
      (AbcTwoNinths.PolyCap.ratHeightProdMonomial P hP hI _).1]
    change _ ≤ 2 * max (∑ p : S, max (V p * L p) 0) (∑ p : S, max (-(V p * L p)) 0)
    have he (p : S) : |V p| * L p = max (V p * L p) 0 + max (-(V p * L p)) 0 := by
      have heq : |V p * L p| = |V p| * L p := by rw [abs_mul, abs_of_nonneg (hL p)]
      rw [← heq]
      rcases le_total 0 (V p * L p) with h | h
      · simp [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      · simp [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    simp_rw [he]
    rw [Finset.sum_add_distrib, two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have hres (j : ι) : ∑ p : S, |r j p| * L p ≤ T := by
    exact (Finset.sum_coe_sort S (fun p : ℕ => |(padicValRat p (u j) : ℝ) -
      g.slope (b j) (i j) * (padicValRat p c.source : ℝ)| * log p)).le.trans
        (transverse_sum_le g (b j) (i j) S hS)
  have heq (p : S) : E p = A * V p + ∑ j, (y j : ℝ) * r j p := by
    let : Fact (P p).Prime := ⟨hP p⟩
    have he : E p = (a : ℝ) * V p + ∑ j, (y j : ℝ) * (padicValRat (P p) (u j) : ℝ) := by
      dsimp only [E, V, z]
      rw [padicValRat.mul (zpow_ne_zero _ c.source_principal.1)
        (Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hu j)),
        valuation_prod _ _ (fun j => zpow_ne_zero (y j) (hu j))]
      simp [padicValRat.zpow]
    rw [he]
    simp only [A, r, add_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  have hcoord (p : S) : |E p| * L p ≤
      |A| * (|V p| * L p) + ∑ j, |(y j : ℝ)| * (|r j p| * L p) := by
    have h := (abs_add_le (A * V p) (∑ j, (y j : ℝ) * r j p)).trans
      (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    rw [heq]
    simpa only [add_mul, Finset.sum_mul, abs_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right h (hL p)
  calc
    AbcTwoNinths.Basic.rationalHeight z ≤ ∑ p : S, |E p| * L p := hchar
    _ ≤ ∑ p : S, (|A| * (|V p| * L p) + ∑ j, |(y j : ℝ)| * (|r j p| * L p)) :=
      Finset.sum_le_sum fun p _ => hcoord p
    _ = |A| * (∑ p : S, |V p| * L p) + ∑ j, |(y j : ℝ)| * (∑ p : S, |r j p| * L p) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset ι))]
    _ ≤ |A| * (2 * AbcTwoNinths.Basic.rationalHeight c.source) + ∑ j, |(y j : ℝ)| * T :=
      add_le_add (mul_le_mul_of_nonneg_left hax (abs_nonneg _))
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hres j) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The character on the list selected by a hitting prime satisfies the same height bound. -/
theorem HittingPrime.character_height_le {g : GroupedTuple c} (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    AbcTwoNinths.Basic.rationalHeight (q.character a y) ≤
      2 * AbcTwoNinths.Basic.rationalHeight c.source * |(a : ℝ) + ∑ i, (y i : ℝ) * g.slope q.listIndex i| +
      (t.thirdLogRadical / log t.thirdLogRadical + 2 * log c.cutoff) * ∑ i, |(y i : ℝ)| :=
  g.character_height_le (fun _ => q.listIndex) id a y

end AbcSubexp
