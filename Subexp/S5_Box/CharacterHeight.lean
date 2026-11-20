/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import AbcTwoNinths.Paper.S2_PolyCap.PlaneCoordinateHeight

/-!
# Height of the column translation

The finite valuations express the rational height in the exponent-coordinate
norm. Splitting off the roof coordinate gives the estimate used in Section 5.

## Main results
* `AbcSubexp.Box.ratHeightCoordinates`
* `AbcSubexp.Box.sourceValuationZero`
* `AbcSubexp.Box.oneGeneratorHeightBound`
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace AbcSubexp.Box

open Parameters Real

private theorem valuationParts (u : ℚ) {p : ℕ} (hp : p.Prime) :
    padicValRat p u = (u.num.natAbs.factorization p : ℤ) - (u.den.factorization p : ℤ) := by
  rw [padicValRat_def, ← Nat.factorization_def _ hp, padicValInt, ← Nat.factorization_def _ hp]

/-- The height of a nonzero rational is the coordinate norm on any prime support. -/
theorem ratHeightCoordinates (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (u : ℚ) (hu : u ≠ 0) (hs : ∀ p, p.Prime → p ∉ S → padicValRat p u = 0) :
    AbcTwoNinths.Basic.rationalHeight u =
      AbcTwoNinths.PolyCap.coordHeight (fun p : S => (padicValRat p u : ℝ) * log (p : ℝ)) := by
  classical
  have hn : u.num.natAbs ≠ 0 := by simpa using hu
  have hd : u.den ≠ 0 := u.den_pos.ne'
  have exclusive {p : ℕ} (hp : p.Prime) :
      u.num.natAbs.factorization p = 0 ∨ u.den.factorization p = 0 := by
    by_contra! h
    have ha : p ∈ u.num.natAbs.primeFactors := Finsupp.mem_support_iff.mpr h.1
    have hb : p ∈ u.den.primeFactors := Finsupp.mem_support_iff.mpr h.2
    have hg := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors ha) (Nat.dvd_of_mem_primeFactors hb)
    rw [u.reduced.gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  have hpos {p : ℕ} (hp : p.Prime) :
      max ((padicValRat p u : ℝ) * log (p : ℝ)) 0 =
        (u.num.natAbs.factorization p : ℝ) * log (p : ℝ) := by
    rw [valuationParts u hp, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_le)
    rcases exclusive hp with H | H
    · simp [H, neg_mul, max_eq_right (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) hlog))]
    · simp [H, max_eq_left (mul_nonneg (Nat.cast_nonneg _) hlog)]
  have hneg {p : ℕ} (hp : p.Prime) :
      max (-((padicValRat p u : ℝ) * log (p : ℝ))) 0 =
        (u.den.factorization p : ℝ) * log (p : ℝ) := by
    rw [valuationParts u hp, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_le)
    rcases exclusive hp with H | H
    · simp [H, max_eq_left (mul_nonneg (Nat.cast_nonneg _) hlog)]
    · simp [H, max_eq_right (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) hlog))]
  have hsub (n : ℕ) (Hn : n = u.num.natAbs ∨ n = u.den) :
      n.factorization.support ⊆ S := by
    intro p hp
    by_contra hnot
    have hprime := Nat.prime_of_mem_primeFactors (show p ∈ n.primeFactors from hp)
    have hz := hs p hprime hnot
    rw [valuationParts u hprime, sub_eq_zero] at hz
    have Hz : u.num.natAbs.factorization p = u.den.factorization p := by exact_mod_cast hz
    rcases exclusive hprime with HE | HE
    · rcases Hn with rfl | rfl
      · exact Finsupp.mem_support_iff.mp hp HE
      · exact Finsupp.mem_support_iff.mp hp (Hz ▸ HE)
    · rcases Hn with rfl | rfl
      · exact Finsupp.mem_support_iff.mp hp (Hz.symm ▸ HE)
      · exact Finsupp.mem_support_iff.mp hp HE
  have hsum (n : ℕ) (Hn : n = u.num.natAbs ∨ n = u.den) :
      (∑ p : S, (n.factorization p : ℝ) * log (p : ℝ)) = log (n : ℝ) := by
    rw [log_nat_eq_sum_factorization, Finsupp.sum]
    rw [Finset.sum_coe_sort S (fun p : ℕ => (n.factorization p : ℝ) * log (p : ℝ))]
    exact (Finset.sum_subset (hsub n Hn) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, Nat.cast_zero, zero_mul])).symm
  unfold AbcTwoNinths.Basic.rationalHeight AbcTwoNinths.PolyCap.coordHeight
  simp_rw [fun p : S => hpos (hS p p.property), fun p : S => hneg (hS p p.property)]
  rw [hsum _ (Or.inl rfl), hsum _ (Or.inr rfl)]
  rcases le_total u.num.natAbs u.den with h | h
  · rw [max_eq_right h, max_eq_right (log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast h))]
  · rw [max_eq_left h, max_eq_left (log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hd) (by exact_mod_cast h))]

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

/-- The axial source has zero valuation at every prime outside the triple's radical. -/
theorem sourceValuationZero {p : ℕ} (hp : p.Prime) (h : ¬p ∣ t.radical) :
    padicValRat p c.source = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : 0 < t.c := t.add ▸ Nat.add_pos_left t.apos _
  have hR (H : p ∣ t.a * t.b * t.c) : p ∣ t.radical :=
    Finset.dvd_prod_of_mem _ ((Nat.mem_primeFactors).mpr
      ⟨hp, H, by positivity [t.apos, t.bpos]⟩)
  have ha : ¬p ∣ t.a := fun H => h (hR (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left H _) _))
  have hb : ¬p ∣ t.b := fun H => h (hR (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right H _) _))
  have hcc : ¬p ∣ t.c := fun H => h (hR (dvd_mul_of_dvd_right H _))
  have hA : padicValRat p (t.a : ℚ) = 0 := by simp [padicValNat.eq_zero_of_not_dvd ha]
  have hB : padicValRat p (t.b : ℚ) = 0 := by simp [padicValNat.eq_zero_of_not_dvd hb]
  have hC : padicValRat p (t.c : ℚ) = 0 := by simp [padicValNat.eq_zero_of_not_dvd hcc]
  have ha0 : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
  have hb0 : (t.b : ℚ) ≠ 0 := by exact_mod_cast t.bpos.ne'
  have hc0 : (t.c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs : padicValRat p (AbcTwoNinths.Statement.selectedSource t) = 0 := by
    unfold AbcTwoNinths.Statement.selectedSource
    split
    · rw [padicValRat.div hc0 hb0, hC, hB, sub_zero]
    · rw [padicValRat.div hc0 ha0, hC, hA, sub_zero]
    · rw [padicValRat.div (neg_ne_zero.mpr ha0) hb0, padicValRat.neg, hA, hB, sub_zero]
  rw [← c.source_eq, padicValRat.pow] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast c.sourcePower_pos.ne')

/-- The one-generator subgroup has the axial height and a bounded transverse contribution. -/
theorem oneGeneratorHeightBound (q : HittingPrime g) (i : Fin (dimension ε))
    (a n : ℤ) (htransverse : t.thirdLogRadical / log t.thirdLogRadical ≤ log c.cutoff) :
    AbcTwoNinths.Basic.rationalHeight (c.source ^ a * (g.unit q.listIndex i) ^ n) ≤
      |(a : ℝ) + (n : ℝ) * g.slope q.listIndex i| * AbcTwoNinths.Basic.rationalHeight c.source +
        |(n : ℝ)| * (2 * log c.cutoff) := by
  classical
  let f := g.prime q.listIndex i
  let v := g.unit q.listIndex i
  let S := insert f (insert g.anchor t.radical.primeFactors)
  let ax (p : ℕ) := (padicValRat p c.source : ℝ) * log (p : ℝ)
  let slope := g.slope q.listIndex i
  let pr (p : ℕ) := ((padicValRat p v : ℝ) - slope * (padicValRat p c.source : ℝ)) *
    log (p : ℝ)
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    simp only [S, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact g.prime_isPrime _ _
    · exact g.anchor_prime
    · exact Nat.prime_of_mem_primeFactors hp
  have hsrc : ∀ p, p.Prime → p ∉ t.radical.primeFactors → padicValRat p c.source = 0 := by
    intro p hp hnot
    apply sourceValuationZero hp
    intro hd
    exact hnot (Nat.mem_primeFactors.mpr ⟨hp, hd, by
      unfold AbcTwoNinths.Basic.Triple.radical AbcTwoNinths.Basic.radical
      exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)⟩)
  have hsource : ∀ p, p.Prime → p ∉ S → padicValRat p c.source = 0 :=
    fun p hp hn => hsrc p hp (fun hm => hn (by simp [S, hm]))
  have hz := c.source_principal.1
  have hv := (g.unit_principal q.listIndex i).1
  have hchar := mul_ne_zero (zpow_ne_zero a hz) (zpow_ne_zero n hv)
  have hval {p : ℕ} (hp : p.Prime) :
      padicValRat p (c.source ^ a * v ^ n) =
        a * padicValRat p c.source + n * padicValRat p v := by
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.mul (zpow_ne_zero _ hz) (zpow_ne_zero _ hv),
      padicValRat.zpow, padicValRat.zpow]
  have hsupport : ∀ p, p.Prime → p ∉ S → padicValRat p (c.source ^ a * v ^ n) = 0 := by
    intro p hp hn
    have hz' := hsource p hp hn
    have hv' : padicValRat p v = 0 :=
      g.unit_support _ _ p hp (fun h => hn (by simp [S, h]))
        (fun h => hn (by simp [S, f, h])) hz'
    rw [hval hp, hz', hv']
    simp
  have hcomponents :
      (fun p : S => (padicValRat p (c.source ^ a * v ^ n) : ℝ) * log (p : ℝ)) =
        (fun p : S => ((a : ℝ) + (n : ℝ) * slope) * ax p) +
          (fun p : S => (n : ℝ) * pr p) := by
    funext p
    rw [hval (hS p p.property)]
    simp only [Int.cast_add, Int.cast_mul, Pi.add_apply, ax, pr]
    ring
  have hax : AbcTwoNinths.PolyCap.coordHeight (fun p : S => ax p) = AbcTwoNinths.Basic.rationalHeight c.source :=
    (ratHeightCoordinates S hS c.source hz hsource).symm
  have hfnot : f ∉ t.radical.primeFactors := fun hf =>
    g.prime_fresh _ _ (Nat.dvd_of_mem_primeFactors hf)
  have hanot : g.anchor ∉ t.radical.primeFactors := fun ha =>
    g.anchor_fresh (Nat.dvd_of_mem_primeFactors ha)
  have hfane : f ≠ g.anchor := g.prime_ne_anchor _ _
  have hprf : pr f = log (f : ℝ) := by
    simp [pr, v, f, g.unit_fresh, sourceValuationZero (g.prime_isPrime _ _) (g.prime_fresh _ _)]
  have hpra : pr g.anchor = -log (g.anchor : ℝ) := by
    simp [pr, v, g.unit_anchor, sourceValuationZero g.anchor_prime g.anchor_fresh]
  have hroof : pr g.roof = 0 := by
    have hr : (padicValRat g.roof c.source : ℝ) ≠ 0 := by exact_mod_cast g.roof_nonzero
    dsimp [pr, slope, GroupedTuple.slope, v]
    rw [div_mul_cancel₀ _ hr, sub_self, zero_mul]
  have hfpos : 0 < (f : ℝ) := by exact_mod_cast (g.prime_isPrime _ _).pos
  have hapos : 0 < (g.anchor : ℝ) := by exact_mod_cast g.anchor_prime.pos
  have hfupper : log (f : ℝ) ≤ log c.cutoff := log_le_log hfpos (g.primes_in_window _ _).2
  have haupper : log (g.anchor : ℝ) ≤ log c.cutoff := log_le_log hapos g.anchor_in_window.2
  have hpr :
      AbcTwoNinths.PolyCap.coordHeight (fun p : S => pr p) ≤ 2 * log c.cutoff := by
    have old :
        (∑ p ∈ t.radical.primeFactors, |pr p|) ≤ log c.cutoff := by
      have H := g.transverse_height q.listIndex i
      have H' : (∑ p ∈ t.radical.primeFactors.erase g.roof, |pr p|) < t.thirdLogRadical / log t.thirdLogRadical := by
        apply lt_of_eq_of_lt _ H
        apply Finset.sum_congr rfl
        intro p hp
        have hlog : 0 ≤ log (p : ℝ) := log_nonneg
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).one_le)
        simp only [pr, abs_mul, abs_of_nonneg hlog, slope, v, GroupedTuple.slope]
      calc
        (∑ p ∈ t.radical.primeFactors, |pr p|) = ∑ p ∈ t.radical.primeFactors.erase g.roof, |pr p| := by
          by_cases hmem : g.roof ∈ t.radical.primeFactors
          · simpa only [hroof, abs_zero, add_zero] using
              (Finset.sum_erase_add _ (fun p => |pr p|) hmem).symm
          · rw [Finset.erase_eq_of_notMem hmem]
        _ ≤ _ := H'.le.trans htransverse
    have fresh (F : ℝ → ℝ) (H : ∀ x, F x ≤ |x|) (hF :
        F (pr f) + F (pr g.anchor) ≤ log c.cutoff) :
        (∑ p : S, F (pr p)) ≤ 2 * log c.cutoff := by
      rw [Finset.sum_coe_sort S (fun p : ℕ => F (pr p))]
      have hfn : f ∉ insert g.anchor t.radical.primeFactors := by simp [hfane, hfnot]
      simp only [S, Finset.sum_insert hfn, Finset.sum_insert hanot]
      have hb : (∑ p ∈ t.radical.primeFactors, F (pr p)) ≤
          ∑ p ∈ t.radical.primeFactors, |pr p| := Finset.sum_le_sum (fun p _ => H (pr p))
      linarith
    have hf0 : 0 ≤ log (f : ℝ) := log_nonneg (by exact_mod_cast (g.prime_isPrime _ _).one_le)
    have ha0 : 0 ≤ log (g.anchor : ℝ) := log_nonneg (by exact_mod_cast g.anchor_prime.one_le)
    apply max_le
    · exact fresh (fun x => max x 0) (fun x => max_le (le_abs_self x) (abs_nonneg x))
        (by simpa [hprf, hpra, max_eq_left hf0, max_eq_right (neg_nonpos.mpr ha0)] using hfupper)
    · exact fresh (fun x => max (-x) 0) (fun x => max_le (neg_le_abs x) (abs_nonneg x))
        (by simpa [hprf, hpra, max_eq_left ha0, max_eq_right (neg_nonpos.mpr hf0)] using haupper)
  rw [ratHeightCoordinates S hS _ hchar hsupport, hcomponents]
  refine (AbcTwoNinths.PolyCap.coordHeightAdd _ _).trans ?_
  rw [AbcTwoNinths.PolyCap.coordHeightSmul, AbcTwoNinths.PolyCap.coordHeightSmul, hax]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hpr (abs_nonneg _)) _

end AbcSubexp.Box
