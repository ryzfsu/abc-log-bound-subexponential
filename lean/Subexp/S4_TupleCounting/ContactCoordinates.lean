/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S3_ContactPrime.SourceSupport
public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket
public import AbcTwoNinths.Paper.S4_ExteriorE2.Join
public import AbcTwoNinths.Paper.S4_ExteriorE2.Products
public import AbcTwoNinths.Paper.S5_Selection.RoofMass

/-!
# Coordinates of the primitive contact unit

The reduced numerator and denominator of the contact unit determine its old
prime coordinates and its primitive signed lift in Section 3.

## Main results

* `AbcSubexp.TupleCounting.existsContactAxis`
* `AbcSubexp.TupleCounting.contactAxisMass`
-/

@[expose] public section

open Real

namespace AbcSubexp.TupleCounting

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t)

/-- Primes in the reduced numerator or denominator of the contact unit. -/
abbrev ContactSupport := AbcTwoNinths.ExteriorE2.Support c.source.num.natAbs c.source.den

private theorem sourceNumNonzero : c.source.num.natAbs ≠ 0 := by
  rw [Int.natAbs_ne_zero]
  exact fun h => c.source_principal.1 (Rat.zero_of_num_zero h)

private theorem sourceValuationsZero :
    padicValInt c.prime c.source.num = 0 ∧ padicValNat c.prime c.source.den = 0 := by
  have h := c.source_principal.2.1
  rw [padicValRat_def] at h
  rcases c.source.num_or_den_zero_padicVal c.prime_isPrime with hn | hd
  · exact ⟨hn, by omega⟩
  · exact ⟨by omega, hd⟩

private theorem sourceDenAvoid : ¬ c.prime ∣ c.source.den := by
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  exact fun h => (dvd_iff_padicValNat_ne_zero c.source.den_nz).1 h (sourceValuationsZero c).2

/-- The contact prime is off the support of the primitive contact unit. -/
theorem contactSupportAvoid (i : ContactSupport c) : c.prime ≠ i.val := by
  intro he
  have hmem : c.prime ∈ c.source.num.natAbs.primeFactors ∪ c.source.den.primeFactors :=
    he.symm ▸ i.property
  exact ((ContactPrime.source_prime_support_iff c c.prime_isPrime).1 hmem) c.source_principal.2.1

private theorem sourceNumeratorResidue [Fact c.prime.Prime] :
    (c.source.num : ZMod c.prime) = c.source.den := by
  obtain ⟨_, hden⟩ := sourceValuationsZero c
  have hd : (c.source.den : ℚ) ≠ 0 := by exact_mod_cast c.source.den_nz
  have hdiff : c.source.num - (c.source.den : ℤ) ≠ 0 := by
    intro h
    apply c.source_ne_one
    rw [← c.source.num_div_den]
    exact (div_eq_one_iff_eq hd).2 (by exact_mod_cast sub_eq_zero.mp h)
  have hsub : c.source - 1 = ((c.source.num - (c.source.den : ℤ) : ℤ) : ℚ) / c.source.den := by
    conv_lhs => rw [← c.source.num_div_den]
    push_cast
    field_simp
  have hpos := c.source_principal.2.2.resolve_left c.source_ne_one
  rw [hsub, padicValRat.div (by exact_mod_cast hdiff) hd, padicValRat.of_int,
    padicValRat.of_nat, hden, Nat.cast_zero, sub_zero] at hpos
  have hdiv : (c.prime : ℤ) ∣ c.source.num - (c.source.den : ℤ) := by
    by_contra h
    rw [padicValInt.eq_zero_of_not_dvd h] at hpos
    omega
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
  push_cast at h
  exact sub_eq_zero.mp h

private theorem rationalPrincipalOfPadicPrincipal {p : ℕ} [Fact p.Prime] {u : ℚ}
    (hu : AbcTwoNinths.Basic.Principal p u) : AbcTwoNinths.Basic.RatPrincipalUnit p u := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [AbcTwoNinths.Basic.Principal] at hu
  have hnorm := Padic.norm_eq_of_norm_sub_lt_right (z1 := (u : ℚ_[p])) (z2 := 1)
    (by simpa [AbcTwoNinths.Basic.Principal] using hu)
  rw [norm_one] at hnorm
  have hpadu : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast hu0
  rw [Padic.norm_eq_zpow_neg_valuation hpadu, Padic.valuation_ratCast,
    ← zpow_zero (p : ℝ), zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne'] at hnorm
  refine ⟨hu0, by omega, ?_⟩
  by_cases h : u = 1
  · exact Or.inl h
  · apply Or.inr
    have hpad : ((u - 1 : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
    have hn : ‖((u - 1 : ℚ) : ℚ_[p])‖ < 1 := by simpa [AbcTwoNinths.Basic.Principal] using hu
    rw [Padic.norm_eq_zpow_neg_valuation hpad, Padic.valuation_ratCast,
      ← zpow_zero (p : ℝ), zpow_lt_zpow_iff_right₀ hp] at hn
    omega

/-- The exact reduced prime vector lifts to the source and is primitive in its
signed residue kernel. -/
theorem existsContactAxis [Fact c.prime.Prime] [Fact (2 < c.prime)] :
    let n := c.source.num.natAbs
    let d := c.source.den
    let r := AbcTwoNinths.ExteriorE2.residue (AbcTwoNinths.ExteriorE2.base n d) (AbcTwoNinths.ExteriorE2.prime n d) (contactSupportAvoid c)
    let γ := AbcTwoNinths.ExteriorE2.gammaStar r (AbcTwoNinths.ExteriorE2.monomial (AbcTwoNinths.ExteriorE2.base n d) (AbcTwoNinths.ExteriorE2.prime n d))
    ∃ s : AbcTwoNinths.ExteriorE2.Kernel r, s.val = AbcTwoNinths.ExteriorE2.vec n d ∧ (γ s : ℚ) = c.source ∧
      ∀ (k : ℕ) (w : AbcTwoNinths.ExteriorE2.Kernel r), w ^ k = s → k = 1 := by
  intro n d r γ
  let neg := decide (c.source.num < 0)
  have hsign : (c.source.num : ℤ) = if neg then -(n : ℤ) else n := by
    by_cases h : c.source.num < 0
    · simp [neg, h, n, abs_of_neg h]
    · simp [neg, h, n, abs_of_nonneg (le_of_not_gt h)]
  have hdZ : (d : ZMod c.prime) ≠ 0 :=
    fun h => sourceDenAvoid c ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hNumZ := sourceNumeratorResidue c
  change (c.source.num : ZMod c.prime) = (d : ZMod c.prime) at hNumZ
  have hres : (n : ZMod c.prime) = if neg then -(d : ZMod c.prime) else d := by
    cases hneg : neg <;> rw [hneg] at hsign
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      simpa [hsign] using hNumZ
    · simp only [↓reduceIte] at hsign ⊢
      have he : -(n : ZMod c.prime) = d := by simpa [hsign] using hNumZ
      exact neg_eq_iff_eq_neg.mp he
  have hsource : c.source = if neg then -((n : ℚ) / d) else (n : ℚ) / d := by
    rw [← c.source.num_div_den, hsign]
    cases neg <;> simp [d, neg_div]
  obtain ⟨s, hs, hγ⟩ := AbcTwoNinths.ExteriorE2.join r _ (AbcTwoNinths.ExteriorE2.vec n d) n d neg hdZ
    (AbcTwoNinths.ExteriorE2.resEval (sourceNumNonzero c) c.source.den_nz (contactSupportAvoid c)) hres
    (AbcTwoNinths.ExteriorE2.ratEval (sourceNumNonzero c) c.source.den_nz)
  have hsourceAxis : (γ s : ℚ) = c.source := hγ.trans hsource.symm
  refine ⟨s, hs, hsourceAxis, fun k w hw => ?_⟩
  apply c.source_primitive (γ w : ℚ) k
  · exact rationalPrincipalOfPadicPrincipal
      (AbcTwoNinths.Diamond.signedLiftPrincipal (AbcTwoNinths.ExteriorE2.base n d) (AbcTwoNinths.ExteriorE2.prime n d) (contactSupportAvoid c) w)
  · rw [← Units.val_pow_eq_pow_val, ← map_pow, hw, hsourceAxis]

/-- The total old coefficient mass is twice the height less the absolute
real logarithm of the source. -/
theorem contactAxisMass :
    (∑ i : ContactSupport c, |((AbcTwoNinths.ExteriorE2.vec c.source.num.natAbs c.source.den).toAdd i : ℝ)| *
      Real.log (i.val : ℝ)) =
        2 * AbcTwoNinths.Basic.rationalHeight c.source - |Real.log (|(c.source : ℝ)|)| := by
  have hMass := AbcTwoNinths.Selection.roofMass (sourceNumNonzero c) c.source.den_nz c.source.reduced
  simp only [AbcTwoNinths.ExteriorE2.base] at hMass
  rw [hMass]
  have hn : (0 : ℝ) < c.source.num.natAbs :=
    by exact_mod_cast Nat.pos_of_ne_zero (sourceNumNonzero c)
  have hd : (0 : ℝ) < c.source.den := by exact_mod_cast c.source.den_pos
  have habs : |(c.source : ℝ)| = (c.source.num.natAbs : ℝ) / c.source.den := by
    conv_lhs => rw [← c.source.num_div_den]
    push_cast
    rw [abs_div, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, abs_of_pos hd]
  have hheight :
      AbcTwoNinths.Basic.rationalHeight c.source = max (Real.log (c.source.num.natAbs : ℝ)) (Real.log (c.source.den : ℝ)) :=
    by
      unfold AbcTwoNinths.Basic.rationalHeight
      rw [Nat.cast_max]
      exact Real.strictMonoOn_log.monotoneOn.map_max hn hd
  rw [habs, hheight, Real.log_mul hn.ne' hd.ne', Real.log_div hn.ne' hd.ne']
  rcases le_total (Real.log (c.source.num.natAbs : ℝ)) (Real.log (c.source.den : ℝ)) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

end AbcSubexp.TupleCounting
