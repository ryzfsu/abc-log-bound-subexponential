/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.RationalDepthReduction
public import AbcTwoNinths.Paper.S1_Statement.LogarithmicHeight
public import Subexp.Prerequisites.MinorComparison
public import AbcTwoNinths.Paper.S7_Terminal.SelectedAxialGrowth

/-!
# The primitive contact unit

The height bounds the exponents of rational principal roots of the contact source.
A largest exponent gives a primitive root, and the contact mass ensures that the
odd-prime lift preserves the original depth.

## Main results
* `AbcSubexp.ContactPrime.primitive_heavy_contact`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime


private theorem principal_ne_neg_one {p : ℕ} [Fact p.Prime] (hp : 2 < p) {u : ℚ}
    (hu : AbcTwoNinths.Basic.RatPrincipalUnit p u) : u ≠ -1 := by
  rintro rfl
  rcases hu.2.2 with h | h
  · norm_num at h
  · have hnot : ¬ p ∣ 2 := fun hd => hp.not_ge (Nat.le_of_dvd (by decide) hd)
    rw [show (-1 : ℚ) - 1 = -(2 : ℚ) by norm_num, padicValRat.neg,
      show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hnot, Nat.cast_zero] at h
    exact (lt_irrefl (0 : ℤ)) h

private theorem exists_primitive_power (t : AbcTwoNinths.Basic.Triple) {p : ℕ}
    [Fact p.Prime] (hp : 2 < p) (hz : AbcTwoNinths.Basic.RatPrincipalUnit p (AbcTwoNinths.Statement.selectedSource t))
    (hz_ne : AbcTwoNinths.Statement.selectedSource t ≠ 1) :
    ∃ (u : ℚ) (g : ℕ), AbcTwoNinths.Basic.RatPrincipalUnit p u ∧ 0 < g ∧
      AbcTwoNinths.Statement.selectedSource t = u ^ g ∧
      ∀ (v : ℚ) (m : ℕ), AbcTwoNinths.Basic.RatPrincipalUnit p v → v ^ m = u → m = 1 := by
  classical
  let P (m : ℕ) := 0 < m ∧ ∃ v : ℚ, AbcTwoNinths.Basic.RatPrincipalUnit p v ∧ AbcTwoNinths.Statement.selectedSource t = v ^ m
  let N := ⌊t.logHeight / Real.log 2⌋₊
  have bounded {m : ℕ} (hm : P m) : m ≤ N := by
    obtain ⟨_, v, hv, hpow⟩ := hm
    have hv_ne : v ≠ 1 := fun he => hz_ne (by simp [hpow, he])
    exact Nat.le_floor (AbcTwoNinths.Statement.exponentLeHeight hv.1 hv_ne
      (principal_ne_neg_one hp hv) hpow)
  have h1 : P 1 := ⟨Nat.one_pos, AbcTwoNinths.Statement.selectedSource t, hz, by simp⟩
  let g := Nat.findGreatest P N
  obtain ⟨hg, u, hu, hpow⟩ : P g := Nat.findGreatest_spec (bounded h1) h1
  refine ⟨u, g, hu, hg, hpow, ?_⟩
  intro v m hv hvm
  have hm : 0 < m := by
    by_contra! hzero
    obtain rfl : m = 0 := by omega
    exact hz_ne (by simp [hpow, ← hvm])
  have hmg : P (m * g) := ⟨Nat.mul_pos hm hg, v, hv, by rw [hpow, ← hvm, pow_mul]⟩
  have hle : m * g ≤ g := Nat.le_findGreatest (bounded hmg) hmg
  have hle' : m ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hle) hg
  omega

private theorem selected_real_log (t : AbcTwoNinths.Basic.Triple) (ho : t.a ≤ t.b) :
    |Real.log (AbcTwoNinths.Statement.selectedSource t : ℝ)| ≤ Real.log ((t.c : ℝ) / (t.a : ℝ)) := by
  have ha : 0 < (t.a : ℝ) := by exact_mod_cast t.apos
  have hb : 0 < (t.b : ℝ) := by exact_mod_cast t.bpos
  have hab : (t.a : ℝ) ≤ t.b := by exact_mod_cast ho
  have hsum : (t.a : ℝ) + t.b = t.c := by exact_mod_cast t.add
  have hc : 0 < (t.c : ℝ) := by linarith
  have hac : (t.a : ℝ) ≤ t.c := by linarith
  have hbc : (t.b : ℝ) ≤ t.c := by linarith
  have hloga := Real.log_le_log ha hab
  have hlogb := Real.log_le_log hb hbc
  have hlogc := Real.log_le_log ha hac
  rw [Real.log_div hc.ne' ha.ne']
  cases h : AbcTwoNinths.Statement.minRadicalSide t <;> simp only [AbcTwoNinths.Statement.selectedSource, h, Rat.cast_div,
    Rat.cast_neg, Rat.cast_natCast, neg_div]
  all_goals try rw [Real.log_neg_eq_log]
  all_goals
    rw [Real.log_div (by positivity) (by positivity)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Extract a primitive rational principal unit and preserve the full odd-prime depth. -/
theorem primitive_heavy_contact (t : AbcTwoNinths.Basic.Triple) {p : ℕ}
    [Fact p.Prime] [Fact (2 < p)]
    (hp : p ∈ (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)).primeFactors)
    {e : ℝ} (he : 0 < e) (ho : t.a ≤ t.b) (hreal : AbcTwoNinths.Statement.RealContactBound (e / 100) t)
    (hH : Real.exp (3 * e * t.thirdLogRadical) ≤ t.logHeight)
    (hheight : 2 * Real.log 2 ≤ t.logHeight)
    (herror : Real.log 2 + Real.log (t.logHeight / Real.log 2) ≤ e * t.logHeight)
    (hprime_size : 1 / e < (p : ℝ))
    (hmass : 2 * e * t.logHeight < (padicValNat p (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)) : ℝ) *
      Real.log (p : ℝ)) :
    ∃ (u : ℚ) (g : ℕ), AbcTwoNinths.Basic.RatPrincipalUnit p u ∧ u ≠ 1 ∧
      0 < g ∧ (g : ℝ) < 1 / e ∧ AbcTwoNinths.Statement.selectedSource t = u ^ g ∧
      (∀ (v : ℚ) (m : ℕ), AbcTwoNinths.Basic.RatPrincipalUnit p v → v ^ m = u → m = 1) ∧
      let h := AbcTwoNinths.Basic.rationalHeight u
      let n := padicValNat p (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t))
      padicValRat p (u - 1) = (n : ℤ) ∧
      (e / 2) * Real.exp (3 * e * t.thirdLogRadical) ≤ h ∧ h ≤ t.logHeight ∧
      2 * e * h < (n : ℝ) * Real.log (p : ℝ) ∧
      (n : ℝ) * Real.log (p : ℝ) ≤ h + Real.log 2 ∧
      |Real.log (u : ℝ)| ≤ (2 * e / 100) * h := by
  have p_prime : p.Prime := Fact.out
  have p_gt_two : 2 < p := Fact.out
  have source_ne : AbcTwoNinths.Statement.selectedSource t ≠ 1 := AbcSubexp.Prerequisites.selected_shift_nontrivial t hp
  have sourceDepth := AbcTwoNinths.Selection.selectedSourceDepthOfMem t hp
  have hprincipal : AbcTwoNinths.Basic.RatPrincipalUnit p (AbcTwoNinths.Statement.selectedSource t) := by
    refine ⟨?_, sourceDepth.1, Or.inr ?_⟩
    · have ha : (t.a : ℚ) ≠ 0 := by exact_mod_cast t.apos.ne'
      have hb : (t.b : ℚ) ≠ 0 := by exact_mod_cast t.bpos.ne'
      have hc : (t.c : ℚ) ≠ 0 := by
        exact_mod_cast (t.add ▸ Nat.add_pos_left t.apos t.b : 0 < t.c).ne'
      unfold AbcTwoNinths.Statement.selectedSource
      cases AbcTwoNinths.Statement.minRadicalSide t
      · exact div_ne_zero hc hb
      · exact div_ne_zero hc ha
      · exact div_ne_zero (neg_ne_zero.mpr ha) hb
    · rw [sourceDepth.2]
      have hmem := Nat.mem_primeFactors.mp hp
      exact_mod_cast one_le_padicValNat_of_dvd hmem.2.2 hmem.2.1
  obtain ⟨u, g, hu, hg, hu_pow, hprim⟩ :=
    exists_primitive_power t p_gt_two hprincipal source_ne
  have hu_ne : u ≠ 1 := fun he => source_ne (by simp [hu_pow, he])
  have one_principal : AbcTwoNinths.Basic.RatPrincipalUnit p (1 : ℚ) :=
    ⟨one_ne_zero, by simp, Or.inl rfl⟩
  have hlte := AbcTwoNinths.Basic.ltePair
    (p_prime.odd_of_ne_two (by omega)) hg hu one_principal
    (show u ^ g ≠ (1 : ℚ) ^ g by simpa [← hu_pow] using source_ne)
  rw [one_pow, ← hu_pow, sourceDepth.2] at hlte
  let h := AbcTwoNinths.Basic.rationalHeight u
  let n := padicValNat p (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t))
  have hg_pos : 0 < (g : ℝ) := by exact_mod_cast hg
  have hH_pos : 0 < t.logHeight := (Real.exp_pos _).trans_le hH
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p_prime.pos
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hindex := AbcTwoNinths.Statement.exponentLeHeight hu.1 hu_ne (principal_ne_neg_one p_gt_two hu) hu_pow
  have hh_scaled : (g : ℝ) * h = AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.Statement.selectedSource t) := by
    rw [hu_pow]
    change (g : ℝ) * Real.log (AbcTwoNinths.Statement.mulHeight u : ℝ) =
      Real.log (AbcTwoNinths.Statement.mulHeight (u ^ g) : ℝ)
    rw [AbcTwoNinths.Statement.mulHeightPow, Nat.cast_pow, Real.log_pow]
  have hsource_hi : AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.Statement.selectedSource t) ≤ t.logHeight := by
    apply Real.log_le_log
    · exact_mod_cast (AbcTwoNinths.Statement.selectedSource t).den_pos.trans_le (le_max_right _ _)
    · exact_mod_cast AbcTwoNinths.Statement.mulHeightSelectedSourceLe t
  have hsource_lo : t.logHeight - Real.log 2 ≤ AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.Statement.selectedSource t) :=
    AbcTwoNinths.Terminal.selectedHeightLower t
  have hroot := AbcTwoNinths.Basic.rationalDifferenceBound (c := 1) (d := 1)
    hu one_principal (by simpa using hu_ne)
  have h_one : AbcTwoNinths.Basic.padicRationalHeight (1 : ℚ) = 0 := by
    norm_num [AbcTwoNinths.Basic.padicRationalHeight]
  simp only [pow_one, Nat.cast_one, one_mul, h_one, add_zero] at hroot
  change (padicValRat p (u - 1) : ℝ) * Real.log (p : ℝ) ≤ Real.log 2 + h at hroot
  have hloss : (padicValNat p g : ℝ) * Real.log (p : ℝ) ≤ Real.log (t.logHeight / Real.log 2) := by
    have hpow_le : (p : ℝ) ^ padicValNat p g ≤ (g : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hg (pow_padicValNat_dvd (p := p) (n := g))
    have hl := (Real.log_le_log (pow_pos hp_pos _) hpow_le).trans
      (Real.log_le_log hg_pos hindex)
    rwa [Real.log_pow] at hl
  have hlte' : (n : ℝ) = (padicValRat p (u - 1) : ℝ) + (padicValNat p g : ℝ) := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℝ)) hlte
  have hroot_large : e * t.logHeight < h := by
    rw [hlte', add_mul] at hmass
    linarith
  have hg_bound : (g : ℝ) < 1 / e := by
    apply (lt_div_iff₀ he).2
    have hr := mul_lt_mul_of_pos_left hroot_large hg_pos
    rw [hh_scaled] at hr
    have hh : (g : ℝ) * e * t.logHeight < 1 * t.logHeight := by
      rw [mul_assoc, one_mul]
      exact hr.trans_le hsource_hi
    exact lt_of_mul_lt_mul_right hh hH_pos.le
  have hsmall : g < p := by exact_mod_cast hg_bound.trans hprime_size
  have hval_zero : padicValNat p g = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => hsmall.not_ge (Nat.le_of_dvd hg hd))
  have hdepth : padicValRat p (u - 1) = (n : ℤ) := by
    simpa only [hval_zero, Nat.cast_zero, add_zero] using hlte.symm
  have h_h_lo : (e / 2) * Real.exp (3 * e * t.thirdLogRadical) ≤ h := by
    have hs : t.logHeight / 2 ≤ (g : ℝ) * h := by linarith
    have he' : (g : ℝ) * e ≤ 1 := (lt_div_iff₀ he).1 hg_bound |>.le
    have hy : (g : ℝ) * ((e / 2) * Real.exp (3 * e * t.thirdLogRadical)) ≤ t.logHeight / 2 := by
      have hq := mul_le_mul_of_nonneg_right he' (Real.exp_pos (3 * e * t.thirdLogRadical)).le
      nlinarith
    exact le_of_mul_le_mul_left (hy.trans hs) hg_pos
  have h_h_hi : h ≤ t.logHeight := by
    calc
      h ≤ (g : ℝ) * h :=
        le_mul_of_one_le_left (le_of_lt (lt_trans (mul_pos he hH_pos) hroot_large))
          (by exact_mod_cast hg)
      _ ≤ t.logHeight := hh_scaled.le.trans hsource_hi
  have hreal' : |Real.log (u : ℝ)| ≤ (2 * e / 100) * h := by
    have hs := (selected_real_log t ho).trans hreal
    rw [hu_pow, Rat.cast_pow, Real.log_pow, abs_mul, abs_of_nonneg hg_pos.le] at hs
    apply le_of_mul_le_mul_left _ hg_pos
    rw [mul_left_comm, hh_scaled]
    nlinarith [mul_le_mul_of_nonneg_left
      (show t.logHeight ≤ 2 * AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.Statement.selectedSource t) by linarith) he.le]
  refine ⟨u, g, hu, hu_ne, hg, hg_bound, hu_pow, hprim, hdepth, h_h_lo, h_h_hi, ?_, ?_, hreal'⟩
  · exact (mul_le_mul_of_nonneg_left h_h_hi (by positivity)).trans_lt hmass
  · simpa only [hdepth, Int.cast_natCast, add_comm] using hroot

end AbcSubexp.ContactPrime
