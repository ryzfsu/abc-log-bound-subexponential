/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S2_Parameters.HeightCeiling
public import Subexp.S3_ContactPrime.HeavyPrime
public import Subexp.S3_ContactPrime.ModulusExclusion
public import Subexp.S3_ContactPrime.PrimitiveContact
public import Subexp.S3_ContactPrime.RealContact
public import Subexp.S3_ContactPrime.SmoothModulus

/-!
# Contact selection on the positive-rate tail

A common onset supplies the real and finite contact estimates, selects a heavy
prime, and preserves its depth after extracting a primitive axial unit.

## Main results
* `AbcSubexp.ContactPrime.exists_contact`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime

open AbcSubexp.Parameters
open Filter

/-- The finite contact estimate holds at each positive rate with a smaller cutoff rate. -/
theorem finiteContact_of_posRate {β σ ν : ℝ}
    (hσ : 0 < σ) (hgap : 2 * σ ≤ β) (hν : 0 < ν) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.a ≤ t.b → X ≤ t.thirdLogRadical →
      Real.exp (β * t.thirdLogRadical) ≤ t.logHeight → AbcTwoNinths.Statement.SmallPrimeMassBound σ ν t := by
  have hβ : 0 < β := by linarith
  have hdiff : 0 < β - σ := by linarith
  have hden : 0 < 4 * (1 + β - σ) := by linarith
  have hθ : 0 < ν * (β - σ) / (4 * (1 + β - σ)) :=
    div_pos (mul_pos hν hdiff) hden
  obtain ⟨A, D, hexclude⟩ := excludeModulus_of_posRate hβ hσ hgap hθ
  obtain ⟨B, hB, htrim⟩ := smoothModulus_of_mass_posRate hσ hgap hν D
  refine ⟨max A B, hB.trans (le_max_right _ _), ?_⟩
  intro t horder hx hhigh
  by_contra hbad
  obtain ⟨M, L, hM, _, hL, hdvd, hparity, hlo, hhi, hlog, hmass⟩ :=
    htrim t ((le_max_right _ _).trans hx) hhigh hbad
  exact hexclude t horder ((le_max_left _ _).trans hx) hhigh M L
    hM hL hdvd hparity hlo hhi hlog hmass

private theorem eventual_height_margin {e : ℝ} (he : 0 < e) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 2 * x ≤ e * Real.exp (3 * e * x) := by
  have hrate : 0 < 3 * e := by positivity
  obtain ⟨Y, hY⟩ := eventually_atTop.1 ((Real.tendsto_exp_div_pow_atTop 1).eventually
    (eventually_ge_atTop (2 / (e * (3 * e)))))
  refine ⟨max 1 (Y / (3 * e)), fun x hx => ?_⟩
  have hx_pos : 0 < x := zero_lt_one.trans_le ((le_max_left _ _).trans hx)
  have harg := (div_le_iff₀ hrate).1 ((le_max_right _ _).trans hx)
  have h := hY (3 * e * x) (by simpa [mul_comm] using harg)
  simp only [pow_one] at h
  have h' := (le_div_iff₀ (mul_pos hrate hx_pos)).1 h
  have hmul := mul_le_mul_of_nonneg_left h' he.le
  calc
    2 * x = e * (2 / (e * (3 * e)) * (3 * e * x)) := by field_simp [he.ne']
    _ ≤ _ := hmul

/-- A sufficiently large ordered high triple supplies the contact data in Section 3. -/
theorem exists_contact (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ t : AbcTwoNinths.Basic.Triple, X ≤ t.thirdLogRadical → t.a ≤ t.b →
      AbcSubexp.High ε t → Nonempty (Contact ε t) := by
  let e := exponent ε
  have he : 0 < e := lt_min hε (by norm_num)
  have he_small : e ≤ 1 / 10 := min_le_right _ _
  have hβ : 0 < 3 * e := by positivity
  have hσ : 0 < 3 * e / 50 := by positivity
  have hgap : 2 * (3 * e / 50) ≤ 3 * e := by linarith
  have hrate : 0 < 147 * e / 50 := by positivity
  obtain ⟨A, _, hreal⟩ := realContact_of_posRate (3 * e) (e / 100) hβ (by positivity)
  obtain ⟨B, _, hfinite⟩ := finiteContact_of_posRate hσ hgap (show (0 : ℝ) < 1 / 25 by norm_num)
  obtain ⟨C, hcap⟩ := AbcSubexp.exists_height_onset
  obtain ⟨D, hlarge⟩ := eventual_height_margin he
  let primeBound := Real.log (max 5 (1 / e)) / (147 * e / 50)
  let heightBound := max 1 (Real.log 2 - Real.log (Real.log 2))
  let X := max (max A B) (max (max C D) (max primeBound heightBound))
  refine ⟨X, fun t hx hord hhigh => ?_⟩
  have hab := (le_max_left _ _).trans hx
  have hcdb := (le_max_right _ _).trans hx
  have hcd := (le_max_left _ _).trans hcdb
  have hbounds := (le_max_right _ _).trans hcdb
  have hlogH := hcap t ((le_max_left _ _).trans hcd)
  have hr := hreal t hord ((le_max_left _ _).trans hab) hhigh
  have hf := hfinite t hord ((le_max_right _ _).trans hab) hhigh
  have hhBound : heightBound ≤ t.thirdLogRadical := (le_max_right _ _).trans hbounds
  have hx_one : 1 ≤ t.thirdLogRadical := (le_max_left _ _).trans hhBound
  have hx_pos : 0 < t.thirdLogRadical := zero_lt_one.trans_le hx_one
  have hH : Real.exp (3 * e * t.thirdLogRadical) ≤ t.logHeight := hhigh
  have height_pos : 0 < t.logHeight := (Real.exp_pos _).trans_le hH
  have hheight_margin : 2 * t.thirdLogRadical ≤ e * t.logHeight :=
    (hlarge t.thirdLogRadical ((le_max_right _ _).trans hcd)).trans (mul_le_mul_of_nonneg_left hH he.le)
  have hlog_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hheight : 2 * Real.log 2 ≤ t.logHeight := by
    have hlog_le := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hproduct := mul_le_mul_of_nonneg_right he_small height_pos.le
    linarith
  have herror : Real.log 2 + Real.log (t.logHeight / Real.log 2) ≤ e * t.logHeight := by
    rw [Real.log_div height_pos.ne' hlog_two_pos.ne']
    have hlog_bound : Real.log 2 - Real.log (Real.log 2) ≤ t.thirdLogRadical :=
      (le_max_right _ _).trans hhBound
    linarith
  obtain ⟨p, hp, _, hlo, hhi, hmass⟩ :=
    heavyPrime_of_contact_mass t he he_small hx_pos hord hH hr hf
  have prime_isPrime := Nat.prime_of_mem_primeFactors hp
  have prime_pos : 0 < (p : ℝ) := by exact_mod_cast prime_isPrime.pos
  have hpMax : max 5 (1 / e) < (p : ℝ) := by
    have hb : primeBound ≤ t.thirdLogRadical := (le_max_left _ _).trans hbounds
    have hbl := (div_le_iff₀ hrate).1 hb
    exact (Real.log_lt_log_iff (by positivity) prime_pos).1
      ((by simpa [primeBound, mul_comm] using hbl : Real.log (max 5 (1 / e)) ≤
        (147 * e / 50) * t.thirdLogRadical).trans_lt hlo)
  have hp5 : 5 < p := by exact_mod_cast (le_max_left (5 : ℝ) (1 / e)).trans_lt hpMax
  have : Fact p.Prime := ⟨prime_isPrime⟩
  have : Fact (2 < p) := ⟨by omega⟩
  obtain ⟨u, g, hu, hne, hg, hgBound, hpow, hpPrimitive, hn, hhlo, hhhi, hdlo, hdhi, har⟩ :=
    primitive_heavy_contact t hp he hord hr hH hheight herror
      ((le_max_right (5 : ℝ) (1 / e)).trans_lt hpMax) hmass
  exact ⟨{
    prime := p
    prime_isPrime := prime_isPrime
    prime_gt_five := hp5
    prime_dvd_side := Nat.dvd_of_mem_primeFactors hp
    log_lower := by linarith
    log_upper := hhi
    source := u
    source_principal := hu
    source_ne_one := hne
    sourcePower := g
    sourcePower_pos := hg
    sourcePower_le := hgBound.le
    source_eq := hpow.symm
    source_primitive := hpPrimitive
    depth := padicValNat p (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t))
    depth_eq := hn
    depth_side := rfl
    height_cap := (Real.log_le_iff_le_exp height_pos).1 hlogH
    axial_height_lower := hhlo
    axial_height_upper := hhhi
    depth_share := hdlo
    depth_share_upper := hdhi
    real_contact := by
      rw [Real.log_abs]
      simpa [show 2 * e / 100 = e / 50 by ring] using har }⟩

end AbcSubexp.ContactPrime
