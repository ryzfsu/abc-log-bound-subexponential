/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S4_ExteriorE2.PivotedSource
public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeExponentHeight
public import AbcTwoNinths.Paper.S4_ExteriorE2.PivotedGridGeometry
public import AbcTwoNinths.Paper.S4_ExteriorE2.OrientedShortProjection
public import AbcTwoNinths.Paper.S4_ExteriorE2.ReducedOrientedPlane
public import Subexp.Prerequisites.PlaneHeightBounds

/-!
# Exclusion of a deep cutoff modulus

A modulus below the finite-place cutoff cannot carry a fixed share of the height
at arbitrarily large radical scale. The projection grid depends on the positive rate.

## Main results
* `AbcSubexp.ContactPrime.excludeModulus_of_posRate`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime

open Real

private theorem planeLogBound {c d : ℕ} {H h U Z ℓ : ℝ}
    (hH : 0 < H) (hlog : log H ≤ 4 * ℓ) (hℓ : 1 ≤ ℓ)
    (hU : ℓ ≤ U) (hZ : ℓ ≤ Z) (hh : h ≤ 2 * H)
    (hc : 0 < c) (hcu : (c : ℝ) * U ≤ 3 * h) (hdz : (d : ℝ) * Z ≤ 2 * h) :
    log ((d : ℝ) / (U / ℓ) + (c : ℝ) / (Z / ℓ)) + 1 ≤ 15 * ℓ := by
  have he : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hu : 1 ≤ U / ℓ := (one_le_div he).2 hU
  have hz : 1 ≤ Z / ℓ := (one_le_div he).2 hZ
  have hp : 0 < (d : ℝ) / (U / ℓ) + (c : ℝ) / (Z / ℓ) :=
    add_pos_of_nonneg_of_pos (div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hu))
      (div_pos (by exact_mod_cast hc) (zero_lt_one.trans_le hz))
  have hd' := div_le_self (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hu
  have hc' := div_le_self (Nat.cast_nonneg c : (0 : ℝ) ≤ c) hz
  have hsize : (d : ℝ) / (U / ℓ) + (c : ℝ) / (Z / ℓ) ≤ 10 * H := by
    have hu' := mul_le_mul_of_nonneg_left (hℓ.trans hU) (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have hz' := mul_le_mul_of_nonneg_left (hℓ.trans hZ) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith
  have h := log_le_log hp hsize
  rw [log_mul (by norm_num) hH.ne'] at h
  linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]

/-- At every fixed positive growth rate, a sufficiently deep modulus on the
minimum-radical side cannot satisfy the cutoff, scale and mass inequalities. -/
theorem excludeModulus_of_posRate {β σ θ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) (hgap : 2 * σ ≤ β) (hθ : 0 < θ) :
    ∃ (X : ℝ) (minDepth : ℕ), ∀ t : AbcTwoNinths.Basic.Triple, t.a ≤ t.b →
      X ≤ t.thirdLogRadical → exp (β * t.thirdLogRadical) ≤ t.logHeight →
      ∀ M L : ℕ, 3 ≤ M → minDepth ≤ L → M ^ L ∣ AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t) →
        (¬ 2 ∣ M ∨ 4 ∣ M) → (β - σ) * t.thirdLogRadical / 2 ≤ log (M : ℝ) →
        log (M : ℝ) ≤ log t.logHeight - σ * t.thirdLogRadical → log t.logHeight ≤ 4 * log (M : ℝ) →
        θ * t.logHeight ≤ (L : ℝ) * log (M : ℝ) → False := by
  classical
  let κ := 16 * θ
  have hκ : 0 < κ := mul_pos (by norm_num) hθ
  have hκθ : κ / 16 = θ := by dsimp [κ]; ring
  let Q₀ : ℝ := max 48 (44236800 / κ)
  have hQ₀48 : 48 ≤ Q₀ := le_max_left _ _
  have hQ₀ : 0 < Q₀ := by linarith
  let Q := ⌈max 1 (2 * Q₀ / (β - σ))⌉₊
  have hQ1 : 1 ≤ (Q : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hQr : 0 < (Q : ℝ) := zero_lt_one.trans_le hQ1
  have hQ : 0 < Q := by exact_mod_cast hQr
  have hscale : 2 * Q₀ ≤ (Q : ℝ) * (β - σ) :=
    (div_le_iff₀ (by linarith)).1 ((le_max_right _ _).trans (Nat.le_ceil _))
  let A := 4 / θ * log (8 / (θ * log 2))
  obtain ⟨B, hB⟩ := AbcTwoNinths.ExteriorE2.eventualConstantGridCost Q (θ := θ) hσ
  refine ⟨max (max B 1) (A / β), ⌈146 + 2 * (64 / κ)⌉₊, ?_⟩
  intro t hord hx hrate M L hM hL hd hpar hell hcut hlog hmass
  have hxB := (le_max_left B 1).trans ((le_max_left _ _).trans hx)
  have hxpos : 0 < t.thirdLogRadical := zero_lt_one.trans_le ((le_max_right B 1).trans ((le_max_left _ _).trans hx))
  have hH := (exp_pos _).trans_le hrate
  have hA : A ≤ t.logHeight := by
    have hb := (div_le_iff₀ hβ).1 ((le_max_right _ _).trans hx)
    linarith only [hb, Real.add_one_le_exp (β * t.thirdLogRadical), hrate]
  have hLr : 146 + 2 * (64 / κ) ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have hLpos : 0 < L := by
    exact_mod_cast (show 0 < (L : ℝ) by linarith [show 0 < 64 / κ by positivity])
  have hM2 : 2 ≤ M := by omega
  have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  let ℓ := log (M : ℝ)
  have hℓ : 1 ≤ ℓ := ((lt_log_iff_exp_lt hMp).2
    (exp_one_lt_three.trans_le (by exact_mod_cast hM))).le
  have hℓp : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hcap : (M : ℝ) ≤ t.logHeight * exp (-σ * t.thirdLogRadical) := by
    rw [← exp_log hH, ← exp_add, ← Real.log_le_iff_le_exp hMp]
    linarith only [hcut]
  have hmκ : κ * t.logHeight / 16 ≤ (L : ℝ) * ℓ := by
    calc κ * t.logHeight / 16 = θ * t.logHeight := by dsimp [κ]; ring
         _ ≤ _ := hmass
  obtain ⟨s⟩ := AbcTwoNinths.ExteriorE2.actualSource t hord hM hLpos hd
  obtain ⟨V, g, hg, hpiv, hV, he, hgen, hgκ, hdep, hlte, hroot, hHt, hfloor⟩ :=
    AbcTwoNinths.ExteriorE2.generatorOfKernel s.q s.hprime s.hcop s.hinj s.E s.hroof s.hkernel hM2 hpar s.hdepth
      hH hκ hmκ s.hheight.2 (by rwa [hκθ])
  let w := fun j => log (s.q j : ℝ)
  have hw j : 0 < w j := log_pos (by exact_mod_cast (s.hprime j).one_lt)
  let v := fun i => V (.inr i)
  let k := (V (.inl ())).toNat
  have hk : (k : ℤ) = V (.inl ()) := Int.toNat_of_nonneg hpiv.le
  have hkpos : 0 < k := by exact_mod_cast (hk.symm ▸ hpiv : 0 < (k : ℤ))
  have hshape : Sum.elim (fun _ : Unit => (k : ℤ)) v = V := by
    funext j
    rcases j with ⟨⟩ | i
    · exact hk
    · rfl
  have hroof : t.logHeight ≤ (k : ℝ) * ((g : ℝ) * (3 * t.thirdLogRadical)) := by
    have hr := AbcTwoNinths.ExteriorE2.roofMass w s.E (.inl ()) (fun j => (hw j).le) s.hroof s.hmax s.hheight.1 s.hweights
    have he' : s.E (.inl ()) = (g : ℤ) * k := by rw [he, hk]; simp
    rw [he', Int.cast_mul, Int.cast_natCast, Int.cast_natCast] at hr
    linarith only [hr]
  have hdim : (Fintype.card s.i : ℝ) ≤ s.S.card := by
    exact_mod_cast (show Fintype.card s.i ≤ s.S.card by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective (Subtype.val : s.i → s.S) Subtype.val_injective)
  have hcost := hB t hxB s.S s.hsupport (3 * t.thirdLogRadical) (by positivity) le_rfl
  let : NeZero M := ⟨by omega⟩
  let r := AbcTwoNinths.ExteriorE2.monomialReduction M s.q s.hcop
  have hline : ∀ a ∈ r.ker, AbcTwoNinths.Basic.roofProjection (k : ℤ) v a = 0 →
      ∃ m : ℤ, a = m • Sum.elim (fun _ : Unit => (k : ℤ)) v := by
    intro a ha hz
    rw [hshape]
    exact hgen a ha (by simpa only [hk, v] using hz)
  have hshort := AbcTwoNinths.ExteriorE2.shortProjectionOfCutoffImage r hkpos hQ v hline
    (show 1 ≤ (g : ℝ) by exact_mod_cast hg) hH (show 0 < 3 * t.thirdLogRadical by positivity) hθ
    hroof hmass hlte hroot
    ((log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hM2)).trans hfloor.le)
    hA (AbcTwoNinths.ExteriorE2.rangeBound M s.q s.hcop) hcap
    (by linarith only [hcost, mul_le_mul_of_nonneg_right hdim (Real.log_nonneg hQ1)])
  have hxQ : t.thirdLogRadical / (Q : ℝ) ≤ ℓ / Q₀ := by
    apply (div_le_div_iff₀ hQr hQ₀).2
    nlinarith only [mul_le_mul_of_nonneg_right hscale hxpos.le,
      mul_le_mul_of_nonneg_left hell hQr.le]
  have hW : (∑ i, w (.inr i)) ≤ 3 * t.thirdLogRadical := by
    have hs : (∑ j, w j) ≤ 3 * t.thirdLogRadical := s.hweights
    rw [Fintype.sum_sum_type] at hs
    exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => (hw (.inl j)).le)).trans hs
  have hgrid : 4 * ((∑ i, w (.inr i)) / (Q : ℝ)) ≤ ℓ := by
    calc
      _ ≤ 12 * (t.thirdLogRadical / (Q : ℝ)) := by
        rw [← mul_div_assoc, ← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hQr.le
        linarith only [hW]
      _ ≤ 12 * (ℓ / Q₀) := by gcongr
      _ ≤ ℓ := by
        rw [← mul_div_assoc, div_le_iff₀ hQ₀]
        nlinarith only [mul_le_mul_of_nonneg_left hQ₀48 hℓp.le, hℓp]
  have hplane := AbcTwoNinths.ExteriorE2.orientedPlaneOfShortProjection r (by exact_mod_cast hkpos.ne') v
    (hshape.symm ▸ hV) hline w hw Q hℓp
    (AbcTwoNinths.ExteriorE2.kernelWeightedHeightGtLog s.q s.hprime s.hcop s.hinj hM2) hgrid hshort
  dsimp only at hplane
  rw [hshape] at hplane
  obtain ⟨u, hu, z, hz, c, d, heq, hcd, hc, hd', hind, huℓ, hzℓ, hp, hcu, hdz⟩ := hplane
  have harea := AbcSubexp.Prerequisites.planeHeightProductLe hQ hH.le
    (Finset.sum_nonneg fun j _ => (hw (.inr j)).le) hHt hW hp
  have hlarge : 146 + 2 * (Nat.log 2 g : ℝ) ≤ L := by
    linarith only [hLr, AbcTwoNinths.ExteriorE2.generatorLossLe hgκ]
  apply AbcTwoNinths.ExteriorE2.excludeOrientedPlane (x := ℓ) (Q := Q₀) s.q s.hprime s.hcop s.hinj
    V u z heq hu hz hind hdep hM hH.le hκ (le_max_right _ _) (by linarith) hmκ _ hlarge
    huℓ.le hzℓ.le hcd hc hd' (planeLogBound hH hlog hℓ huℓ.le hzℓ.le hHt hc hcu hdz)
    le_rfl le_rfl
  simpa only [mul_div_assoc] using harea.trans
    (show 24 * t.logHeight * t.thirdLogRadical / (Q : ℝ) ≤ 24 * t.logHeight * ℓ / Q₀ by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hxQ (by positivity))

end AbcSubexp.ContactPrime
