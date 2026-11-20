/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.SignedPrincipalUnitBracket
public import AbcTwoNinths.Paper.S6_Diamond.SelectedShearEstimate
public import AbcTwoNinths.Paper.S6_Diamond.ProjectedKernelBasis
public import AbcTwoNinths.Paper.S6_Diamond.ProjectedPrincipalUnits
public import Subexp.Prerequisites.CoordinateExclusion

/-!
# Weighted shear and projected separation

The contact bounds in Section 3 exclude short shears of the old signed kernel
at an arbitrary positive contact rate.

## Main results
* `AbcSubexp.TupleCounting.nativeWeightedShear`
* `AbcSubexp.TupleCounting.projectedSeparation`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real

private theorem logFactorBound {e x ell h b : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 10) (hx : 12 ≤ x) (hell : 1 ≤ ell)
    (hroof : 2 * e * x ≤ ell) (hh : 0 < h) (hcap : log h ≤ 2 * x)
    (hb : 0 < b) (hscale : ell * (b / 2) ≤ 10 * h) :
    max 4 (log (exp 2 * ell * (b / 2)) / ell) ≤ 2 / e := by
  have hl : 0 < ell := by linarith
  have harg : 0 < exp 2 * ell * (b / 2) := by positivity
  have hlog := log_le_log harg (show exp 2 * ell * (b / 2) ≤ exp 2 * (10 * h) by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (exp_pos _).le)
  rw [log_mul (exp_ne_zero _) (by positivity), log_exp, log_mul (by norm_num) hh.ne'] at hlog
  have h10 : log 10 ≤ 9 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  apply max_le ((le_div_iff₀ he).2 (by linarith))
  apply (div_le_iff₀ hl).2
  have hbound : 2 * x ≤ (2 / e) * ell / 2 := by
    rw [show (2 / e) * ell / 2 = ell / e by ring]
    apply (le_div_iff₀ he).2
    linarith
  linarith

private theorem shortProductContradiction {e x ell h n P D : ℝ}
    (he : 0 < e) (hx : 0 < x) (hh : 0 < h) (hell : 2 * e * x ≤ ell)
    (hn : 2 * e * h ≤ n * ell) (hP : 0 ≤ P)
    (hprod : P * log x ≤ 192 * h * x) (hD0 : 0 ≤ D) (hD : D ≤ 2 / e)
    (hB : n * ell ^ 2 ≤ 588 * P * D ^ 2)
    (hon : 112896 < e ^ 4 * log x) : False := by
  have hl : 0 < log x := by
    by_contra! h'
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ e ^ 4 by positivity) h']
  have hroof0 : 0 ≤ ell := (show 0 < 2 * e * x by positivity).le.trans hell
  have hscale : D * e ≤ 2 := (le_div_iff₀ he).mp hD
  have hs : (D * e) ^ 2 ≤ 4 := by
    have h' := mul_self_le_mul_self (mul_nonneg hD0 he.le) hscale
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hn hroof0
  have h2 := mul_le_mul_of_nonneg_left hell (show 0 ≤ 2 * e * h by positivity)
  have h3 : 4 * e ^ 2 * h * x ≤ 588 * P * D ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg e)
  have h5 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 588 * P by positivity)
  have h6 : 4 * e ^ 4 * h * x ≤ 2352 * P := by nlinarith
  have h7 := mul_le_mul_of_nonneg_right h6 hl.le
  have h8 := mul_lt_mul_of_pos_right hon (show 0 < 4 * h * x by positivity)
  nlinarith

section SignedKernel

variable {J : Type*} [Fintype J] {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable (q : J → ℕ) (hq : ∀ i, (q i).Prime) (avoid : ∀ i, p ≠ q i)

local notation "γ" => AbcTwoNinths.ExteriorE2.gammaStar (AbcTwoNinths.ExteriorE2.residue q hq avoid) (AbcTwoNinths.ExteriorE2.monomial q hq)
local notation "K" => AbcTwoNinths.ExteriorE2.Kernel (AbcTwoNinths.ExteriorE2.residue q hq avoid)
local notation "weight" => (fun i => Real.log (q i : ℝ))

private theorem mass_le_twice_signed_height (hqinj : Function.Injective q) (s : K) :
    AbcTwoNinths.Basic.mass weight s.val.toAdd ≤ 2 * AbcTwoNinths.Basic.rationalHeight (γ s : ℚ) := by
  have hmonomial : (AbcTwoNinths.ExteriorE2.monomial q hq s.val : ℚ) =
      AbcTwoNinths.PolyCap.prodMonomial q s.val.toAdd := by
    simp [AbcTwoNinths.ExteriorE2.monomial, AbcTwoNinths.ExteriorE2.eval, AbcTwoNinths.ExteriorE2.ratUnit,
      AbcTwoNinths.PolyCap.prodMonomial]
  have heightEq := (AbcTwoNinths.PolyCap.ratHeightProdMonomial q hq hqinj s.val.toAdd).1
  have hsigned : AbcTwoNinths.Basic.rationalHeight (γ s : ℚ) = AbcTwoNinths.Basic.rationalHeight (AbcTwoNinths.PolyCap.prodMonomial q s.val.toAdd) := by
    by_cases hr : AbcTwoNinths.ExteriorE2.residue q hq avoid s.val = 1
    · simp [AbcTwoNinths.ExteriorE2.gammaStar, AbcTwoNinths.ExteriorE2.signUnit, hr, hmonomial]
    · simp [AbcTwoNinths.ExteriorE2.gammaStar, AbcTwoNinths.ExteriorE2.signUnit, hr, hmonomial, AbcTwoNinths.Basic.rationalHeight]
  rw [hsigned, heightEq, two_mul, AbcTwoNinths.Basic.mass]
  have hsplit : (∑ j, |(s.val.toAdd j : ℝ)| * weight j) =
      ∑ j, (max ((s.val.toAdd j : ℝ) * weight j) 0 +
        max (-((s.val.toAdd j : ℝ) * weight j)) 0) := by
    apply Finset.sum_congr rfl
    intro j _
    have hw : 0 ≤ weight j := Real.log_nonneg (by exact_mod_cast (hq j).one_le)
    rw [max_zero_add_max_neg_zero_eq_abs_self, abs_mul, abs_of_nonneg hw]
  rw [hsplit, Finset.sum_add_distrib]
  exact add_le_add (le_max_left _ _) (le_max_right _ _)

/-- A nonaxial vector in the old residue kernel has weighted distance at least
`2 * x / log x` from every real multiple of the axial vector in Section 4. -/
theorem nativeWeightedShear (hp : 5 ≤ p) (hqinj : Function.Injective q)
    (s w : K) {j : J} (hj : s.val.toAdd j ≠ 0)
    (hind : ¬ ∃ a : ℚ, ∀ i, (w.val.toAdd i : ℚ) = a * (s.val.toAdd i : ℚ))
    {e x α : ℝ} (he : 0 < e) (herate : e ≤ 1 / 10) (hx : 12 ≤ x)
    (hroof : 2 * e * x ≤ log (p : ℝ))
    (hcontact : 2 * e * AbcTwoNinths.Basic.rationalHeight (γ s : ℚ) ≤
      (padicValRat p ((γ s : ℚ) - 1) : ℝ) * log (p : ℝ))
    (hcap : log (AbcTwoNinths.Basic.rationalHeight (γ s : ℚ)) ≤ 2 * x)
    (honset : 112896 < e ^ 4 * log x) :
    2 * x / log x ≤ ∑ i, |(w.val.toAdd i : ℝ) - α * (s.val.toAdd i : ℝ)| * weight i := by
  let h := AbcTwoNinths.Basic.rationalHeight (γ s : ℚ)
  let ell := log (p : ℝ)
  let T := 2 * x / log x
  let V := AbcTwoNinths.Basic.mass weight s.val.toAdd
  have hxpos : 0 < x := by linarith
  have hxlog : 0 < log x := Real.log_pos (by linarith)
  change 2 * e * x ≤ ell at hroof
  have hell2 : 2 * log 2 ≤ ell := by
    calc
      _ = log ((2 : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
      _ ≤ ell := Real.log_le_log (by positivity)
        (by exact_mod_cast show 2 ^ 2 ≤ p by omega)
  have hell : 1 ≤ ell := by linarith [Real.log_two_gt_d9]
  have hellpos : 0 < ell := by linarith
  have heightFloor (z : K) (hz : z ≠ 1) : ell / 2 ≤ AbcTwoNinths.Basic.rationalHeight (γ z : ℚ) := by
    have hzchar : (γ z : ℚ) ≠ 1 := by
      intro hzchar
      apply hz
      apply AbcTwoNinths.ExteriorE2.modularResidueLatticeInjective q hq hqinj avoid
      rw [map_one]
      exact Units.ext hzchar
    have hf := AbcTwoNinths.Diamond.principalHeightFloor (AbcTwoNinths.Diamond.signedLiftPrincipal q hq avoid z) hzchar
    rw [Real.log_div (by positivity) (by norm_num)] at hf
    change ell - log 2 ≤ AbcTwoNinths.Basic.rationalHeight (γ z : ℚ) at hf
    linarith
  have hs : s ≠ 1 := by
    rintro rfl
    exact hj rfl
  have hh : 0 < h := (by positivity : 0 < ell / 2).trans_le (heightFloor s hs)
  have hV : V ≤ 2 * h := mass_le_twice_signed_height q hq avoid hqinj s
  by_contra! hshort
  obtain ⟨a, b, hdet, hrep, hinj, hu, hv, hprod, hc, hd⟩ :=
    AbcTwoNinths.Diamond.collisionKernelColumns q hq hqinj s w hj hind hshort
  let U := AbcTwoNinths.Diamond.kernelColumn s w a
  let Z := AbcTwoNinths.Diamond.kernelColumn s w b
  let A := AbcTwoNinths.Basic.mass weight (AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd a)
  let B := AbcTwoNinths.Basic.mass weight (AbcTwoNinths.Basic.eval s.val.toAdd w.val.toAdd b)
  have hU : U ≠ 1 := by
    intro hzero
    have hcoord : ((1, 0) : AbcTwoNinths.Basic.ZPair) = (0, 0) := hinj (by
      change AbcTwoNinths.Basic.eval U.val.toAdd Z.val.toAdd (1, 0) = _
      rw [hzero]
      funext i
      simp [AbcTwoNinths.Basic.eval])
    exact one_ne_zero (congrArg Prod.fst hcoord)
  have hZ : Z ≠ 1 := by
    intro hzero
    have hcoord : ((0, 1) : AbcTwoNinths.Basic.ZPair) = (0, 0) := hinj (by
      change AbcTwoNinths.Basic.eval U.val.toAdd Z.val.toAdd (0, 1) = _
      rw [hzero]
      funext i
      simp [AbcTwoNinths.Basic.eval])
    exact one_ne_zero (congrArg Prod.snd hcoord)
  have huFloor := heightFloor U hU
  have hvFloor := heightFloor Z hZ
  change AbcTwoNinths.Basic.rationalHeight (γ U : ℚ) ≤ A at hu
  change AbcTwoNinths.Basic.rationalHeight (γ Z : ℚ) ≤ B at hv
  have hA := huFloor.trans hu
  have hB := hvFloor.trans hv
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  change A * B < 12 * V * T at hprod
  rcases em (b.2 = 0 ∨ a.2 = 0) with hzero | hnonzero
  · have hgcd : Int.gcd b.2 (-a.2) = 1 := by
      have hdiv := dvd_add
        (dvd_mul_of_dvd_right (Int.gcd_dvd_left b.2 (-a.2)) a.1)
        (dvd_mul_of_dvd_right (Int.gcd_dvd_right b.2 (-a.2)) b.1)
      have hdet' : a.1 * b.2 + b.1 * (-a.2) = 1 := by
        unfold AbcTwoNinths.Basic.det at hdet
        linarith
      rw [hdet'] at hdiv
      exact Nat.dvd_one.mp (by exact_mod_cast hdiv)
    have hheightProd : AbcTwoNinths.Basic.rationalHeight (γ U : ℚ) * AbcTwoNinths.Basic.rationalHeight (γ Z : ℚ) ≤ 2 * h * (12 * T) := by
      calc
        _ ≤ A * B := mul_le_mul hu hv (by linarith) hApos.le
        _ ≤ 12 * V * T := hprod.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hV hT]
    have hepow : e ^ 4 ≤ e := by
      have heone : e ≤ 1 := by linarith
      simpa using (pow_le_pow_of_le_one he.le heone (show 1 ≤ 4 by norm_num))
    have heLog : 48 < e * log x := by
      have := mul_le_mul_of_nonneg_right hepow hxlog.le
      linarith
    have hthreshold : 2 * (12 * T) < ell / 2 := by
      have hscaled := mul_lt_mul_of_pos_right heLog hxpos
      calc
        _ = 48 * x / log x := by dsimp [T]; ring
        _ < e * x := (div_lt_iff₀ hxlog).2 (by nlinarith)
        _ ≤ _ := by linarith
    have hz : (γ s : ℚ) = (γ U : ℚ) ^ b.2 * (γ Z : ℚ) ^ (-a.2) := by
      rw [hrep, map_mul, map_zpow, map_zpow, Units.val_mul,
        Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
    have hzero' : b.2 = 0 ∨ -a.2 = 0 := by simpa using hzero
    exact AbcSubexp.Prerequisites.exclude_zero_coordinate (γ U).ne_zero (γ Z).ne_zero hz hgcd hzero' hh
      rfl rfl rfl huFloor hvFloor hheightProd hthreshold
  · rcases not_or.mp hnonzero with ⟨hcne, hane⟩
    let coeff := (b.2.natAbs : ℝ) / (2 * B) + ((-a.2).natAbs : ℝ) / (2 * A)
    let D := max 4 (log (exp 2 * ell * (coeff / 2)) / ell)
    have hcoeffpos : 0 < coeff := by
      have hcpos : 0 < (b.2.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hcne
      have hdpos : 0 < ((-a.2).natAbs : ℝ) := by
        exact_mod_cast Int.natAbs_pos.mpr (neg_ne_zero.mpr hane)
      dsimp [coeff]
      positivity
    have hcoeffMass : (b.2.natAbs : ℝ) * A + ((-a.2).natAbs : ℝ) * B ≤ 10 * h := by
      simp only [Int.natAbs_neg, Nat.cast_natAbs, Int.cast_abs]
      change |(b.2 : ℝ)| * A ≤ 3 * V at hc
      change |(a.2 : ℝ)| * B ≤ 2 * V at hd
      linarith
    have hscale : ell * (coeff / 2) ≤ 10 * h := by
      have hden : 0 < 4 * A * B := by positivity
      have hdenRoof : ell ^ 2 ≤ 4 * A * B := by
        nlinarith [mul_le_mul hA hB (show 0 ≤ ell / 2 by positivity) hApos.le]
      rw [show ell * (coeff / 2) =
          ell * ((b.2.natAbs : ℝ) * A + ((-a.2).natAbs : ℝ) * B) / (4 * A * B) by
        dsimp [coeff]
        field_simp
        ring]
      apply (div_le_iff₀ hden).2
      calc
        _ ≤ ell * (10 * h) := mul_le_mul_of_nonneg_left hcoeffMass hellpos.le
        _ ≤ (10 * h) * ell ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hell (show 0 ≤ 10 * h * ell by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hdenRoof (by positivity)
    have hDu : max (AbcTwoNinths.Basic.rationalHeight (γ U : ℚ)) ell ≤ 2 * A :=
      max_le (by linarith) (by linarith)
    have hDv : max (AbcTwoNinths.Basic.rationalHeight (γ Z : ℚ)) ell ≤ 2 * B :=
      max_le (by linarith) (by linarith)
    have hheightProd : (2 * A * (2 * B)) * log x ≤ 192 * h * x := by
      calc
        _ = 4 * (A * B) * log x := by ring
        _ ≤ 4 * (12 * V * T) * log x := by gcongr
        _ = 96 * V * x := by dsimp [T]; field_simp; ring
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hV hxpos.le]
    have hB1 := AbcTwoNinths.Diamond.liftedBound q hq avoid hp hqinj U Z s hinj
      hcne (neg_ne_zero.mpr hane) hrep hDu hDv
    change (padicValRat p ((γ s : ℚ) - 1) : ℝ) * ell ^ 2 ≤ 588 * (2 * A) * (2 * B) * D ^ 2 at hB1
    exact shortProductContradiction (D := D) he hxpos hh hroof hcontact (by positivity) hheightProd
      (le_trans (by norm_num) (le_max_left _ _))
      (logFactorBound he herate hx hell hroof hh hcap hcoeffpos hscale)
      (by rwa [← mul_assoc (588 : ℝ) (2 * A) (2 * B)]) honset

/-- Every nonzero projected vector of the reindexed old residue kernel has
transverse cost at least `2 * x / log x` in Section 4. -/
theorem projectedSeparation {I : Type*} [Fintype I] (index : Unit ⊕ I ≃ J)
    (hp : 5 ≤ p) (hqinj : Function.Injective q)
    (s : K) (hs : s.val.toAdd (index (.inl ())) ≠ 0)
    {e x : ℝ} (he : 0 < e) (herate : e ≤ 1 / 10) (hx : 12 ≤ x)
    (hroof : 2 * e * x ≤ log (p : ℝ))
    (hcontact : 2 * e * AbcTwoNinths.Basic.rationalHeight (γ s : ℚ) ≤
      (padicValRat p ((γ s : ℚ) - 1) : ℝ) * log (p : ℝ))
    (hcap : log (AbcTwoNinths.Basic.rationalHeight (γ s : ℚ)) ≤ 2 * x)
    (honset : 112896 < e ^ 4 * log x) :
    ∀ w ∈ (AbcTwoNinths.ExteriorE2.residueLatticeReduction (q ∘ index) (fun i => hq (index i)) (fun i => avoid (index i))).ker,
      AbcTwoNinths.ExteriorE2.cost (fun j => weight (index (.inr j))) (AbcTwoNinths.ExteriorE2.project (s.val.toAdd ∘ index) w) <
          2 * x / log x →
        AbcTwoNinths.ExteriorE2.project (s.val.toAdd ∘ index) w = 0 :=
  AbcTwoNinths.Diamond.projectedSeparationOfReindexedShear index q hq avoid s.val.toAdd hs
    (fun w hind _ =>
      nativeWeightedShear q hq avoid hp hqinj s w hs hind he herate hx hroof hcontact hcap honset)

end SignedKernel

end AbcSubexp.TupleCounting
