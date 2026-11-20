/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.FreshThirdWindow
public import Subexp.S4_TupleCounting.CommonTaggedBall
public import Subexp.S4_TupleCounting.ProjectedPrimeLattice
public import Subexp.Prerequisites.WeightedBallDimension
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# The number of auxiliary primes in one ball

The volume estimate with dimension coefficient seven absorbs the constant lost
in the third-window count. This yields the common-family lower bound of Section 4.

## Main results
* `AbcSubexp.TupleCounting.exists_commonPrimeFamily`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real MeasureTheory
open scoped ENNReal

private theorem commonPrimeCount_lower {e x p h Q W μ n : ℝ}
    (hx : exp 1 ≤ x) (hp : 0 < p) (hh : 0 < h) (hμ : 0 < μ)
    (hQ : 0 ≤ Q) (hn : 0 ≤ n) (hTotal : μ ≤ x*p/h)
    (ht : 0 < log (auxiliaryPrimeCutoff e x p h)) (htx : log (auxiliaryPrimeCutoff e x p h) ≤ x)
    (hSupply : auxiliaryPrimeCutoff e x p h / (8*log (auxiliaryPrimeCutoff e x p h)) ≤ Q)
    (hBall : exp (-(7*x/log x) * log (3*log x)) ≤ W)
    (hCover : Q*W/μ ≤ n) :
    exp ((e^2/10)*x - 12*x*log (3*log x)/log x) / (4*x^2) ≤ n := by
  let L := x/log x * log (3*log x)
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlx := Real.log_pos hx1
  have hlx1 : 1 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 1) hx
  have hXL : 1 ≤ x/log x :=
    (one_le_div hlx).2 (by linarith [log_le_sub_one_of_pos hx0])
  have hL : log 2 ≤ L := calc
    log 2 ≤ log (3*log x) := log_le_log (by norm_num) (by linarith)
    _ ≤ L := le_mul_of_one_le_left (log_nonneg (by linarith)) hXL
  have hShift : exp ((e^2/10)*x - 12*L)*2 ≤ exp ((e^2/10)*x - 7*L) := by
    conv_lhs => rhs; rw [← exp_log (by norm_num : 0 < (2 : ℝ))]
    rw [← exp_add, exp_le_exp]
    linarith [log_nonneg (by norm_num : 1 ≤ (2 : ℝ))]
  have hB : exp (-7*L) ≤ W := by
    convert hBall using 2
    dsimp [L]
    ring
  have hM : auxiliaryPrimeCutoff e x p h ≤ Q*(8*x) :=
    ((div_le_iff₀ (by positivity)).1 hSupply).trans
      (mul_le_mul_of_nonneg_left (by linarith) hQ)
  have hMH : exp ((e^2/10)*x)*p ≤ auxiliaryPrimeCutoff e x p h * h := by
    have hmax := mul_le_mul_of_nonneg_right (le_max_right (p^(1/2 : ℝ)) (p/h)) hh.le
    rw [div_mul_cancel₀ _ hh.ne'] at hmax
    simpa only [auxiliaryPrimeCutoff, mul_assoc] using
      mul_le_mul_of_nonneg_left hmax (exp_pos ((e^2/10)*x)).le
  have hC : Q*W*h ≤ n*(x*p) := calc
    Q*W*h ≤ n*μ*h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hμ).1 hCover) hh.le
    _ ≤ n*(x*p/h)*h := by gcongr
    _ = _ := by field_simp
  have hStrong : exp ((e^2/10)*x - 7*L) ≤ n*(8*x^2) := by
    apply (mul_le_mul_iff_left₀ hp).1
    calc
      exp ((e^2/10)*x-7*L)*p = (exp ((e^2/10)*x)*p)*exp (-7*L) := by
        rw [sub_eq_add_neg, exp_add]; ring_nf
      _ ≤ (Q*(8*x)*h)*W := mul_le_mul
        (hMH.trans (mul_le_mul_of_nonneg_right hM hh.le)) hB (exp_pos _).le (by positivity)
      _ = (Q*W*h)*(8*x) := by ring
      _ ≤ (n*(x*p))*(8*x) := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = n*(8*x^2)*p := by ring
  have hEq : 12*x*log (3*log x)/log x = 12*L := by dsimp [L]; ring
  rw [hEq, div_le_iff₀ (by positivity : 0 < 4*x^2)]
  linarith only [hShift.trans hStrong]

/-- A single tagged center and a finite family of fresh primes with the Section 4 lower bound.
The argument `hsupply` is provided uniformly by `eventually_auxiliaryFreshPrimes_card`. -/
theorem exists_commonPrimeFamily (S : Finset ℕ) (roof : ℕ) {R p : ℕ}
    (hR : 0 < R) (hp : 0 < p) (hS : ∀ q ∈ S, q.Prime) (hdiv : ∀ q ∈ S, q ∣ R)
    {e x h : ℝ} (hx : exp 1 ≤ x) (hxR : log R = 3*x) (hh : 0 < h)
    (ht : 0 < log (auxiliaryPrimeCutoff e x p h)) (htx : log (auxiliaryPrimeCutoff e x p h) ≤ x)
    (hsupply : auxiliaryPrimeCutoff e x p h / (8*log (auxiliaryPrimeCutoff e x p h)) ≤
      ((auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h)).card : ℝ))
    {G : Type*} [AddCommGroup G] [Finite G] (red : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof) →+ G)
    (hcard : (Nat.card G : ℝ) = ((p : ℝ)-1)/2) (s : red.ker)
    (hroof : h/(2*x) ≤ |((s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (.inl ()) : ℝ)|)
    (hprim : ∀ (a : ℤ) (w : red.ker), a • w = s → IsUnit a)
    (hshort : ∀ w ∈ red.ker,
      AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ)) (AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w) < x/log x →
        AbcTwoNinths.ExteriorE2.project (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) w = 0)
    (label : ℕ → G) (center : ℕ → AbcTwoNinths.ExteriorE2.Coord (AbcTwoNinths.ExteriorE2.OldIndex S roof)) :
    ∃ (D : Set (AbcTwoNinths.ExteriorE2.Coord (AbcTwoNinths.ExteriorE2.OldIndex S roof))) (z : AbcSubexp.Prerequisites.Tag red × AbcTwoNinths.ExteriorE2.Coord (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (P : Finset ℕ),
      IsAddFundamentalDomain (AbcTwoNinths.ExteriorE2.projected red (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof))).toAddSubgroup D volume ∧
      P ⊆ auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h) ∧
      exp ((e^2/10)*x - 12*x*log (3*log x)/log x) / (4*x^2) ≤ P.card ∧
      ∀ q ∈ P, z.1 = AbcSubexp.Prerequisites.tag red (label q) ∧
        z.2 ∈ AbcTwoNinths.ExteriorE2.wrapped (L := (AbcTwoNinths.ExteriorE2.projected red (s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof))).toAddSubgroup) D
          (AbcTwoNinths.ExteriorE2.ball (fun j => log (j.val : ℝ)) (center q) (x/log x/2)) := by
  classical
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  obtain ⟨D, hD, hDm, hDf, hvol, hmass⟩ :=
    exists_projected_domain_mass_le red hcard s hx0 hh hroof hprim
  let Q := auxiliaryFreshPrimes R (auxiliaryPrimeCutoff e x p h)
  let w := fun j : AbcTwoNinths.ExteriorE2.OldIndex S roof => log (j.val : ℝ)
  have hw (j : AbcTwoNinths.ExteriorE2.OldIndex S roof) : 0 ≤ w j :=
    log_nonneg (by exact_mod_cast (hS j.val (Finset.mem_erase.mp j.property).2).one_le)
  obtain ⟨z, P, hsub, hcount, hmem⟩ := existsCommonTaggedBall red s w hw
    (x/log x) Q label center hD hDm hDf hshort hvol
  rw [AbcSubexp.Prerequisites.normalization red hDf hvol] at hmass
  have hμ : 0 < (Nat.card G : ℝ) / |((s : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof)) (.inl ()) : ℝ)| :=
    div_pos (by exact_mod_cast Nat.card_pos) ((div_pos hh (by positivity)).trans_le hroof)
  have hB := AbcSubexp.Prerequisites.smallBall_subexponential_lower S roof hS (AbcTwoNinths.ExteriorE2.supportProductLe S hR hS hdiv) hx hxR 0
  have hB' : exp (-(7*x/log x)*log (3*log x)) ≤
      volume.real (AbcTwoNinths.ExteriorE2.ball w 0 (x/log x/2)) := by
    simpa only [AbcSubexp.Prerequisites.smallBall, AbcTwoNinths.ExteriorE2.ball, AbcTwoNinths.ExteriorE2.cost, Pi.sub_apply, div_eq_inv_mul, mul_one] using hB
  exact ⟨D, z, P, hD, hsub,
    commonPrimeCount_lower hx (by exact_mod_cast hp) hh hμ (Nat.cast_nonneg Q.card)
      (Nat.cast_nonneg P.card) hmass ht htx hsupply hB' (Nat.ceil_le.mp hcount), hmem⟩

end AbcSubexp.TupleCounting
