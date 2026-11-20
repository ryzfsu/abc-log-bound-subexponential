/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ThirdWindow
public import Subexp.S4_TupleCounting.AuxiliaryPrimeCutoff
public import AbcTwoNinths.Paper.S4_ExteriorE2.PrimeSupply

/-!
# Fresh primes below the auxiliary cutoff

The third-window Chebyshev estimate leaves a positive proportion of the window
after deleting the prime factors of twice the radical in Section 4.

## Main results
* `AbcSubexp.TupleCounting.eventually_auxiliaryFreshPrimes_card`
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real Filter

/-- The primes of the real third-window that do not divide twice the radical. -/
noncomputable def auxiliaryFreshPrimes (R : ℕ) (M : ℝ) : Finset ℕ :=
  thirdWindowPrimes ⌊M⌋₊ \ (2 * R).primeFactors

/-- Membership in the auxiliary family is exactly the prime-window and freshness conditions. -/
theorem mem_auxiliaryFreshPrimes {R q : ℕ} (hR : 0 < R) {M : ℝ} (hM : 0 ≤ M) :
    q ∈ auxiliaryFreshPrimes R M ↔
      q.Prime ∧ M / 3 < q ∧ (q : ℝ) ≤ M ∧ ¬q ∣ 2 * R := by
  rw [auxiliaryFreshPrimes, Finset.mem_sdiff, mem_thirdWindowPrimes]
  have hn : 2 * R ≠ 0 := by positivity
  have hlo : ⌊M⌋₊ < 3 * q ↔ M / 3 < (q : ℝ) := by
    rw [Nat.floor_lt hM, div_lt_iff₀ (by norm_num : (0 : ℝ) < 3), Nat.cast_mul,
      Nat.cast_ofNat, mul_comm (q : ℝ)]
  simp only [hlo, Nat.le_floor_iff hM, Nat.mem_primeFactors]
  tauto

private theorem eventually_freshThirdWindow {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (R : ℕ) (M : ℝ), 0 < R → log R = 3*x →
      0 < M → b*x ≤ log M → log M ≤ x →
      M / (8 * log M) ≤ ((auxiliaryFreshPrimes R M).card : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_thirdWindow_card
  have hg := (tendsto_exp_mul_div_rpow_atTop 2 b hb).eventually_ge_atTop 168
  have hlim := ((tendsto_const_mul_atTop_of_pos hb).2 tendsto_id).eventually_ge_atTop
    ((max N 6 : ℕ) : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hg, hlim] with x hx hg' hxN
  intro R M hR hlogR hM hlo hhi
  have hx0 : 0 < x := by linarith
  have ht : 0 < log M := (mul_pos hb hx0).trans_le hlo
  have hNat : max N 6 ≤ ⌊M⌋₊ := by
    apply Nat.le_floor
    exact hxN.trans (hlo.trans (by linarith [log_le_sub_one_of_pos hM]))
  let X := ⌊M⌋₊
  have hX : 6 ≤ X := (le_max_right _ _).trans hNat
  have hX' : (6 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXM : (X : ℝ) ≤ M := Nat.floor_le hM.le
  have hMX : M ≤ (6 / 5 : ℝ) * X := by
    have h := Nat.lt_floor_add_one M
    change M < (X : ℝ) + 1 at h
    linarith
  have hLogX : 0 < log (X : ℝ) := log_pos (by linarith)
  have hW := (div_lt_iff₀ (mul_pos (by norm_num) hLogX)).1
    (hN X ((le_max_left _ _).trans hNat))
  have hscaled := mul_le_mul_of_nonneg_left (log_le_log hXpos hXM)
    (Nat.cast_nonneg (thirdWindowPrimes X).card : (0 : ℝ) ≤ _)
  have hw : M ≤ ((thirdWindowPrimes X).card : ℝ) * (6 * log M) := by
    linarith only [hMX, hW, hscaled]
  have hOld := AbcTwoNinths.ExteriorE2.oldPrimeBudget hR hlogR
  have hOldMass : ((2*R).primeFactors.card : ℝ) * (24 * log M) ≤ M := by
    have hExp := Real.exp_le_exp.mpr hlo
    rw [exp_log hM] at hExp
    change 168 ≤ exp (b*x) / x ^ (2 : ℝ) at hg'
    rw [Real.rpow_two, le_div_iff₀ (sq_pos_of_pos hx0)] at hg'
    calc
      _ ≤ (1+6*x) * (24*x) := mul_le_mul hOld (by linarith) (by positivity) (by positivity)
      _ ≤ 168 * x^2 := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx)]
      _ ≤ M := hg'.trans hExp
  have hUnion : (thirdWindowPrimes X).card ≤
      (auxiliaryFreshPrimes R M).card + (2*R).primeFactors.card := by
    exact Finset.card_le_card_sdiff_add_card
  have hUnion' : ((thirdWindowPrimes X).card : ℝ) ≤
      (auxiliaryFreshPrimes R M).card + ((2*R).primeFactors.card : ℝ) := by exact_mod_cast hUnion
  apply (div_le_iff₀ (by positivity : 0 < 8 * log M)).2
  linarith only [hw, hOldMass, mul_le_mul_of_nonneg_right hUnion' ht.le]

/-- At sufficiently large height for fixed `e`, the fresh set at the selected
cutoff contains at least `M / (8 log M)` primes. -/
theorem eventually_auxiliaryFreshPrimes_card {e : ℝ} (he : 0 < e) (heCap : e ≤ 1/10) :
    ∀ᶠ x : ℝ in atTop, ∀ (R : ℕ) (p h : ℝ), 0 < R → log R = 3*x → 0 < p →
      (2.94*e)*x < log p → log p ≤ x → (e/2)*exp (3*e*x) ≤ h →
      let M := auxiliaryPrimeCutoff e x p h
      M / (8*log M) ≤ ((auxiliaryFreshPrimes R M).card : ℝ) := by
  filter_upwards [eventually_freshThirdWindow (b := e^2/10) (by positivity),
    ((tendsto_const_mul_atTop_of_pos (sq_pos_of_pos he)).2 tendsto_id).eventually_ge_atTop 20]
    with x htail hon
  intro R p h hR hlogR hp hcontact hup hh
  have hb := auxiliaryPrimeCutoffBounds he heCap hp hon hcontact hup hh
  have hM : 0 < auxiliaryPrimeCutoff e x p h := mul_pos (exp_pos _)
    ((Real.rpow_pos_of_pos hp _).trans_le (le_max_left _ _))
  exact htail R _ hR hlogR hM hb.2.2.2.1 hb.2.2.2.2.1

end AbcSubexp.TupleCounting
