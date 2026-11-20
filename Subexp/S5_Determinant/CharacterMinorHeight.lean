/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.LocalDepthHeightComparison
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Height of a mixed character minor

Integral rows and rows multiplied by a rational column character have a common
denominator cost proportional to the number of weighted rows. The signed
prime exponents retain common numerator factors across the selected columns.

## Main results
* `AbcSubexp.characterMinor_depth_height`
* `AbcSubexp.binomialMinor_depth_height`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators
open Real

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The selected square matrix with the character applied only on the weighted rows. -/
def characterMinor (weighted : Finset I) (A : Matrix I I ℤ) (γ : I → ℚ) : Matrix I I ℚ :=
  Matrix.of fun i j => (if i ∈ weighted then γ j else 1) * (A i j : ℚ)

private theorem integral_of_valuations (x : ℚ)
    (hx : ∀ q : ℕ, q.Prime → 0 ≤ padicValRat q x) : ∃ z : ℤ, (z : ℚ) = x := by
  have hd : x.den = 1 := by
    by_contra hn
    obtain ⟨q, hq, hdiv⟩ := Nat.exists_prime_and_dvd hn
    let : Fact q.Prime := ⟨hq⟩
    have hpos := one_le_padicValNat_of_dvd x.den_nz hdiv
    have hval := hx q hq
    rw [padicValRat_def] at hval
    rcases x.num_or_den_zero_padicVal hq with h | h <;> omega
  exact ⟨x.num, by simpa [hd] using x.num_div_den⟩

private theorem scale_pos (S : Finset ℕ) (b : ℕ → ℤ) (hS : ∀ q ∈ S, Nat.Prime q) :
    0 < ∏ q ∈ S, (q : ℚ) ^ b q :=
  Finset.prod_pos fun q hq => zpow_pos (by exact_mod_cast (hS q hq).pos) _

private theorem scale_valuation (S : Finset ℕ) (b : ℕ → ℤ)
    (hS : ∀ q ∈ S, Nat.Prime q) (p : ℕ) (hp : p.Prime) :
    padicValRat p (∏ q ∈ S, (q : ℚ) ^ b q) = if p ∈ S then b p else 0 := by
  let : Fact p.Prime := ⟨hp⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    have hprime := hS q (Finset.mem_insert_self _ _)
    have hrest (r : ℕ) (hr : r ∈ S) := hS r (Finset.mem_insert_of_mem hr)
    have hqn : (q : ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    rw [Finset.prod_insert hq, padicValRat.mul (zpow_ne_zero _ hqn)
      (scale_pos S b hrest).ne', padicValRat.zpow, ih hrest]
    by_cases heq : p = q
    · subst q
      simp [padicValRat.self hp.one_lt, hq]
    · let : Fact q.Prime := ⟨hprime⟩
      simp [heq, padicValNat_primes heq]

private theorem rowBound_det {M : Matrix I I ℝ} (B : I → ℝ)
    (hM : ∀ i j, |M i j| ≤ B i) :
    |M.det| ≤ (Fintype.card I).factorial * ∏ i, B i := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm I, |(Equiv.Perm.sign σ) • ∏ i, M (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm I, ∏ i, B i := by
      apply Finset.sum_le_sum
      intro σ _
      have hu : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      simp only [Units.smul_def, zsmul_eq_mul, abs_mul, hu, one_mul, Finset.abs_prod]
      rw [← Equiv.prod_comp σ B]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => hM (σ j) j)
    _ = _ := by simp [Fintype.card_perm]

private theorem scaled_integer_minor (weighted : Finset I) (A : Matrix I I ℤ) (γ : I → ℚ)
    (c : ℚ) (z : I → ℤ) (hz : ∀ j, (z j : ℚ) = c * γ j) :
    ∃ Z : ℤ, (Z : ℚ) = c ^ weighted.card * (characterMinor weighted A γ).det := by
  classical
  let M : Matrix I I ℤ := Matrix.of fun i j => (if i ∈ weighted then z j else 1) * A i j
  refine ⟨M.det, ?_⟩
  let v (i : I) : ℚ := if i ∈ weighted then c else 1
  have hm : M.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => v i * characterMinor weighted A γ i j) := by
    ext i j
    by_cases h : i ∈ weighted <;> simp [M, v, characterMinor, h, hz, mul_assoc]
  have hv : ∏ i, v i = c ^ weighted.card := by
    simp [v]
  calc
    (M.det : ℚ) = (M.map (Int.castRingHom ℚ)).det := (Int.castRingHom ℚ).map_det M
    _ = _ := by rw [hm, Matrix.det_mul_column, hv]

private theorem archimedean_minor (weighted : Finset I) (A : Matrix I I ℤ) (γ : I → ℚ)
    (T : ℕ) (H : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ (2 : ℝ)^T)
    (hγ : ∀ j, |(γ j : ℝ)| ≤ exp H) :
    |(((characterMinor weighted A γ).det : ℚ) : ℝ)| ≤
      (Fintype.card I).factorial * ((2 : ℝ)^T)^(Fintype.card I) * (exp H)^weighted.card := by
  classical
  let M := (characterMinor weighted A γ).map (Rat.castHom ℝ)
  let B (i : I) : ℝ := (if i ∈ weighted then exp H else 1) * 2^T
  have hb (i j : I) : |M i j| ≤ B i := by
    by_cases h : i ∈ weighted
    · simpa [M, B, characterMinor, h, abs_mul] using
        mul_le_mul (hγ j) (hA i j) (abs_nonneg _) (exp_pos H).le
    · simpa [M, B, characterMinor, h] using hA i j
  have hv : ∏ i, B i = (exp H)^weighted.card * ((2 : ℝ)^T)^(Fintype.card I) := by
    simp only [B, Finset.prod_mul_distrib]
    simp
  have hdet := (Rat.castHom ℝ).map_det (characterMinor weighted A γ)
  change (((characterMinor weighted A γ).det : ℚ) : ℝ) = M.det at hdet
  rw [hdet]
  simpa only [hv, mul_left_comm, mul_comm, mul_assoc] using rowBound_det B hb

/-- The global upper bound (12). The integer budget at a finite place can be negative.
Outside the supplied set, including the contact prime, the character is integral.
Each of the selected weighted rows pays the finite and infinite character costs once. -/
theorem characterMinor_depth_height (weighted : Finset I) (A : Matrix I I ℤ) (γ : I → ℚ)
    (p E T : ℕ) (hp : p.Prime) (S : Finset ℕ) (b : ℕ → ℤ)
    (hS : ∀ q ∈ S, Nat.Prime q) (hpS : p ∉ S)
    (hfinite : ∀ q : ℕ, q.Prime → ∀ j, -(if q ∈ S then b q else 0) ≤ padicValRat q (γ j))
    (H : ℝ) (hγ : ∀ j, |(γ j : ℝ)| ≤ exp H)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ (2 : ℝ)^T)
    (hd : (characterMinor weighted A γ).det ≠ 0)
    (hdepth : (E : ℤ) ≤ padicValRat p (characterMinor weighted A γ).det) :
    (E : ℝ) * log p ≤ (weighted.card : ℝ) * (H + ∑ q ∈ S, (b q : ℝ) * log q) +
      (Fintype.card I : ℝ) * (T * log 2 + log (Fintype.card I)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let c : ℚ := ∏ q ∈ S, (q : ℚ)^b q
  have hc : 0 < c := scale_pos S b hS
  have hclear (j : I) : ∃ z : ℤ, (z : ℚ) = c * γ j := by
    by_cases hz : γ j = 0
    · exact ⟨0, by simp [hz]⟩
    apply integral_of_valuations
    intro q hq
    let : Fact q.Prime := ⟨hq⟩
    rw [padicValRat.mul hc.ne' hz, scale_valuation S b hS q hq]
    have := hfinite q hq j
    omega
  choose z hz using hclear
  obtain ⟨Z, hZ⟩ := scaled_integer_minor weighted A γ c z hz
  have hZn : Z ≠ 0 := by
    intro h
    simp [h, hc.ne', hd] at hZ
  have hunit : padicValRat p c = 0 := by simpa [c, hpS] using scale_valuation S b hS p hp
  have hval : (E : ℤ) ≤ padicValRat p (Z : ℚ) := by
    rw [hZ, padicValRat.mul (pow_ne_zero _ hc.ne') hd, padicValRat.pow, hunit]
    simpa using hdepth
  have hlow := AbcTwoNinths.Basic.integerLogOfDepth p E hp Z hZn hval
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcast : (Z : ℝ) = (c : ℝ)^weighted.card * (((characterMinor weighted A γ).det : ℚ) : ℝ) :=
    by exact_mod_cast hZ
  let N := Fintype.card I
  have hfact : (N.factorial : ℝ) ≤ (N : ℝ)^N := by exact_mod_cast Nat.factorial_le_pow N
  have harch := archimedean_minor weighted A γ T H hA hγ
  have hupper : (Z.natAbs : ℝ) ≤
      (c : ℝ)^weighted.card * ((N : ℝ)^N * ((2 : ℝ)^T)^N * (exp H)^weighted.card) := by
    rw [Nat.cast_natAbs, Int.cast_abs, hcast, abs_mul, abs_of_pos (pow_pos hcR _)]
    apply mul_le_mul_of_nonneg_left _ (pow_pos hcR _).le
    exact harch.trans (by gcongr)
  have hcprod : (c : ℝ) = ∏ q ∈ S, (q : ℝ)^b q := by simp [c]
  have hlogc : log (c : ℝ) = ∑ q ∈ S, (b q : ℝ) * log q := by
    rw [hcprod, Real.log_prod (fun q hq =>
      zpow_ne_zero _ (by exact_mod_cast (hS q hq).ne_zero))]
    simp only [Real.log_zpow]
  have hnPow : (N : ℝ)^N ≠ 0 := by
    by_cases hN : N = 0
    · simp [hN]
    · exact pow_ne_zero _ (by exact_mod_cast hN)
  have htPow : ((2 : ℝ)^T)^N ≠ 0 := by positivity
  have hHPow : (exp H)^weighted.card ≠ 0 := by positivity
  have hzR : (0 : ℝ) < Z.natAbs := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hZn)
  have hlog := Real.log_le_log hzR hupper
  rw [Real.log_mul (pow_ne_zero _ hcR.ne') (mul_ne_zero (mul_ne_zero hnPow htPow) hHPow),
    Real.log_mul (mul_ne_zero hnPow htPow) hHPow,
    Real.log_mul hnPow htPow] at hlog
  simp only [log_pow, log_exp, hlogc] at hlog
  change _ ≤ _ + (N : ℝ) * _
  exact hlow.trans (hlog.trans_eq (by ring))

/-- Finite places other than the contact prime occurring in the selected characters. -/
def minorCharacterPrimes (p : ℕ) (γ : I → ℚ) : Finset ℕ :=
  (Finset.univ.biUnion fun j => (γ j).num.natAbs.primeFactors ∪ (γ j).den.primeFactors).erase p

/-- The largest signed denominator exponent among the selected columns. -/
noncomputable def minorPrimeBudget [Nonempty I] (γ : I → ℚ) (q : ℕ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => -padicValRat q (γ j))

/-- The largest infinite-place logarithm among the selected columns. -/
noncomputable def minorRealBudget [Nonempty I] (γ : I → ℚ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => log |(γ j : ℝ)|)

/-- The product binomial matrix in nonnegative translated transverse coordinates. -/
def transverseBinomialMatrix {m : ℕ} (degree point : I → Fin m → ℕ) : Matrix I I ℤ :=
  Matrix.of fun i j => ((∏ a, (point j a).choose (degree i a) : ℕ) : ℤ)

/-- The global determinant bound of Section 5 at nonnegative binomial nodes,
with the finite support and local maxima computed from the selected characters. -/
theorem binomialMinor_depth_height [Nonempty I] {m : ℕ} (weighted : Finset I)
    (degree point : I → Fin m → ℕ) (γ : I → ℚ) (p E T : ℕ) (hp : p.Prime)
    (hunit : ∀ j, padicValRat p (γ j) = 0) (hγ : ∀ j, γ j ≠ 0)
    (hbox : ∀ j, ∑ a, point j a ≤ T)
    (hd : (characterMinor weighted (transverseBinomialMatrix degree point) γ).det ≠ 0)
    (hdepth : (E : ℤ) ≤ padicValRat p
      (characterMinor weighted (transverseBinomialMatrix degree point) γ).det) :
    (E : ℝ) * log p ≤ (weighted.card : ℝ) * (minorRealBudget γ +
        ∑ q ∈ minorCharacterPrimes p γ, (minorPrimeBudget γ q : ℝ) * log q) +
      (Fintype.card I : ℝ) * (T * log 2 + log (Fintype.card I)) := by
  classical
  apply characterMinor_depth_height weighted _ γ p E T hp _ _ _ _ _ _ _ _ hd hdepth
  · intro q hq
    have hm := (Finset.mem_erase.mp hq).2
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hm
    exact (Finset.mem_union.mp hj).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  · exact Finset.notMem_erase _ _
  · intro q hq j
    by_cases hmem : q ∈ minorCharacterPrimes p γ
    · simpa [hmem, minorPrimeBudget] using neg_le_neg
        (Finset.le_sup' (fun i => -padicValRat q (γ i)) (Finset.mem_univ j))
    rw [ite_eq_right hmem, neg_zero]
    by_cases heq : q = p
    · simp [heq, hunit]
    have hnd : ¬q ∣ (γ j).den := by
      intro hdvd
      apply hmem
      exact Finset.mem_erase.mpr ⟨heq, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
        Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq, hdvd, (γ j).den_nz⟩)⟩⟩
    simp [padicValRat_def, padicValNat.eq_zero_of_not_dvd hnd]
  · intro j
    have hpos : 0 < |(γ j : ℝ)| := abs_pos.mpr (by exact_mod_cast hγ j)
    rw [← Real.log_le_iff_le_exp hpos]
    exact Finset.le_sup' (fun i => log |(γ i : ℝ)|) (Finset.mem_univ j)
  · intro i j
    have hh : ∏ a, (point j a).choose (degree i a) ≤ 2 ^ T := calc
      _ ≤ ∏ a, 2 ^ point j a := Finset.prod_le_prod fun a _ => Nat.choose_le_two_pow _ _
      _ = 2 ^ ∑ a, point j a := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (hbox j)
    change |(((∏ a, (point j a).choose (degree i a) : ℕ) : ℤ) : ℝ)| ≤ (2 : ℝ)^T
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hh

end AbcSubexp
