/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ContactValuation
public import Subexp.S5_Determinant.BoxCharacter
public import Subexp.S5_Determinant.BoxLocalBudget
public import Subexp.S5_Determinant.RationalLogProduct

/-!
# Infinite-place cost of the box columns

Each auxiliary generator has two fresh valuations of opposite signs.
Their contribution at infinity is bounded by the logarithm of the ratio
of the endpoints in the auxiliary-prime interval.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

private theorem abs_sub_log_le_log_three (x y M : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxl : M/3 < x) (hxu : x ≤ M) (hyl : M/3 < y) (hyu : y ≤ M) :
    |log x - log y| ≤ log 3 := by
  have hxy : x ≤ 3*y := by linarith
  have hyx : y ≤ 3*x := by linarith
  have h₁ := log_le_log hx hxy
  have h₂ := log_le_log hy hyx
  rw [log_mul (by norm_num) hy.ne'] at h₁
  rw [log_mul (by norm_num) hx.ne'] at h₂
  rw [abs_le]
  constructor <;> linarith

/-- The signed difference of the logarithms of old and fresh contributions
to one projected generator costs its old projection plus `log 3`. -/
theorem HittingPrime.real_generator_projection (q : HittingPrime g) (i : Fin (dimension ε)) :
    |log |(g.unit q.listIndex i : ℝ)| - g.slope q.listIndex i * (log |(c.source : ℝ)|)| ≤
      t.thirdLogRadical / log t.thirdLogRadical + log 3 := by
  classical
  let f := g.prime q.listIndex i
  let v := g.unit q.listIndex i
  let R := t.radical.primeFactors
  let S := insert f (insert g.anchor R)
  let l := g.slope q.listIndex i
  let pr (p : ℕ) := ((padicValRat p v : ℝ) - l * padicValRat p c.source) * log (p : ℝ)
  have hr : t.radical ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hnos (p : ℕ) (hp : p.Prime) (h : p ∉ R) : ¬ p ∣ t.radical :=
    fun hd => h (Nat.mem_primeFactors.mpr ⟨hp, hd, hr⟩)
  have hs : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact g.prime_isPrime _ _
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact g.anchor_prime
    exact Nat.prime_of_mem_primeFactors hp
  have hsv : ∀ p, p.Prime → p ∉ S → padicValRat p v = 0 := by
    intro p hp hn
    simp only [S, Finset.mem_insert, not_or] at hn
    exact g.valuation_eq_zero_outside_support _ _ hp (hnos p hp hn.2.2) hn.2.1 hn.1
  have hx := log_abs_rat_eq_sum_padicValRat c.source_principal.1 R
    (fun _ => Nat.prime_of_mem_primeFactors)
    (fun p hp hn => c.valuation_eq_zero_of_fresh hp (hnos p hp hn))
  have hv := log_abs_rat_eq_sum_padicValRat (g.unit_principal q.listIndex i).1 S hs hsv
  have hfnot : f ∉ insert g.anchor R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨g.prime_ne_anchor _ _, fun h => g.prime_fresh _ _ (Nat.dvd_of_mem_primeFactors h)⟩
  have hanot : g.anchor ∉ R := fun h => g.anchor_fresh (Nat.dvd_of_mem_primeFactors h)
  simp only [S, Finset.sum_insert hfnot, Finset.sum_insert hanot, f,
    g.unit_fresh, g.unit_anchor] at hv
  have he : log |(v : ℝ)| - l * log |(c.source : ℝ)| =
      (log (f : ℝ) - log (g.anchor : ℝ)) + ∑ p ∈ R, pr p := by
    rw [hv, hx]
    simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul, pr, sub_mul,
      Finset.sum_sub_distrib, f, v]
    ring_nf
    simp only [mul_assoc, Finset.mul_sum]
  have hsum : ∑ p ∈ R, |pr p| ≤ t.thirdLogRadical / log t.thirdLogRadical := by
    simpa only [pr, l, v, R, oldProjection, oldAxial, abs_mul, abs_of_nonneg (log_natCast_nonneg _)]
      using oldProjection_sum q i
  have hratio := abs_sub_log_le_log_three (f : ℝ) (g.anchor : ℝ) c.cutoff
    (by exact_mod_cast (g.prime_isPrime _ _).pos) (by exact_mod_cast g.anchor_prime.pos)
    (g.primes_in_window _ _).1 (g.primes_in_window _ _).2 g.anchor_in_window.1 g.anchor_in_window.2
  change |log |(v : ℝ)| - l * (log |(c.source : ℝ)|)| ≤ _
  rw [he]
  exact (abs_add_le ..).trans ((add_le_add hratio
    ((Finset.abs_sum_le_sum_abs _ _).trans hsum)).trans_eq (add_comm _ _))

/-- The logarithm of the real character is linear in the axial and transverse coordinates. -/
theorem HittingPrime.log_character (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    log |(q.character a y : ℝ)| = (a : ℝ) * log |(c.source : ℝ)| +
      ∑ i, (y i : ℝ) * log |(g.unit q.listIndex i : ℝ)| := by
  have hx : (c.source : ℝ) ≠ 0 := by exact_mod_cast c.source_principal.1
  have hu (i : Fin (dimension ε)) : (g.unit q.listIndex i : ℝ) ≠ 0 := by
    exact_mod_cast (g.unit_principal _ i).1
  simp only [character, Rat.cast_mul, Rat.cast_zpow, Rat.cast_prod, log_abs,
    log_mul (zpow_ne_zero _ hx) (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hu i)),
    log_prod (fun i _ => zpow_ne_zero (y i) (hu i)), log_zpow]

/-- Uniform infinite-place cost of the actual base columns. -/
theorem real_box_budget {I : Type*} [Fintype I] [Nonempty I] (q : HittingPrime g)
    (a : I → ℤ) (y : I → Fin (dimension ε) → ℤ) (hbox : ∀ j, q.box (a j) (y j))
    (ht : 0 < log c.cutoff) (hb : 0 ≤ c.transverseBudget) :
    minorRealBudget (fun j => q.character (a j) (y j)) ≤
      c.width / 2 * (exponent ε / 50 * AbcTwoNinths.Basic.rationalHeight c.source) +
      (dimension ε : ℝ)^2 * c.transverseBudget / log c.cutoff * (t.thirdLogRadical / log t.thirdLogRadical + log 3) := by
  classical
  apply Finset.sup'_le
  intro j _
  have hwidth : 0 ≤ c.width / 2 := (abs_nonneg _).trans (hbox j).1
  have hsep := shearedBound q (hbox j) ht (log |(c.source : ℝ)|)
    (fun i => log |(g.unit q.listIndex i : ℝ)|)
  rw [q.log_character]
  refine (le_abs_self _).trans (hsep.trans ?_)
  refine add_le_add (mul_le_mul_of_nonneg_left c.real_contact hwidth) ?_
  have hk : 0 ≤ (dimension ε : ℝ) * c.transverseBudget / log c.cutoff := by positivity
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => q.real_generator_projection i) hk).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end AbcSubexp
