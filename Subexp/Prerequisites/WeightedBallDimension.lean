/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S4_ExteriorE2.WeightedVolume

/-!
# Dimension and volume of a logarithmically weighted ball

The Section 4 tuple count requires a lower bound for a ball in the coordinates
away from the distinguished prime. An inscribed cube bounds its volume, while a
split at the square root of the height parameter bounds the number of coordinates.
-/

@[expose] public section

open MeasureTheory Set AbcTwoNinths.ExteriorE2
open scoped ENNReal

namespace AbcSubexp.Prerequisites

/-- The open cube of half-width `r / s` lies in the weighted ball when the weights sum to at most `s`. -/
theorem weightedBallVolumeLower {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hbudget : ∑ i, w i ≤ s) (c : ι → ℝ) :
    ENNReal.ofReal ((2*r/s) ^ Fintype.card ι) ≤
      volume {a : ι → ℝ | ∑ i, w i * |a i - c i| < r} := by
  classical
  let d := r / s
  have hd : 0 < d := div_pos hr hs
  have hsub : (Set.pi univ (fun i => Ioo (c i - d) (c i + d))) ⊆
      {a : ι → ℝ | ∑ i, w i * |a i - c i| < r} := by
    intro a ha
    change (∑ i, w i * |a i - c i|) < r
    by_cases he : ∀ i, w i = 0
    · simpa [he] using hr
    · push Not at he
      obtain ⟨j, hj⟩ := he
      have habs (i : ι) : |a i - c i| < d := by
        have hmem := ha i (mem_univ i)
        exact abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      have hsum : (∑ i, w i * |a i - c i|) < ∑ i, w i * d :=
        Finset.sum_lt_sum
          (fun i _ => mul_le_mul_of_nonneg_left (habs i).le (hw i))
          ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (habs j) (lt_of_le_of_ne (hw j) hj.symm)⟩
      calc
        _ < (∑ i, w i * d) := hsum
        _ = (∑ i, w i) * d := (Finset.sum_mul _ _ _).symm
        _ ≤ s * d := mul_le_mul_of_nonneg_right hbudget hd.le
        _ = r := by dsimp [d]; field_simp
  have hvol := measure_mono (μ := (volume : Measure (ι → ℝ))) hsub
  rw [Real.volume_pi_Ioo] at hvol
  have hside (i : ι) : c i + d - (c i - d) = 2*r/s := by
    dsimp [d]
    ring
  simp_rw [hside, Finset.prod_const, Finset.card_univ] at hvol
  rw [← ENNReal.ofReal_pow (show 0 ≤ 2*r/s by positivity)] at hvol
  exact hvol

/-- The logarithmic weight budget `3 * x` gives a cube of side length `α / 3`. -/
theorem sourceWeightedBallVolumeLower {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {α x : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hb : ∑ i, w i ≤ 3*x) (c : ι → ℝ) :
    ENNReal.ofReal ((α/3) ^ Fintype.card ι) ≤
      volume {a : ι → ℝ | ∑ i, w i * |a i - c i| < α*x/2} := by
  have h := weightedBallVolumeLower w hw (r := α*x/2) (s := 3*x)
    (by positivity) (by positivity) hb c
  have he : 2*(α*x/2)/(3*x) = α/3 := by field_simp
  simpa only [he] using h

/-- The projected ball in ordinary exponent coordinates, centered at `c`. -/
def smallBall (S : Finset ℕ) (roof : ℕ) (α x : ℝ) (c : OldIndex S roof → ℝ) :
    Set (OldIndex S roof → ℝ) :=
  {a | ∑ i, Real.log (i.val : ℝ) * |a i - c i| < α*x/2}

/-- The cube volume bound in prime coordinates with logarithmic weights. -/
theorem smallBall_volume_lower (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) {R : ℕ} (hprod : ∏ q ∈ S, q ≤ R)
    {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (hR : Real.log (R : ℝ) = 3*x)
    (c : OldIndex S roof → ℝ) :
    ENNReal.ofReal ((α/3) ^ Fintype.card (OldIndex S roof)) ≤
      volume (smallBall S roof α x c) := by
  apply sourceWeightedBallVolumeLower (fun i : OldIndex S roof => Real.log (i.val : ℝ)) _
    hα hx (oldLogBudget S roof hS hprod hR) c
  intro i
  exact Real.log_nonneg (by exact_mod_cast (hS i.val (Finset.mem_erase.mp i.property).2).one_lt.le)

/-- Positive prime log weights bound each coordinate of the ball. -/
theorem smallBall_volume_lt_top (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) (α x : ℝ) (c : OldIndex S roof → ℝ) :
    volume (smallBall S roof α x c) < ⊤ := by
  let b (i : OldIndex S roof) : ℝ := α*x/2 / Real.log (i.val : ℝ)
  have hw (i : OldIndex S roof) : 0 < Real.log (i.val : ℝ) :=
    Real.log_pos (by exact_mod_cast (hS i.val (Finset.mem_erase.mp i.property).2).one_lt)
  have hsub : smallBall S roof α x c ⊆ Set.Icc (c - b) (c + b) := by
    intro a ha
    change (∑ i, Real.log (i.val : ℝ) * |a i - c i|) < α*x/2 at ha
    have hb (i : OldIndex S roof) : |a i - c i| < b i := by
      have hi : Real.log (i.val : ℝ) * |a i - c i| ≤
          ∑ j, Real.log (j.val : ℝ) * |a j - c j| :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (abs_nonneg (a j - c j)))
          (Finset.mem_univ i)
      exact (lt_div_iff₀ (hw i)).2 (by simpa only [mul_comm] using hi.trans_lt ha)
    exact ⟨fun i => by simpa using (abs_lt.mp (hb i)).1.le,
           fun i => by simpa [add_comm] using (abs_lt.mp (hb i)).2.le⟩
  exact (measure_mono hsub).trans_lt measure_Icc_lt_top

/-- Real-valued form of the cube volume estimate. -/
theorem smallBall_real_lower (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) {R : ℕ} (hprod : ∏ q ∈ S, q ≤ R)
    {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (hR : Real.log (R : ℝ) = 3*x)
    (c : OldIndex S roof → ℝ) :
    (α/3) ^ Fintype.card (OldIndex S roof) ≤
      (volume : Measure (OldIndex S roof → ℝ)).real (smallBall S roof α x c) := by
  rw [measureReal_def]
  rw [← ENNReal.toReal_ofReal (show 0 ≤ (α/3) ^ Fintype.card (OldIndex S roof) by positivity)]
  exact ENNReal.toReal_mono (smallBall_volume_lt_top S roof hS α x c).ne
    (smallBall_volume_lower S roof hS hprod hα hx hR c)

/-- Split at `sqrt x`: at most `sqrt x` positive integers fall below the split,
and every coordinate above it spends at least `log x / 2` of the budget. -/
theorem card_le_seven_mul_div_log (F : Finset ℕ) (hF : ∀ q ∈ F, 0 < q)
    {x : ℝ} (hx : 1 < x) (hbudget : ∑ q ∈ F, Real.log (q : ℝ) ≤ 3*x) :
    (F.card : ℝ) ≤ 7*x/Real.log x := by
  classical
  let lo := F.filter (fun q : ℕ => (q : ℝ) ≤ Real.sqrt x)
  let hi := F.filter (fun q : ℕ => ¬ (q : ℝ) ≤ Real.sqrt x)
  have hpartition : lo.card + hi.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) _
  have hlo : (lo.card : ℝ) ≤ Real.sqrt x := by
    have hcount : lo.card ≤ ⌊Real.sqrt x⌋₊ := by
      calc
        lo.card ≤ (Finset.Icc 1 ⌊Real.sqrt x⌋₊).card := Finset.card_le_card (by
          intro q hq
          obtain ⟨hqF, hq⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_Icc.mpr ⟨hF q hqF, Nat.le_floor hq⟩)
        _ = _ := by simp
    exact (show (lo.card : ℝ) ≤ ⌊Real.sqrt x⌋₊ by exact_mod_cast hcount).trans
      (Nat.floor_le (Real.sqrt_nonneg x))
  have hx0 : 0 < x := by linarith
  have hxs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hhi : (hi.card : ℝ) ≤ 6*x/Real.log x := by
    have hsumb : (∑ q ∈ hi, Real.log (q : ℝ)) ≤ ∑ q ∈ F, Real.log (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q hq _ =>
        Real.log_nonneg (by exact_mod_cast (hF q hq))
    have hh : (hi.card : ℝ) * (Real.log x / 2) ≤ ∑ q ∈ hi, Real.log (q : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro q hq
      rw [← Real.log_sqrt hx0.le]
      exact Real.log_le_log hxs (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hq).2))
    apply (le_div_iff₀ hlx).2
    linarith [hh.trans (hsumb.trans hbudget)]
  have hlog : Real.log x ≤ Real.sqrt x := by
    have ht := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 2 by positivity)
    rw [Real.log_div hxs.ne' (by norm_num), Real.log_sqrt hx0.le] at ht
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlo' : (lo.card : ℝ) ≤ x/Real.log x := by
    apply hlo.trans
    apply (le_div_iff₀ hlx).2
    nlinarith [mul_le_mul_of_nonneg_left hlog hxs.le, Real.sq_sqrt hx0.le]
  have hpart : (F.card : ℝ) = (lo.card : ℝ) + (hi.card : ℝ) := by exact_mod_cast hpartition.symm
  rw [hpart]
  calc
    _ ≤ x/Real.log x + 6*x/Real.log x := add_le_add hlo' hhi
    _ = _ := by ring

/-- At the manuscript radius parameter `1 / log x`, the same old ball has
an explicit subexponential lower bound, uniformly in the center. -/
theorem smallBall_subexponential_lower (S : Finset ℕ) (roof : ℕ)
    (hS : ∀ q ∈ S, q.Prime) {R : ℕ} (hprod : ∏ q ∈ S, q ≤ R)
    {x : ℝ} (hx : Real.exp 1 ≤ x) (hR : Real.log (R : ℝ) = 3*x)
    (c : OldIndex S roof → ℝ) :
    Real.exp (-(7*x/Real.log x) * Real.log (3*Real.log x)) ≤
      (volume : Measure (OldIndex S roof → ℝ)).real (smallBall S roof (1/Real.log x) x c) := by
  have hx' : 1 < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx'
  have hlx1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hlog3 : 0 ≤ Real.log (3*Real.log x) := Real.log_nonneg (by linarith)
  have hF : ∀ q ∈ S.erase roof, 0 < q := fun q hq => (hS q (Finset.mem_erase.mp hq).2).pos
  have hbudget : ∑ q ∈ S.erase roof, Real.log (q : ℝ) ≤ 3*x := by
    rw [← Finset.sum_coe_sort (s := S.erase roof) (f := fun q : ℕ => Real.log (q : ℝ))]
    exact oldLogBudget S roof hS hprod hR
  have hdim : (Fintype.card (OldIndex S roof) : ℝ) ≤ 7*x/Real.log x := by
    simpa only [OldIndex, Fintype.card_coe] using card_le_seven_mul_div_log _ hF hx' hbudget
  have hα : 0 < 1/Real.log x := by positivity
  refine le_trans ?_ (smallBall_real_lower S roof hS hprod hα hx0 hR c)
  have harg : 0 < (1/Real.log x)/3 := by positivity
  have heq : (1/Real.log x)/3 = (3*Real.log x)⁻¹ := by field_simp
  rw [← Real.exp_log (pow_pos harg _), Real.log_pow, heq, Real.log_inv]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hdim hlog3]

end AbcSubexp.Prerequisites
