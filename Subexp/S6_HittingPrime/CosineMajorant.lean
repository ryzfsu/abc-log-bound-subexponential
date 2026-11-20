/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The cosine majorant for a missed box

An even cosine power is sharply concentrated near the integers. Taking the product
over the centered coordinates gives a majorant for the indicator of a missed box.

## Main results
* `AbcSubexp.cosineMissMajorant_nonneg`
* `AbcSubexp.one_le_cosineMissMajorant_of_miss`
* `AbcSubexp.exists_cosineDegree`
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace AbcSubexp

/-- The product of the even cosine powers of the centered phases. -/
noncomputable def cosineKernel {m : ℕ} (F : ℕ) (z : Fin m → ℝ) : ℝ :=
  ∏ i, Real.cos (Real.pi * z i) ^ (2 * F)

/-- The trigonometric majorant for the complement of the open box of radius `η`. -/
noncomputable def cosineMissMajorant {m : ℕ} (η : ℝ) (F : ℕ) (z : Fin m → ℝ) : ℝ :=
  1 + (Real.cos (Real.pi * η) ^ 2) ^ F - cosineKernel F z

private theorem cosine_sq_le_one (x : ℝ) : Real.cos x ^ 2 ≤ 1 := by
  nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]

private theorem cosine_power_nonneg (x : ℝ) (F : ℕ) : 0 ≤ Real.cos x ^ (2 * F) := by
  rw [pow_mul]
  positivity

private theorem cosine_power_le_one (x : ℝ) (F : ℕ) : Real.cos x ^ (2 * F) ≤ 1 := by
  rw [pow_mul]
  exact pow_le_one₀ (sq_nonneg _) (cosine_sq_le_one _)

/-- The cosine kernel is nonnegative. -/
theorem cosineKernel_nonneg {m : ℕ} (F : ℕ) (z : Fin m → ℝ) : 0 ≤ cosineKernel F z := by
  unfold cosineKernel
  exact Finset.prod_nonneg fun i _ => cosine_power_nonneg (Real.pi * z i) F

/-- The cosine kernel is bounded above by one. -/
theorem cosineKernel_le_one {m : ℕ} (F : ℕ) (z : Fin m → ℝ) : cosineKernel F z ≤ 1 := by
  unfold cosineKernel
  exact Finset.prod_le_one₀ (fun i _ => cosine_power_nonneg (Real.pi * z i) F)
    (fun i _ => cosine_power_le_one (Real.pi * z i) F)

/-- The missed-box majorant is nonnegative for every phase vector. -/
theorem cosineMissMajorant_nonneg {m : ℕ} (η : ℝ) (F : ℕ) (z : Fin m → ℝ) :
    0 ≤ cosineMissMajorant η F z := by
  unfold cosineMissMajorant
  have htail : 0 ≤ (Real.cos (Real.pi * η) ^ 2) ^ F := by positivity
  linarith [cosineKernel_le_one F z]

private theorem abs_cos_pi_mul_sub_int (x : ℝ) (n : ℤ) :
    |Real.cos (Real.pi * (x - (n : ℝ)))| = |Real.cos (Real.pi * x)| := by
  rw [mul_sub, mul_comm Real.pi (n : ℝ), Real.cos_sub_int_mul_pi, abs_mul, abs_zpow]
  simp

private theorem cosine_sq_le_of_miss {η x : ℝ} (hη : 0 ≤ η)
    (hmiss : η ≤ |x - (round x : ℝ)|) :
    Real.cos (Real.pi * x) ^ 2 ≤ Real.cos (Real.pi * η) ^ 2 := by
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1 / 2 := abs_sub_round x
  have hlow : 0 ≤ Real.pi * |y| := by positivity
  have hhigh : Real.pi * |y| ≤ Real.pi / 2 := by
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hy Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hηy : Real.pi * η ≤ Real.pi * |y| := mul_le_mul_of_nonneg_left hmiss Real.pi_pos.le
  have hc_nonneg : 0 ≤ Real.cos (Real.pi * |y|) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hlow], hhigh⟩
  have hc_le : Real.cos (Real.pi * |y|) ≤ Real.cos (Real.pi * η) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hη)
      (hhigh.trans (by linarith [Real.pi_pos])) hηy
  have hc_abs : |Real.cos (Real.pi * x)| = Real.cos (Real.pi * |y|) := by
    rw [← abs_cos_pi_mul_sub_int x (round x)]
    change |Real.cos (Real.pi * y)| = Real.cos (Real.pi * |y|)
    calc
      |Real.cos (Real.pi * y)| = |Real.cos (|Real.pi * y|)| := by rw [Real.cos_abs]
      _ = Real.cos (Real.pi * |y|) := by
        rw [abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hc_nonneg]
  rw [← sq_abs (Real.cos (Real.pi * x)), hc_abs]
  exact pow_le_pow_left₀ hc_nonneg hc_le 2

/-- If one coordinate misses the open box, the majorant is at least one. -/
theorem one_le_cosineMissMajorant_of_miss {m : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (F : ℕ) (z : Fin m → ℝ) (hmiss : ∃ i, η ≤ |z i - (round (z i) : ℝ)|) :
    1 ≤ cosineMissMajorant η F z := by
  classical
  obtain ⟨i, hi⟩ := hmiss
  have hkernel : cosineKernel F z ≤ (Real.cos (Real.pi * η) ^ 2) ^ F := by
    unfold cosineKernel
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc
      _ ≤ Real.cos (Real.pi * z i) ^ (2 * F) * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun j _ => cosine_power_nonneg (Real.pi * z j) F)
            (fun j _ => cosine_power_le_one (Real.pi * z j) F))
          (cosine_power_nonneg (Real.pi * z i) F)
      _ ≤ (Real.cos (Real.pi * η) ^ 2) ^ F := by
        rw [mul_one, pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _) (cosine_sq_le_of_miss hη hi) F
  unfold cosineMissMajorant
  linarith

/-- A positive degree makes the missed-box tail smaller than half the lower bound
for the constant Fourier coefficient. -/
theorem exists_cosineDegree (m : ℕ) {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    ∃ F : ℕ, 0 < F ∧ (Real.cos (Real.pi * η) ^ 2) ^ F <
      (((2 * (F : ℝ) + 1) ^ m)⁻¹) / 2 := by
  let ρ := Real.cos (Real.pi * η) ^ 2
  have hρ0 : 0 ≤ ρ := sq_nonneg _
  have hang0 : 0 < Real.pi * η := mul_pos Real.pi_pos hη
  have hang1 : Real.pi * η ≤ Real.pi / 2 := by
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hη'.le Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hc0 : 0 ≤ Real.cos (Real.pi * η) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hang1⟩
  have hc1 : Real.cos (Real.pi * η) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hang1 hang0
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    nlinarith [mul_pos (sub_pos.mpr hc1) (by linarith : 0 < 1 + Real.cos (Real.pi * η))]
  have hlim : Tendsto (fun F : ℕ => (3 : ℝ) ^ m * ((F : ℝ) ^ m * ρ ^ F))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one m hρ0 hρ1).const_mul
      ((3 : ℝ) ^ m)
  have hevent : ∀ᶠ F : ℕ in atTop, (3 : ℝ) ^ m * ((F : ℝ) ^ m * ρ ^ F) < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨F, hF, hsmall⟩ := (eventually_ge_atTop (1 : ℕ)).and hevent |>.exists
  have hFreal : (1 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
  have hbase : 0 < ((2 * (F : ℝ) + 1) ^ m) := by positivity
  have hpower : (2 * (F : ℝ) + 1) ^ m ≤ (3 * (F : ℝ)) ^ m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  refine ⟨F, Nat.succ_le_iff.mp hF, ?_⟩
  change ρ ^ F < (((2 * (F : ℝ) + 1) ^ m)⁻¹) / 2
  rw [inv_eq_one_div, div_right_comm, lt_div_iff₀ hbase]
  calc
    ρ ^ F * (2 * (F : ℝ) + 1) ^ m ≤ ρ ^ F * (3 * (F : ℝ)) ^ m :=
      mul_le_mul_of_nonneg_left hpower (pow_nonneg hρ0 F)
    _ = (3 : ℝ) ^ m * ((F : ℝ) ^ m * ρ ^ F) := by rw [mul_pow]; ring
    _ < 1 / 2 := hsmall

end AbcSubexp
