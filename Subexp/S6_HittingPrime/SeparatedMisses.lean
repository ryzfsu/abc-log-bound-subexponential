/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.JointFrequencies
public import Subexp.S6_HittingPrime.JointSelection

/-!
# The miss count for separated frequencies

In Section 6, separation of the bounded nonzero integer combinations of the
slopes controls the nonconstant character sums in the joint miss count.
-/

@[expose] public section

open Finset Real
open scoped BigOperators

namespace AbcSubexp

open CosineSpectrum

/-- The actual open-box test on all coordinates of a single row. -/
def rowPhaseHit {m s : ℕ} (x : Fin s → Fin m → ℝ) (center : Fin m → ℝ) (η : ℝ)
    (v : ℕ) (b : Fin s) : Prop :=
  ∀ i, |(v : ℝ) * x b i - center i - (round ((v : ℝ) * x b i - center i) : ℝ)| < η

/-- Nonzero bounded integer combinations of the actual slopes suffice to bound
all integer times at which the prescribed open box misses every row. -/
theorem separated_missedTimes_card_le {m s : ℕ} (F X : ℕ)
    (x : Fin s → Fin m → ℝ) (center : Fin m → ℝ) {η δ : ℝ}
    (hη : 0 ≤ η) (hδ : 0 < δ)
    (hsmall : (cos (π * η) ^ 2) ^ F ≤ ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2)
    (hsep : ∀ y : Fin s → Fin m → ℤ, y ≠ 0 → (∑ b, ∑ i, (y b i).natAbs) ≤ s * m * F →
      δ ≤ |(∑ b, ∑ i, (y b i : ℝ) * x b i) - round (∑ b, ∑ i, (y b i : ℝ) * x b i)|) :
    ((missedTimes X (rowPhaseHit x center η)).card : ℝ) ≤
      X * (1 - ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2) ^ s + 3 ^ s * (1 / (2 * δ)) := by
  classical
  let U (b : Fin s) (v : ℕ) := cosineMissMajorant η F (fun i => (v : ℝ) * x b i - center i)
  let E := missedTimes X (rowPhaseHit x center η)
  have hsub : E ⊆ thirdWindowTimes X := filter_subset ..
  have hmiss (v : ℕ) (hv : v ∈ E) (b : Fin s) : 1 ≤ U b v := by
    apply one_le_cosineMissMajorant_of_miss hη
    have hm : ¬rowPhaseHit x center η v b := (mem_filter.mp hv).2 b
    simpa only [rowPhaseHit, not_forall, not_lt] using hm
  have hρ : (cos (π * η) ^ 2) ^ F ≤ 1 := by
    apply pow_le_one₀ (sq_nonneg _) _
    exact (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨neg_one_le_cos _, cos_le_one _⟩)
  have hbound := all_rows_miss_card_le (thirdWindowTimes X) E hsub U
    (fun _ => coefficient η F center) (fun b => node F (x b)) (by positivity : 0 ≤ 1 / (2 * δ))
    (fun b v => cosineMissMajorant_nonneg η F _) hmiss (fun i v _ => expansion η F center (x i) v)
    (fun b => node_zero F (x b)) (fun _ => constant_norm_le η F center hsmall)
    (fun _ => mass_le_three η F center hρ)
    (fun k hk => productNode_Ico_norm_le F x hδ hsep
      (Nat.add_le_add_right (Nat.div_le_self X 3) 1) k hk)
  have ha₁ : 1 ≤ (2 * (F : ℝ) + 1) ^ m := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) F])
  have ha₂ : ((2 * (F : ℝ) + 1) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha₁
  have ha : 0 ≤ 1 - ((2 * (F : ℝ) + 1) ^ m)⁻¹ / 2 := by linarith
  have hI : (thirdWindowTimes X).card ≤ X := by simp [thirdWindowTimes]
  exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hI) (pow_nonneg ha s)) (le_refl _))

end AbcSubexp
