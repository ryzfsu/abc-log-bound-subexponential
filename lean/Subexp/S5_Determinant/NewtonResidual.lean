/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.NewtonInterpolation

/-!
# Multivariate Newton expansion at a contact prime

The transverse character has a Newton expansion with one power of the contact
prime for each unit of excess degree. An axial principal unit of depth `n`
preserves the residual divisibility after the terms of degree below `n` are removed.

## Main results

* `AbcSubexp.mixedNewtonExpansion`
* `AbcSubexp.principalCharacterNewtonExpansion`
* `AbcSubexp.principalCharacterCoefficient_dvd`
* `AbcSubexp.principalCharacterResidual_dvd`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The tensor product of the one-coordinate Newton coefficients at cutoff `D`. -/
def mixedNewtonCoefficient (D : ℕ) (g : ι → R) (b ν : ι → ℕ) : R :=
  ∏ i, ∑ j ∈ Finset.range D, (g i - 1) ^ j *
    (AbcTwoNinths.Basic.newtonCoefficient (fun z => (z.choose (b i) : ℤ) * (z.choose j : ℤ)) (ν i) : R)

/-- The product binomial evaluated at a nonnegative transverse node. -/
def transverseBinomial (y ν : ι → ℕ) : R := ∏ i, ((y i).choose (ν i) : R)

/-- On a finite box containing the node, the tensor expansion is exact. -/
theorem mixedNewtonExpansion [DecidableEq ι] (D : ℕ) (g : ι → R) (b y : ι → ℕ)
    (hy : ∀ i, y i < D) :
    (∏ i, g i ^ y i) * transverseBinomial y b =
      ∑ ν : ι → Fin D, mixedNewtonCoefficient D g b (fun i => ν i) *
        transverseBinomial y (fun i => ν i) := by
  classical
  unfold transverseBinomial mixedNewtonCoefficient
  rw [← Finset.prod_mul_distrib]
  have hone (i : ι) : g i ^ y i * ((y i).choose (b i) : R) =
      ∑ k : Fin D, (∑ j ∈ Finset.range D, (g i - 1) ^ j *
        (AbcTwoNinths.Basic.newtonCoefficient (fun z => (z.choose (b i) : ℤ) * (z.choose j : ℤ)) k : R)) *
        ((y i).choose k : R) := by
    have h := AbcTwoNinths.Basic.weightedNewtonExpansion (g i) 1 (b i) 1 (y i) D D (hy i) (by simp [hy i])
    rw [← Fin.sum_univ_eq_sum_range] at h
    rw [mul_comm]
    simpa only [one_mul] using h
  simp_rw [hone]
  rw [Fintype.prod_sum]
  simp_rw [Finset.prod_mul_distrib]

/-- Each coordinate contributes its excess above the polynomial row degree. -/
theorem mixedNewtonCoefficient_dvd (D : ℕ) (p : R) (g : ι → R) (b ν : ι → ℕ)
    (hg : ∀ i, p ∣ g i - 1) :
    p ^ (∑ i, (ν i - b i)) ∣ mixedNewtonCoefficient D g b ν := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  simpa using AbcTwoNinths.Basic.newtonWeightedDvd p (g i) (hg i) 1 (b i) 1 (ν i) D

/-- Including the axial binomial expansion gives the full Newton coefficients
of the principal character times the polynomial row. -/
theorem principalCharacterNewtonExpansion [DecidableEq ι] (D : ℕ) (g₀ : R) (g : ι → R)
    (b : ι → ℕ) (a : ℕ) (y : ι → ℕ) (hy : ∀ i, y i < D) :
    g₀ ^ a * ((∏ i, g i ^ y i) * transverseBinomial y b) =
      ∑ μ ∈ Finset.range (a + 1), ∑ ν : ι → Fin D,
        ((g₀ - 1) ^ μ * mixedNewtonCoefficient D g b (fun i => ν i)) *
          ((a.choose μ : R) * transverseBinomial y (fun i => ν i)) := by
  classical
  have haxis := add_pow (g₀ - 1) (1 : R) a
  simp only [sub_add_cancel, one_pow, mul_one] at haxis
  rw [haxis, mixedNewtonExpansion D g b y hy, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- The complete axial and transverse coefficient has its weighted prime-power factor. -/
theorem principalCharacterCoefficient_dvd (D n μ : ℕ) (p g₀ : R) (g : ι → R)
    (b ν : ι → ℕ) (hg₀ : p ^ n ∣ g₀ - 1) (hg : ∀ i, p ∣ g i - 1) :
    p ^ (n * μ + ∑ i, (ν i - b i)) ∣
      (g₀ - 1) ^ μ * mixedNewtonCoefficient D g b ν := by
  rw [pow_add, pow_mul]
  exact mul_dvd_mul (pow_dvd_pow_of_dvd hg₀ μ) (mixedNewtonCoefficient_dvd D p g b ν hg)

/-- Subtracting one common low-degree combination from the character row leaves
an entry divisible by the prime to the depth difference. -/
theorem principalCharacterResidual_dvd [DecidableEq ι] (D n : ℕ) (p g₀ : R) (g : ι → R)
    (b : ι → ℕ) (hg₀ : p ^ n ∣ g₀ - 1) (hg : ∀ i, p ∣ g i - 1)
    (a : ℕ) (y : ι → ℕ) (hy : ∀ i, y i < D) :
    p ^ (n - ∑ i, b i) ∣
      g₀ ^ a * ((∏ i, g i ^ y i) * transverseBinomial y b) -
        ∑ ν : ι → Fin D with (∑ i, (ν i : ℕ)) < n,
          mixedNewtonCoefficient D g b (fun i => ν i) * transverseBinomial y (fun i => ν i) := by
  classical
  let term (ν : ι → Fin D) := mixedNewtonCoefficient D g b (fun i => ν i) *
    transverseBinomial y (fun i => ν i)
  let row := (∏ i, g i ^ y i) * transverseBinomial y b
  have hsplit : row = (∑ ν : ι → Fin D with (∑ i, (ν i : ℕ)) < n, term ν) +
      ∑ ν : ι → Fin D with ¬ (∑ i, (ν i : ℕ)) < n, term ν := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact mixedNewtonExpansion D g b y hy
  have htail : p ^ (n - ∑ i, b i) ∣
      ∑ ν : ι → Fin D with ¬ (∑ i, (ν i : ℕ)) < n, term ν := by
    apply Finset.dvd_sum
    intro ν hν
    have hdeg : n ≤ ∑ i, (ν i : ℕ) := by simpa using (Finset.mem_filter.mp hν).2
    have hadd : (∑ i, (ν i : ℕ)) ≤ (∑ i, ((ν i : ℕ) - b i)) + ∑ i, b i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by omega
    exact (pow_dvd_pow p (show n - ∑ i, b i ≤ ∑ i, ((ν i : ℕ) - b i) by omega)).trans
      ((mixedNewtonCoefficient_dvd D p g b (fun i => ν i) hg).trans (dvd_mul_right _ _))
  have hax : p ^ (n - ∑ i, b i) ∣ g₀ ^ a - 1 :=
    (pow_dvd_pow p (Nat.sub_le ..)).trans (hg₀.trans (by simpa using sub_dvd_pow_sub_pow g₀ 1 a))
  change _ ∣ g₀ ^ a * row - _
  have heq : g₀ ^ a * row - (∑ ν : ι → Fin D with (∑ i, (ν i : ℕ)) < n, term ν) =
      (g₀ ^ a - 1) * row + ∑ ν : ι → Fin D with ¬ (∑ i, (ν i : ℕ)) < n, term ν := by
    linear_combination hsplit
  rw [show g₀ ^ a * row - _ = _ from heq]
  exact dvd_add (dvd_mul_of_dvd_left hax _) htail

end AbcSubexp
