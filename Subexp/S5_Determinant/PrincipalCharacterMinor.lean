/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.NewtonResidual
public import AbcTwoNinths.Basic.LocalInterpolationMatrix
public import Subexp.Prerequisites.MinorComparison

/-!
# Local divisibility of principal-character minors

Subtracting a common combination of the low-degree rows factors a power of
the contact prime from each character row of every full-sized minor.

## Main results

* `AbcSubexp.principalCharacterMinor_dvd`
* `AbcSubexp.principalCharacterMinor_integer_dvd`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open scoped BigOperators

variable {I J ι R Col : Type*} [Fintype I] [Fintype J] [Fintype ι] [CommRing R]

/-- A single integral translation puts all the chosen nodes inside a common
nonnegative coordinate box, whose cutoff can also include the full low simplex. -/
theorem exists_commonNewtonBox [Fintype Col] (n : ℕ) (z : Col → ι → ℤ) :
    ∃ (s : ι → ℕ) (D : ℕ) (y : Col → ι → ℕ), n ≤ D ∧
      (∀ x i, (y x i : ℤ) = z x i + s i) ∧ ∀ x i, y x i < D := by
  classical
  let s (i : ι) := Finset.univ.sup fun x => (-z x i).toNat
  let y (x : Col) (i : ι) := (z x i + s i).toNat
  let bound := Finset.univ.sup fun x => Finset.univ.sup (y x)
  refine ⟨s, n + bound + 1, y, by omega, ?_, ?_⟩
  · intro x i
    have hs : (-z x i).toNat ≤ s i := Finset.le_sup (f := fun t => (-z t i).toNat) (Finset.mem_univ x)
    change ((z x i + s i).toNat : ℤ) = _
    omega
  · intro x i
    have hi : y x i ≤ Finset.univ.sup (y x) := Finset.le_sup (f := y x) (Finset.mem_univ i)
    have hx : Finset.univ.sup (y x) ≤ bound :=
      Finset.le_sup (f := fun t => Finset.univ.sup (y t)) (Finset.mem_univ x)
    omega

/-- The character of a common integral translate differs by one common unit.
The coordinates may include the axial generator. -/
theorem character_translate_eq_mul {U : Type*} [CommGroup U] (g : ι → U)
    (z s : ι → ℤ) : (∏ i, g i ^ (z i + s i)) = (∏ i, g i ^ s i) * ∏ i, g i ^ z i := by
  simp_rw [zpow_add, Finset.prod_mul_distrib]
  exact mul_comm _ _

/-- Every chosen minor preserves the product of factors in the residual rows. -/
theorem determinant_dvd_of_lowRowResiduals [DecidableEq I] [DecidableEq J] (p : R)
    (w : J → ℕ) (low : I → Col → R) (high : J → Col → R) (c : J → I → R)
    (h : ∀ j x, p ^ w j ∣ high j x - ∑ i, c j i * low i x) (sel : I ⊕ J → Col) :
    p ^ (∑ j, w j) ∣ Matrix.det (fun r s => Sum.elim low high r (sel s) : Matrix (I ⊕ J) (I ⊕ J) R) := by
  classical
  choose rem hrem using h
  let basis (u : I ⊕ J) (s : I ⊕ J) : R := Sum.elim low rem u (sel s)
  let coeff : Matrix (I ⊕ J) (I ⊕ J) R :=
    Matrix.fromBlocks 1 0 c (Matrix.diagonal fun j => p ^ w j)
  let wt : I ⊕ J → ℕ := Sum.elim (fun _ => 0) w
  have hcoeff (r u : I ⊕ J) : p ^ wt u ∣ coeff r u := by
    rcases u with i | j
    · simp [wt]
    · rcases r with i | k
      · simp [coeff, wt, Matrix.fromBlocks]
      · by_cases hk : k = j <;> simp [coeff, wt, Matrix.fromBlocks, hk]
  have hcost (f : I ⊕ J → I ⊕ J) (hf : Function.Injective f) :
      ∑ j, w j ≤ ∑ r, wt (f r) := by
    let e := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
    change _ ≤ ∑ r, wt (e r)
    rw [Equiv.sum_comp, Fintype.sum_sum_type]
    simp [wt]
  have hmat : (fun r => ∑ u, coeff r u • basis u : Matrix (I ⊕ J) (I ⊕ J) R) =
      (fun r s => Sum.elim low high r (sel s)) := by
    funext r s
    cases r with
    | inl i =>
      simp [coeff, basis, Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks, Matrix.one_apply]
    | inr j =>
      simp [coeff, basis, Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks, Matrix.diagonal_apply]
      linear_combination -(hrem j (sel s))
  rw [← hmat]
  exact AbcTwoNinths.Basic.determinantDvdOfExpansion p _ coeff basis (fun _ => wt) hcoeff hcost

/-- Multi-indices of total degree below the contact depth in a common coordinate box. -/
abbrev LowNewtonIndex (ι : Type*) [Fintype ι] (D n : ℕ) :=
  {ν : ι → Fin D // (∑ i, (ν i : ℕ)) < n}

/-- The actual local evaluation matrix at nonnegative nodes, restricted to chosen columns. -/
def principalCharacterMinor [DecidableEq ι] (D n : ℕ) (g₀ : R) (g : ι → R)
    (b : J → ι → ℕ) (a : Col → ℕ) (y : Col → ι → ℕ) (sel : LowNewtonIndex ι D n ⊕ J → Col) :
    Matrix (LowNewtonIndex ι D n ⊕ J) (LowNewtonIndex ι D n ⊕ J) R :=
  fun r s => Sum.elim (fun (ν : LowNewtonIndex ι D n) x =>
    transverseBinomial (y x) (fun i => ν.val i)) (fun j x =>
      g₀ ^ a x * ((∏ i, g i ^ y x i) * transverseBinomial (y x) (b j))) r (sel s)

/-- Every choice of columns gives the full depth sum in its local determinant. -/
theorem principalCharacterMinor_dvd [DecidableEq ι] [DecidableEq J]
    (D n : ℕ) (p g₀ : R) (g : ι → R) (b : J → ι → ℕ) (a : Col → ℕ) (y : Col → ι → ℕ)
    (hg₀ : p ^ n ∣ g₀ - 1) (hg : ∀ i, p ∣ g i - 1) (hy : ∀ x i, y x i < D)
    (sel : LowNewtonIndex ι D n ⊕ J → Col) :
    p ^ (∑ j, (n - ∑ i, b j i)) ∣ (principalCharacterMinor D n g₀ g b a y sel).det := by
  classical
  apply determinant_dvd_of_lowRowResiduals p _ _ _ (fun j (ν : LowNewtonIndex ι D n) =>
    mixedNewtonCoefficient D g (b j) (fun i => ν.val i))
  intro j x
  have h := principalCharacterResidual_dvd D n p g₀ g (b j) hg₀ hg (a x) (y x) (hy x)
  rw [Finset.sum_subtype _ (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))] at h
  exact h

/-- Clearing the translated minor by a rational factor of valuation zero preserves its integer depth. -/
theorem principalCharacterMinor_integer_dvd [DecidableEq ι] [DecidableEq J]
    (D n p : ℕ) [Fact p.Prime] (g₀ : AbcTwoNinths.Basic.localRing p)
    (g : ι → AbcTwoNinths.Basic.localRing p) (b : J → ι → ℕ) (a : Col → ℕ) (y : Col → ι → ℕ)
    (hg₀ : (p : AbcTwoNinths.Basic.localRing p) ^ n ∣ g₀ - 1)
    (hg : ∀ i, (p : AbcTwoNinths.Basic.localRing p) ∣ g i - 1) (hy : ∀ x i, y x i < D)
    (sel : LowNewtonIndex ι D n ⊕ J → Col) (u : ℚ) (Z : ℤ) (hu : padicValRat p u = 0)
    (hZ : (Z : ℚ) = u * ((principalCharacterMinor D n g₀ g b a y sel).det : ℚ)) :
    p ^ (∑ j, (n - ∑ i, b j i)) ∣ Z.natAbs := by
  exact AbcSubexp.Prerequisites.integer_divisibility_after_unit_scaling
    ((AbcTwoNinths.Basic.localDvdIff _).mp
      (principalCharacterMinor_dvd D n (p : AbcTwoNinths.Basic.localRing p)
        g₀ g b a y hg₀ hg hy sel)) hu hZ

end AbcSubexp
