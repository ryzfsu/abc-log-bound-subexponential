/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Basic.BinomialMinorNonvanishing

/-!
# Lifting a trivial matrix kernel from a prime field

This module formalizes the modular-to-rational lifting step of Section 7.

An integer evaluation matrix with trivial column kernel modulo a prime has trivial column
kernel over the rationals. This is the determinant lift used in the interpolation argument.

## Main results
* `AbcSubexp.rational_kernel_eq_zero_of_modular`
-/

@[expose] public section

open scoped BigOperators Matrix

namespace AbcSubexp

/-- A nonzero minor over the prime field certifies a trivial rational column kernel. -/
theorem rational_kernel_eq_zero_of_modular (q : ℕ) [Fact q.Prime]
    {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℤ)
    (hmod : ∀ v : J → ZMod q,
      (∀ i : I, ∑ j : J, (M i j : ZMod q) * v j = 0) → ∀ j : J, v j = 0)
    (v : J → ℚ) (hv : ∀ i : I, ∑ j : J, (M i j : ℚ) * v j = 0) :
    ∀ j : J, v j = 0 := by
  classical
  let modMatrix := M.map fun z => (z : ZMod q)
  have hrows : LinearIndependent (ZMod q) modMatrixᵀ.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply hmod c
    intro i
    have hi := congrFun hc i
    simpa [modMatrix, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  obtain ⟨rows, hminor⟩ := AbcTwoNinths.Basic.minorOfIndependentRows modMatrixᵀ hrows
  let minor : Matrix J J ℤ := M.submatrix rows id
  have hmodMinor : ((Int.castRingHom (ZMod q)).mapMatrix minor).det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact hminor
  have hintMinor : minor.det ≠ 0 := by
    intro hz
    apply hmodMinor
    rw [← RingHom.map_det, hz, map_zero]
  let ratMinor := (Int.castRingHom ℚ).mapMatrix minor
  have hratMinor : ratMinor.det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix minor).det ≠ 0
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr hintMinor
  have hinj : Function.Injective ratMinor.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det ratMinor).mpr hratMinor.isUnit)
  have heq : ratMinor.mulVec v = ratMinor.mulVec 0 := by
    funext j
    rw [Matrix.mulVec_zero]
    exact hv (rows j)
  exact congrFun (hinj heq)

end AbcSubexp
