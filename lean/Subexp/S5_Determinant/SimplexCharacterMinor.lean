/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.PrincipalCharacterMinor
public import Subexp.S5_Determinant.SimplexRows

/-!
# Local divisibility of simplex character minors

The full simplex of natural row indices supplies the low-degree terms in the
principal-character expansion. A common scalar in the second block preserves
the prime-power divisor of each residual row.

## Main results

* `AbcSubexp.simplexCharacterMinor_dvd`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open scoped BigOperators

private def lowNewtonIndexEquivSimplexRows {m D n : ℕ} (hD : n ≤ D) :
    LowNewtonIndex (Fin m) D n ≃ ↥(simplexRows m n) where
  toFun ν := ⟨fun i => ν.val i, mem_simplexRows.mpr ν.property⟩
  invFun k := ⟨fun i => ⟨k.val i, (Finset.single_le_sum (fun j _ => Nat.zero_le (k.val j))
    (Finset.mem_univ i)).trans_lt ((mem_simplexRows.mp k.property).trans_le hD)⟩,
    mem_simplexRows.mp k.property⟩
  left_inv _ := Subtype.ext (funext fun _ => Fin.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- Every full-sized minor on the two natural simplex blocks has the sum of
the contact depth differences as a prime-power divisor. -/
theorem simplexCharacterMinor_dvd {R Col : Type*} [CommRing R] [Fintype Col]
    (m n V : ℕ) (p κ g₀ : R) (g : Fin m → R) (a : Col → ℕ) (y : Col → Fin m → ℕ)
    (hg₀ : p ^ n ∣ g₀ - 1) (hg : ∀ i, p ∣ g i - 1)
    (f : ↥(simplexRows m n) ⊕ ↥(simplexRows m V) → Col) :
    p ^ (∑ j : ↥(simplexRows m V), (n - ∑ i, j.val i)) ∣
      Matrix.det (fun r s => Sum.elim (fun i col => transverseBinomial (y col) i.val)
        (fun j col => κ * (g₀ ^ a col * ∏ i, g i ^ y col i) * transverseBinomial (y col) j.val)
        r (f s) : Matrix (↥(simplexRows m n) ⊕ ↥(simplexRows m V))
          (↥(simplexRows m n) ⊕ ↥(simplexRows m V)) R) := by
  classical
  let bound := Finset.univ.sup fun col => Finset.univ.sup (y col)
  let D := n + bound + 1
  have hy (col : Col) (i : Fin m) : y col i < D := by
    have hi : y col i ≤ Finset.univ.sup (y col) :=
      Finset.le_sup (f := y col) (Finset.mem_univ i)
    have hcol : Finset.univ.sup (y col) ≤ bound :=
      Finset.le_sup (f := fun col => Finset.univ.sup (y col)) (Finset.mem_univ col)
    dsimp [D]
    omega
  let e := lowNewtonIndexEquivSimplexRows (m := m) (n := n) (D := D) (by dsimp [D]; omega)
  apply determinant_dvd_of_lowRowResiduals p _ _ _ (fun j i =>
    κ * mixedNewtonCoefficient D g j.val i.val)
  intro j col
  have h := principalCharacterResidual_dvd D n p g₀ g j.val hg₀ hg (a col) (y col) (hy col)
  rw [Finset.sum_subtype _ (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))] at h
  have hsum := Equiv.sum_comp e (fun i =>
    mixedNewtonCoefficient D g j.val i.val * transverseBinomial (y col) i.val)
  change (∑ ν : LowNewtonIndex (Fin m) D n,
    mixedNewtonCoefficient D g j.val (fun i => ν.val i) *
      transverseBinomial (y col) (fun i => ν.val i)) = _ at hsum
  rw [hsum] at h
  have hscaled := dvd_mul_of_dvd_right h κ
  simpa only [mul_sub, Finset.mul_sum, mul_assoc] using hscaled

end AbcSubexp
