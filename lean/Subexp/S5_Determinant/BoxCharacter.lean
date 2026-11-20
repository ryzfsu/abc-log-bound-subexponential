/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-!
# Characters and finite columns of the lattice box

The character multiplies under translation and takes a value different from
one on each nonzero displacement. Each phase-restricted simplex is finite.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

namespace HittingPrime

/-- The transverse coordinates are bounded by the radius. -/
theorem finite_points (q : HittingPrime g) (r : ℕ) : (q.points r).Finite := by
  classical
  apply (Set.finite_Iic (fun _ : Fin (dimension ε) => r)).subset
  intro z hz i
  exact (Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hz.1

/-- Every value of the lattice character is nonzero. -/
theorem character_ne_zero (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    q.character a y ≠ 0 := by
  exact mul_ne_zero (zpow_ne_zero _ c.source_principal.1)
    (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (g.unit_principal q.listIndex i).1)

/-- The character of a translated lattice point. -/
theorem character_add (q : HittingPrime g) (a b : ℤ) (y s : Fin (dimension ε) → ℤ) :
    q.character (a+b) (y+s) = q.character a y * q.character b s := by
  simp only [character, Pi.add_apply, zpow_add₀ c.source_principal.1,
    zpow_add₀ (g.unit_principal q.listIndex _).1, Finset.prod_mul_distrib]
  ring

/-- Restricting the grouped height separation to one list detects nonzero displacements. -/
theorem character_ne_one (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ)
    (hne : (a, y) ≠ 0) : q.character a y ≠ 1 := by
  classical
  let ys (b : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) := if b = q.listIndex then y else 0
  have hne' : (a, ys) ≠ 0 := by
    intro h
    apply hne
    have ha : a = 0 := congrArg Prod.fst h
    exact Prod.ext ha
      (by simpa [ys] using congrFun (congrArg Prod.snd h) q.listIndex)
  have hp : (∏ b, ∏ i, g.unit b i ^ ys b i) = ∏ i, g.unit q.listIndex i ^ y i := by
    rw [Finset.prod_eq_single q.listIndex]
    · simp [ys]
    · intro b _ hb
      simp [ys, hb]
    · simp
  have hsep := g.height_separation a ys hne'
  rw [hp] at hsep
  intro h
  change c.source ^ a * _ = 1 at h
  rw [h] at hsep
  simp [AbcTwoNinths.Basic.rationalHeight] at hsep
  exact (Real.exp_pos _).not_gt hsep

end HittingPrime
end AbcSubexp
