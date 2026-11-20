/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxMinor

/-!
# Nonnegative coordinates of the box columns

Both column blocks use nonnegative exponents after a common lattice translation.
The translation contributes one common factor of valuation zero.

## Main results
* `AbcSubexp.HittingPrime.exists_normalized_box_columns`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

namespace HittingPrime

private theorem character_valuation_zero (q : HittingPrime g) (a : ℤ)
    (y : Fin (dimension ε) → ℤ) : padicValRat c.prime (q.character a y) = 0 := by
  classical
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  let w (i : Fin (dimension ε)) : ℚ := g.unit q.listIndex i ^ y i
  have hw (i : Fin (dimension ε)) : w i ≠ 0 :=
    zpow_ne_zero _ (g.unit_principal q.listIndex i).1
  have hv (i : Fin (dimension ε)) : padicValRat c.prime (w i) = 0 := by
    change padicValRat c.prime (g.unit q.listIndex i ^ y i) = 0
    rw [padicValRat.zpow, (g.unit_principal q.listIndex i).2.1, mul_zero]
  have hvprod (S : Finset (Fin (dimension ε))) : padicValRat c.prime (∏ i ∈ S, w i) = 0 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, padicValRat.mul (hw i)
        (Finset.prod_ne_zero_iff.mpr fun j _ => hw j), hv, ih, add_zero]
  change padicValRat c.prime (c.source ^ a * ∏ i, w i) = 0
  rw [padicValRat.mul (zpow_ne_zero _ c.source_principal.1)
    (Finset.prod_ne_zero_iff.mpr fun i _ => hw i), padicValRat.zpow,
    c.source_principal.2.1, mul_zero, hvprod, add_zero]

/-- The actual columns admit nonnegative coordinates in both blocks and a common
character factor whose valuation at the contact prime is zero. -/
theorem exists_normalized_box_columns (q : HittingPrime g) (b : BoxData q) (a : ℤ)
    (s : Fin (dimension ε) → ℤ) :
    ∃ (AX : (q.BoxPoint ⊕ q.BoxPoint) → ℕ)
      (Y : (q.BoxPoint ⊕ q.BoxPoint) → Fin (dimension ε) → ℕ) (κ : ℚ),
      κ ≠ 0 ∧ padicValRat c.prime κ = 0 ∧
      ∀ col, q.columnCoordinate (fun i => ((-s i).toNat : ℤ)) s col =
          (fun i => (Y col i : ℚ)) ∧
        q.columnCharacter b a s col = κ *
          (c.source ^ AX col * ∏ i, g.unit q.listIndex i ^ Y col i) := by
  classical
  let u (i : Fin (dimension ε)) : ℤ := (-s i).toNat
  let offset (i : Fin (dimension ε)) : ℤ := (c.shift : ℤ) + u i
  let axis (col : q.BoxPoint ⊕ q.BoxPoint) : ℤ :=
    col.elim (q.boxAxis b) (fun z => q.boxAxis b z + a)
  let transverse (col : q.BoxPoint ⊕ q.BoxPoint) : Fin (dimension ε) → ℤ :=
    col.elim q.boxVector (fun z => q.boxVector z + s)
  let bound : ℕ := ∑ col, (-axis col).toNat
  let AX (col : q.BoxPoint ⊕ q.BoxPoint) : ℕ := (axis col + (bound : ℤ)).toNat
  let Y (col : q.BoxPoint ⊕ q.BoxPoint) (i : Fin (dimension ε)) : ℕ :=
    (transverse col i + offset i).toNat
  have hAX (col : q.BoxPoint ⊕ q.BoxPoint) : (AX col : ℤ) = axis col + (bound : ℤ) := by
    have hbound : (-axis col).toNat ≤ bound :=
      Finset.single_le_sum (f := fun col => (-axis col).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ col)
    exact Int.toNat_of_nonneg (by omega)
  have hY (col : q.BoxPoint ⊕ q.BoxPoint) (i : Fin (dimension ε)) :
      (Y col i : ℤ) = transverse col i + offset i := by
    apply Int.toNat_of_nonneg
    cases col with
    | inl z =>
      change 0 ≤ (z.val i : ℤ) - c.shift + (c.shift + ((-s i).toNat : ℤ))
      omega
    | inr z =>
      change 0 ≤ ((z.val i : ℤ) - c.shift + s i) + (c.shift + ((-s i).toNat : ℤ))
      omega
  let κ := q.character (-(bound : ℤ)) (fun i => -offset i)
  refine ⟨AX, Y, κ, q.character_ne_zero _ _, character_valuation_zero q _ _, ?_⟩
  intro col
  constructor
  · funext i
    have hcast : (Y col i : ℚ) = (transverse col i : ℚ) + (offset i : ℚ) := by
      exact_mod_cast hY col i
    rw [hcast]
    cases col <;> simp only [columnCoordinate, Sum.elim_inl, Sum.elim_inr,
      transverse, boxVector, Pi.add_apply, offset, u, Int.cast_add, Int.cast_sub,
      Int.cast_natCast] <;> ring
  · have hcharacter : q.columnCharacter b a s col = q.character (axis col) (transverse col) := by
      cases col <;> rfl
    have hnat : q.character (AX col : ℤ) (fun i => (Y col i : ℤ)) =
        c.source ^ AX col * ∏ i, g.unit q.listIndex i ^ Y col i := by
      simp only [character, zpow_natCast]
    rw [hcharacter, ← hnat]
    change q.character (axis col) (transverse col) =
      q.character (-(bound : ℤ)) (fun i => -offset i) *
        q.character (AX col : ℤ) (fun i => (Y col i : ℤ))
    rw [← q.character_add]
    congr 1
    · rw [hAX]
      ring
    · funext i
      rw [Pi.add_apply, hY]
      ring

end HittingPrime
end AbcSubexp
