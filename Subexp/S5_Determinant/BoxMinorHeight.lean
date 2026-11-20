/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxMinor
public import Subexp.S5_Determinant.CharacterMinorHeight

/-!
# Global height of the selected lattice minor

The positive and negative parts of the displacement give a common polynomial
origin and explicit nonnegative nodes on both sets of columns. Their weight
is at most the original simplex radius plus the sum of the absolute shifts.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp.HittingPrime

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

/-- The origin making both sets of actual transverse nodes nonnegative. -/
def columnOrigin (s : Fin (dimension ε) → ℤ) (i : Fin (dimension ε)) : ℤ := (-s i).toNat

/-- Nonnegative coordinates of both sets of lattice columns in the common origin. -/
def columnNode (q : HittingPrime g) (s : Fin (dimension ε) → ℤ)
    (col : q.BoxPoint ⊕ q.BoxPoint) (i : Fin (dimension ε)) : ℕ :=
  col.elim (fun z => z.val i + (-s i).toNat) (fun z => z.val i + (s i).toNat)

/-- The column-coordinate map agrees with the natural node coordinates. -/
theorem columnCoordinate_eq_natCast (q : HittingPrime g) (s : Fin (dimension ε) → ℤ)
    (col : q.BoxPoint ⊕ q.BoxPoint) :
    q.columnCoordinate (columnOrigin s) s col = fun i => (q.columnNode s col i : ℚ) := by
  funext i
  cases col with
  | inl z =>
    simp only [columnCoordinate, columnOrigin, columnNode, Sum.elim_inl, Int.cast_natCast,
      Nat.cast_add]
  | inr z =>
    have h : (((-s i).toNat : ℕ) : ℤ) + s i = (s i).toNat := by omega
    have h' : (((-s i).toNat : ℕ) : ℚ) + s i = (s i).toNat := by exact_mod_cast h
    simp only [columnCoordinate, columnOrigin, columnNode, Sum.elim_inr, Int.cast_natCast,
      Nat.cast_add, add_assoc, h']

/-- Total weight of the translated binomial nodes. -/
theorem columnNode_sum_le (q : HittingPrime g) (s : Fin (dimension ε) → ℤ)
    (col : q.BoxPoint ⊕ q.BoxPoint) :
    ∑ i, q.columnNode s col i ≤ c.radius + ∑ i, (s i).natAbs := by
  cases col with
  | inl z =>
    simp only [columnNode, Sum.elim_inl, Finset.sum_add_distrib]
    exact Nat.add_le_add z.property.1 (Finset.sum_le_sum fun i _ => by omega)
  | inr z =>
    simp only [columnNode, Sum.elim_inr, Finset.sum_add_distrib]
    exact Nat.add_le_add z.property.1 (Finset.sum_le_sum fun i _ => by omega)

private theorem character_valuation_zero (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    padicValRat c.prime (q.character a y) = 0 := by
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  have hu (s : Finset (Fin (dimension ε))) :
      padicValRat c.prime (∏ i ∈ s, g.unit q.listIndex i ^ y i) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, padicValRat.mul (zpow_ne_zero _ (g.unit_principal _ _).1)
        (Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (g.unit_principal _ j).1),
        padicValRat.zpow, (g.unit_principal _ _).2.1, ih]
      simp
  rw [character, padicValRat.mul (zpow_ne_zero _ c.source_principal.1)
    (Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (g.unit_principal _ j).1),
    padicValRat.zpow, c.source_principal.2.1, hu]
  simp

/-- The global determinant bound with the actual maxima on the selected box columns. -/
theorem boxMinor_depth_height (q : HittingPrime g) (b : BoxData q)
    (a : ℤ) (s : Fin (dimension ε) → ℤ)
    (I J : Finset (Fin (dimension ε) → ℕ)) [Nonempty (↥I ⊕ ↥J)]
    (f : (↥I ⊕ ↥J) ↪ (q.BoxPoint ⊕ q.BoxPoint)) (E : ℕ)
    (hd : ((q.boxMinorMatrix b a s (columnOrigin s) I J).submatrix id f).det ≠ 0)
    (hdepth : (E : ℤ) ≤ padicValRat c.prime
      ((q.boxMinorMatrix b a s (columnOrigin s) I J).submatrix id f).det) :
    let γ := fun j => q.columnCharacter b a s (f j)
    let N := I.card + J.card
    (E : ℝ) * log c.prime ≤ (J.card : ℝ) * (minorRealBudget γ +
        ∑ p ∈ minorCharacterPrimes c.prime γ, (minorPrimeBudget γ p : ℝ) * log p) +
      (N : ℝ) * ((c.radius + ∑ i, (s i).natAbs : ℕ) * log 2 + log (N : ℝ)) := by
  classical
  let w : Finset (↥I ⊕ ↥J) := Finset.univ.map Function.Embedding.inr
  let γ (j : ↥I ⊕ ↥J) := q.columnCharacter b a s (f j)
  let k : ↥I ⊕ ↥J → Fin (dimension ε) → ℕ := Sum.elim Subtype.val Subtype.val
  let y (j : ↥I ⊕ ↥J) := q.columnNode s (f j)
  have hm : (q.boxMinorMatrix b a s (columnOrigin s) I J).submatrix id f =
      characterMinor w (transverseBinomialMatrix k y) γ := by
    ext i j
    cases i <;> simp [boxMinorMatrix, twoBlockMatrix, Matrix.submatrix_apply,
      characterMinor, transverseBinomialMatrix, w, γ, k, y, columnCoordinate_eq_natCast,
      eval_binomialRowPolynomial_nat]
  have hunit (j : ↥I ⊕ ↥J) : padicValRat c.prime (γ j) = 0 := by
    cases hf : f j <;> simp [γ, hf, columnCharacter, character_valuation_zero]
  have hn (j : ↥I ⊕ ↥J) : γ j ≠ 0 := by
    cases hf : f j <;> simp [γ, hf, columnCharacter, character_ne_zero]
  rw [hm] at hd hdepth
  have h := binomialMinor_depth_height w k y γ c.prime E _ c.prime_isPrime hunit hn
    (fun j => q.columnNode_sum_le s (f j)) hd hdepth
  simpa [w, γ, Fintype.card_sum] using h

end AbcSubexp.HittingPrime
