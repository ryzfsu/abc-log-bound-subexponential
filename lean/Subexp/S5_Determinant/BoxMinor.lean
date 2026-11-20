/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxCharacter
public import Subexp.S5_Determinant.TwoBlockRelation
public import Subexp.S5_Determinant.TwoBlockElimination
public import Subexp.S5_Determinant.BinomialRows

/-!
# The two sets of lattice columns

A base column is lifted from the phase-restricted simplex. Its translated
column uses the character of the actual translated lattice vector. The
vanishing of maximal minors on these columns gives a polynomial on the
original natural simplex, with the sum of the two row degrees as its bound.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters MvPolynomial

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

namespace HittingPrime

/-- A point in the full phase-restricted simplex of the contact prime. -/
abbrev BoxPoint (q : HittingPrime g) := ↥(q.points c.radius)

/-- The finite box-point subtype inherits its finite enumeration from the point set. -/
noncomputable instance (q : HittingPrime g) : Fintype q.BoxPoint := (q.finite_points _).fintype

/-- The unshifted transverse coordinates in the lattice box. -/
def boxVector (q : HittingPrime g) (z : q.BoxPoint) (i : Fin (dimension ε)) : ℤ :=
  (z.val i : ℤ) - c.shift

/-- An integral axial lift in the lattice box. -/
def boxAxis (q : HittingPrime g) (b : BoxData q) (z : q.BoxPoint) : ℤ :=
  Classical.choose ((b.box_projection z.val).mp z.property)

/-- The box-axis coordinate paired with a point satisfies the defining box bounds. -/
theorem box_axis_mem (q : HittingPrime g) (b : BoxData q) (z : q.BoxPoint) :
    q.box (q.boxAxis b z) (q.boxVector z) :=
  Classical.choose_spec ((b.box_projection z.val).mp z.property)

/-- Transverse coordinates on the two sets of columns with a common origin. -/
def columnCoordinate (q : HittingPrime g) (u s : Fin (dimension ε) → ℤ)
    (col : q.BoxPoint ⊕ q.BoxPoint) : Fin (dimension ε) → ℚ :=
  col.elim (fun z i => (z.val i : ℚ) + u i)
    (fun z i => ((z.val i : ℚ) + u i) + s i)

/-- The actual lattice character on each of the two sets of columns. -/
def columnCharacter (q : HittingPrime g) (b : BoxData q) (a : ℤ) (s : Fin (dimension ε) → ℤ)
    (col : q.BoxPoint ⊕ q.BoxPoint) : ℚ :=
  col.elim (fun z => q.character (q.boxAxis b z) (q.boxVector z))
    (fun z => q.character (q.boxAxis b z + a) (q.boxVector z + s))

/-- Matrix of binomial polynomial evaluations at the base and translated columns. -/
def boxMinorMatrix (q : HittingPrime g) (b : BoxData q)
    (a : ℤ) (s u : Fin (dimension ε) → ℤ)
    (I J : Finset (Fin (dimension ε) → ℕ)) : Matrix (↥I ⊕ ↥J) (q.BoxPoint ⊕ q.BoxPoint) ℚ :=
  twoBlockMatrix (fun i : ↥I => binomialRowPolynomial i.val)
    (fun j : ↥J => binomialRowPolynomial j.val) (q.columnCoordinate u s) (q.columnCharacter b a s)

/-- Vanishing maximal minors on the actual lattice columns yield the nonzero
polynomial on the exact simplex in the interpolation argument. -/
theorem exists_vanishing_polynomial_of_box_minors (q : HittingPrime g) (b : BoxData q)
    (a : ℤ) (s u : Fin (dimension ε) → ℤ) (hne : (a, s) ≠ 0)
    (I J : Finset (Fin (dimension ε) → ℕ)) {d₀ d₁ : ℕ}
    (hI : ∀ i ∈ I, ∑ k, i k ≤ d₀) (hJ : ∀ j ∈ J, ∑ k, j k ≤ d₁)
    (hd : d₀ + d₁ ≤ c.degree)
    (hminor : ∀ f : (↥I ⊕ ↥J) ↪ (q.BoxPoint ⊕ q.BoxPoint),
      ((q.boxMinorMatrix b a s u I J).submatrix id f).det = 0) :
    ∃ P : MvPolynomial (Fin (dimension ε)) ℚ, P ≠ 0 ∧ P.totalDegree ≤ c.degree ∧
      ∀ z ∈ q.points c.radius, eval (fun i => (z i : ℚ)) P = 0 := by
  classical
  obtain ⟨P, Q, hpq, dp, dq, hrel⟩ :=
    exists_twoBlockRelation_of_minors _ _
      (linearIndependent_binomialRowPolynomial (fun i : ↥I => i.val) Subtype.val_injective)
      (linearIndependent_binomialRowPolynomial (fun j : ↥J => j.val) Subtype.val_injective)
      _ _ (fun i : ↥I => (totalDegree_binomialRowPolynomial_le _).trans (hI _ i.property))
      (fun j : ↥J => (totalDegree_binomialRowPolynomial_le _).trans (hJ _ j.property)) hminor
  let y (z : q.BoxPoint) (i : Fin (dimension ε)) : ℚ := (z.val i : ℚ) + u i
  let r (z : q.BoxPoint) := q.character (q.boxAxis b z) (q.boxVector z)
  obtain ⟨F, hf, df, hv⟩ := exists_vanishing_polynomial_of_two_blocks
    y (fun i => (s i : ℚ)) r (q.character_ne_one a s hne)
    (fun z => q.character_ne_zero _ _) hpq dp dq (fun z => hrel (.inl z)) (fun z => by
      have hcoord : q.columnCoordinate u s (.inr z) = y z + fun i => (s i : ℚ) := by
        funext i
        rfl
      have hchar : q.columnCharacter b a s (.inr z) = r z * q.character a s :=
        q.character_add _ _ _ _
      simpa only [hcoord, hchar] using hrel (.inr z))
  obtain ⟨G, hg, dg, hgz⟩ := exists_vanishing_polynomial_of_translated_nodes
    (fun (z : q.BoxPoint) i => (z.val i : ℚ)) (fun i => (u i : ℚ)) hf (df.trans hd) hv
  exact ⟨G, hg, dg, fun z hz => hgz ⟨z, hz⟩⟩

end HittingPrime
end AbcSubexp
