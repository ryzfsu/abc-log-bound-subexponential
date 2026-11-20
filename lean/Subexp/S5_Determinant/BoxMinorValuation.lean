/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxMinor
public import Subexp.S5_Determinant.BoxLocalCoordinates
public import Subexp.S5_Determinant.PrincipalCharacterMinor
public import Subexp.S5_Determinant.SimplexCharacterMinor

/-!
# Contact-prime valuation of the lattice box minor

The principal axial source and the principal transverse units give the sum of
the residual depths for each nonzero maximal minor of the two box columns.

## Main results

* `AbcSubexp.HittingPrime.boxMinor_valuation_lower`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters MvPolynomial

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

private theorem local_principal_dvd {p : ℕ} [Fact p.Prime] {g : ℚ} (h : AbcTwoNinths.Basic.RatPrincipalUnit p g) :
    (p : AbcTwoNinths.Basic.localRing p) ∣ (⟨g, h.2.1.ge⟩ : AbcTwoNinths.Basic.localRing p) - 1 := by
  have hcong : AbcTwoNinths.Basic.RatCongruent p 1 g 1 := h.2.2.imp_right (fun hv => by
    change (1 : ℤ) ≤ padicValRat p (g - 1)
    omega)
  simpa using (AbcTwoNinths.Basic.localErrorDvd (n := 1) (⟨g, h.2.1.ge⟩ : AbcTwoNinths.Basic.localRing p) 1 hcong)

private theorem local_minor_valuation {p e : ℕ} [Fact p.Prime] {K : Type*}
    [Fintype K] [DecidableEq K] (L : Matrix K K (AbcTwoNinths.Basic.localRing p)) (M : Matrix K K ℚ)
    (hmap : (AbcTwoNinths.Basic.localRing p).subtype.mapMatrix L = M) (h : (p : AbcTwoNinths.Basic.localRing p) ^ e ∣ L.det)
    (hn : M.det ≠ 0) : (e : ℤ) ≤ padicValRat p M.det := by
  have heq : (L.det : ℚ) = M.det := by
    change (AbcTwoNinths.Basic.localRing p).subtype L.det = M.det
    rw [RingHom.map_det, hmap]
  have hv := (AbcTwoNinths.Basic.localDvdIff _).mp h
  rw [heq] at hv
  simpa using hv.resolve_left hn

namespace HittingPrime

private theorem boxMinor_map_matrix
    (q : HittingPrime g) (b : BoxData q) (a : ℤ) (s u : Fin (dimension ε) → ℤ)
    (n V : ℕ) [Fact c.prime.Prime]
    (f : (↥(simplexRows (dimension ε) n) ⊕ ↥(simplexRows (dimension ε) V)) →
      q.BoxPoint ⊕ q.BoxPoint)
    (ax : q.BoxPoint ⊕ q.BoxPoint → ℕ)
    (y : q.BoxPoint ⊕ q.BoxPoint → Fin (dimension ε) → ℕ)
    (κ₀ g₀ : AbcTwoNinths.Basic.localRing c.prime) (gs : Fin (dimension ε) → AbcTwoNinths.Basic.localRing c.prime)
    (hcoord : ∀ x, q.columnCoordinate u s x = (fun i => (y x i : ℚ)))
    (hchar : ∀ x, q.columnCharacter b a s x = (κ₀ : ℚ) *
      ((g₀ : ℚ) ^ ax x * ∏ i, (gs i : ℚ) ^ y x i)) :
    (AbcTwoNinths.Basic.localRing c.prime).subtype.mapMatrix (fun r k => Sum.elim
      (fun (i : ↥(simplexRows (dimension ε) n)) x => transverseBinomial (y x) i.val)
      (fun (j : ↥(simplexRows (dimension ε) V)) x => κ₀ * (g₀ ^ ax x * ∏ i, gs i ^ y x i) *
        transverseBinomial (y x) j.val) r (f k)) =
      (q.boxMinorMatrix b a s u (simplexRows (dimension ε) n) (simplexRows (dimension ε) V)).submatrix id f := by
  ext r k
  cases r with
  | inl i =>
    change ((transverseBinomial (y (f k)) i.val : AbcTwoNinths.Basic.localRing c.prime) : ℚ) =
      eval (q.columnCoordinate u s (f k)) (binomialRowPolynomial i.val)
    rw [hcoord, eval_binomialRowPolynomial_nat]
    simp [transverseBinomial]
  | inr j =>
    change ((κ₀ * (g₀ ^ ax (f k) * ∏ i, gs i ^ y (f k) i) *
      (transverseBinomial (y (f k)) j.val : AbcTwoNinths.Basic.localRing c.prime) : AbcTwoNinths.Basic.localRing c.prime) : ℚ) =
      q.columnCharacter b a s (f k) * eval (q.columnCoordinate u s (f k)) (binomialRowPolynomial j.val)
    rw [hcoord, hchar, eval_binomialRowPolynomial_nat]
    simp [transverseBinomial]

/-- The contact-prime valuation of every nonzero actual box minor is at least
the sum of its transverse residual depths. The origin makes both sets of
transverse polynomial nodes nonnegative. -/
theorem boxMinor_valuation_lower
    (q : HittingPrime g) (b : BoxData q) (a : ℤ) (s : Fin (dimension ε) → ℤ) (V : ℕ)
    (f : (↥(simplexRows (dimension ε) c.depth) ⊕ ↥(simplexRows (dimension ε) V)) ↪
      q.BoxPoint ⊕ q.BoxPoint)
    (hne : ((q.boxMinorMatrix b a s (fun i => ((-s i).toNat : ℤ))
      (simplexRows (dimension ε) c.depth) (simplexRows (dimension ε) V)).submatrix id f).det ≠ 0) :
    ((∑ j : ↥(simplexRows (dimension ε) V), (c.depth - ∑ i, j.val i)) : ℕ) ≤
      padicValRat c.prime ((q.boxMinorMatrix b a s (fun i => ((-s i).toNat : ℤ))
        (simplexRows (dimension ε) c.depth) (simplexRows (dimension ε) V)).submatrix id f).det := by
  classical
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  obtain ⟨ax, y, κ, _, hκ, hxy⟩ := q.exists_normalized_box_columns b a s
  let κ₀ : AbcTwoNinths.Basic.localRing c.prime := ⟨κ, hκ.ge⟩
  let g₀ : AbcTwoNinths.Basic.localRing c.prime := ⟨c.source, c.source_principal.2.1.ge⟩
  let gs (i : Fin (dimension ε)) : AbcTwoNinths.Basic.localRing c.prime :=
    ⟨g.unit q.listIndex i, (g.unit_principal q.listIndex i).2.1.ge⟩
  have hg₀ : (c.prime : AbcTwoNinths.Basic.localRing c.prime) ^ c.depth ∣ g₀ - 1 :=
    AbcTwoNinths.Basic.localErrorDvd _ _ (Or.inr c.depth_eq.ge)
  have hgs (i) : (c.prime : AbcTwoNinths.Basic.localRing c.prime) ∣ gs i - 1 :=
    local_principal_dvd (g.unit_principal q.listIndex i)
  have hmap := boxMinor_map_matrix q b a s _ c.depth V f ax y κ₀ g₀ gs
    (fun x => (hxy x).1) (fun x => (hxy x).2)
  exact local_minor_valuation _ _ hmap
    (simplexCharacterMinor_dvd (dimension ε) c.depth V (c.prime : AbcTwoNinths.Basic.localRing c.prime)
      κ₀ g₀ gs ax y hg₀ hgs f) hne

end HittingPrime
end AbcSubexp
