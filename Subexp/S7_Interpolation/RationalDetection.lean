/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S7_Interpolation.NewtonExpansion
public import Subexp.S7_Interpolation.MinorLift

/-!
# Detecting rational polynomials on a bounded natural grid

This module formalizes rational-grid detection in Section 7.

Injectivity of the binomial evaluation matrix over a prime field implies that a bounded
set of natural points detects rational polynomials of bounded total degree.

## Main results

* `AbcSubexp.eq_zero_of_modular_binomial_kernel`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators

/-- A bounded set of natural points detects rational polynomials of total degree at most
`D` whenever it detects bounded-degree binomial coefficient vectors modulo a prime. -/
theorem eq_zero_of_modular_binomial_kernel {m D : ℕ} (q : ℕ) [Fact q.Prime]
    (B : (Fin m → ℕ) → Prop) (L : ℕ) (hB : ∀ z, B z → ∑ i, z i ≤ L)
    (hmod : ∀ A : Finset (Fin m → ℕ), (∀ a ∈ A, ∑ i, a i ≤ D) →
      ∀ c : (Fin m → ℕ) → ZMod q,
        (∀ z, B z → ∑ a ∈ A, c a * ∏ i, ((z i).choose (a i) : ZMod q) = 0) →
          ∀ a ∈ A, c a = 0)
    (P : MvPolynomial (Fin m) ℚ) (hD : P.totalDegree ≤ D)
    (hvan : ∀ z, B z → MvPolynomial.eval (fun i => (z i : ℚ)) P = 0) : P = 0 := by
  classical
  obtain ⟨w, hw, heval⟩ := exists_binomialEvaluation_expansion P hD
  let rows := (Fintype.piFinset fun _ : Fin m => Finset.range (L + 1)).filter B
  have mem_rows (z : Fin m → ℕ) : z ∈ rows ↔ B z := by
    refine ⟨fun h => (Finset.mem_filter.mp h).2, fun hz => Finset.mem_filter.mpr ⟨?_, hz⟩⟩
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_
    exact Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (z j))
      (Finset.mem_univ i)).trans (hB z hz))
  let M : Matrix (↥rows) (↥w.support) ℤ :=
    fun z a => ((∏ i, (z.val i).choose (a.val i) : ℕ) : ℤ)
  have hM : ∀ v : (↥w.support) → ZMod q,
      (∀ z : ↥rows, ∑ a : ↥w.support, (M z a : ZMod q) * v a = 0) → ∀ a, v a = 0 := by
    intro v hv
    let c (a : Fin m → ℕ) : ZMod q := if ha : a ∈ w.support then v ⟨a, ha⟩ else 0
    have hext (a : ↥w.support) : c a.val = v a := by
      simp only [c, dite_eq_left a.property]
    have hc := hmod w.support hw c (by
      intro z hz
      rw [← Finset.sum_coe_sort]
      simpa only [M, Int.cast_prod, Int.cast_natCast, Nat.cast_prod, hext, mul_comm]
        using hv ⟨z, (mem_rows z).mpr hz⟩)
    intro a
    simpa only [hext] using hc a.val a.property
  have hMw (z : ↥rows) : ∑ a : ↥w.support, (M z a : ℚ) * w a.val = 0 := by
    have hz := (heval z.val).symm.trans (hvan z.val ((mem_rows z.val).mp z.property))
    rw [← Finset.sum_coe_sort] at hz
    simpa only [M, Int.cast_prod, Int.cast_natCast, Nat.cast_prod, mul_comm] using hz
  have hzero := rational_kernel_eq_zero_of_modular q M hM (fun a => w a.val) hMw
  apply eq_zero_of_eval_natGrid
  intro z
  rw [heval z]
  exact Finset.sum_eq_zero fun a ha => by rw [hzero ⟨a, ha⟩, zero_mul]

end AbcSubexp
