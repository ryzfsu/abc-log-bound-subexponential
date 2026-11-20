/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

/-!
# Counting times that miss every row

The product of the row majorants bounds the joint miss count used in Section 6.
Its finite character expansion separates the constant term from the remaining
geometric sums.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace AbcSubexp

/-- Multiply finite character expansions on disjoint rows, then sum over time. -/
private theorem sum_product_character_expansion {s : ℕ} {κ : Type*} [Fintype κ]
    (I : Finset ℕ) (c z : Fin s → κ → ℂ) :
    ∑ v ∈ I, ∏ i, (∑ k, c i k * (z i k) ^ v) =
      ∑ f : Fin s → κ, (∏ i, c i (f i)) * ∑ v ∈ I, (∏ i, z i (f i)) ^ v := by
  classical
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.prod_pow]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm

/-- The count of times missed by every row is bounded by the constant term
and the absolute mass of the nonconstant character sums. -/
theorem all_rows_miss_card_le {s : ℕ} {κ : Type*} [Fintype κ] [Zero κ]
    (I E : Finset ℕ) (hEI : E ⊆ I) (U : Fin s → ℕ → ℝ)
    (c z : Fin s → κ → ℂ) {a M G : ℝ} (hG : 0 ≤ G)
    (hU : ∀ i v, 0 ≤ U i v) (hmiss : ∀ v ∈ E, ∀ i, 1 ≤ U i v)
    (hexp : ∀ i v, v ∈ I → (U i v : ℂ) = ∑ k, c i k * (z i k) ^ v)
    (hz : ∀ i, z i 0 = 1) (hzero : ∀ i, ‖c i 0‖ ≤ a)
    (hmass : ∀ i, ∑ k, ‖c i k‖ ≤ M)
    (hgeom : ∀ f : Fin s → κ, f ≠ 0 → ‖∑ v ∈ I, (∏ i, z i (f i)) ^ v‖ ≤ G) :
    (E.card : ℝ) ≤ (I.card : ℝ) * a ^ s + M ^ s * G := by
  classical
  let C (f : Fin s → κ) := ∏ i, c i (f i)
  let T (f : Fin s → κ) := ∑ v ∈ I, (∏ i, z i (f i)) ^ v
  have hz' : T 0 = (I.card : ℂ) := by simp [T, hz]
  have hc0 : ‖C 0‖ ≤ a ^ s := by
    simpa [C] using (Finset.prod_le_prod₀
      (s := (univ : Finset (Fin s))) (f := fun i => ‖c i 0‖) (g := fun _ => a)
      (fun _ _ => norm_nonneg _) (fun i _ => hzero i))
  have hc : ∑ f, ‖C f‖ ≤ M ^ s := by
    simpa [C, Fintype.prod_sum] using (Finset.prod_le_prod₀
      (s := (univ : Finset (Fin s))) (f := fun i => ∑ k, ‖c i k‖) (g := fun _ => M)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun i _ => hmass i))
  have hrest : ∑ f ∈ univ.erase (0 : Fin s → κ), ‖C f * T f‖ ≤ M ^ s * G := by
    calc
      _ ≤ ∑ f ∈ univ.erase (0 : Fin s → κ), ‖C f‖ * G := by
        apply sum_le_sum
        intro f hf
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hgeom f (mem_erase.mp hf).1) (norm_nonneg _)
      _ = (∑ f ∈ univ.erase (0 : Fin s → κ), ‖C f‖) * G :=
        (Finset.sum_mul ..).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hG
        exact (sum_le_sum_of_subset_of_nonneg (erase_subset ..)
          (fun _ _ _ => norm_nonneg _)).trans hc
  have heval : ((∑ v ∈ I, ∏ i, U i v : ℝ) : ℂ) = ∑ f, C f * T f := by
    push_cast
    calc
      _ = ∑ v ∈ I, ∏ i, (∑ k, c i k * (z i k) ^ v) := by
        exact sum_congr rfl fun v hv => prod_congr rfl fun i _ => hexp i v hv
      _ = _ := sum_product_character_expansion I c z
  have htotal : 0 ≤ ∑ v ∈ I, ∏ i, U i v :=
    sum_nonneg fun v _ => prod_nonneg fun i _ => hU i v
  calc
    (E.card : ℝ) = ∑ _v ∈ E, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ E, ∏ i, U i v := by
      exact sum_le_sum fun v hv => one_le_prod₀ fun i _ => hmiss v hv i
    _ ≤ ∑ v ∈ I, ∏ i, U i v :=
      sum_le_sum_of_subset_of_nonneg hEI (fun v _ _ => prod_nonneg fun i _ => hU i v)
    _ = ‖∑ f, C f * T f‖ := by rw [← heval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htotal]
    _ ≤ ∑ f, ‖C f * T f‖ := norm_sum_le _ _
    _ = ‖C 0 * T 0‖ + ∑ f ∈ univ.erase (0 : Fin s → κ), ‖C f * T f‖ :=
      (Finset.add_sum_erase _ _ (mem_univ _)).symm
    _ ≤ _ := by
      rw [hz', norm_mul, Complex.norm_natCast]
      have hmain := mul_le_mul_of_nonneg_right hc0 (show 0 ≤ (I.card : ℝ) by positivity)
      exact add_le_add (by simpa [mul_comm] using hmain) hrest

end AbcSubexp
