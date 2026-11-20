/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ThirdWindow
public import Subexp.S6_HittingPrime.ProductMissCount

/-!
# Comparing the miss set with the supply of primes

For the Section 6 hitting-prime argument, count all the integer times that
miss every row in the third window. A strict bound below the number of
primes in that window ensures that one prime hits a row.
-/

@[expose] public section

open Finset Real
open scoped BigOperators

namespace AbcSubexp

/-- All integer times in the third window, including its right endpoint. -/
def thirdWindowTimes (X : ℕ) := Ico (X / 3 + 1) (X + 1)

/-- Membership in the third-window time set is the defining interval condition. -/
theorem mem_thirdWindowTimes {X v : ℕ} : v ∈ thirdWindowTimes X ↔ X < 3 * v ∧ v ≤ X := by
  simp only [thirdWindowTimes, Finset.mem_Ico]
  omega

/-- The times in the third window that miss every row. -/
noncomputable def missedTimes {s : ℕ} (X : ℕ) (hit : ℕ → Fin s → Prop) : Finset ℕ := by
  classical
  exact (thirdWindowTimes X).filter (fun v => ∀ i, ¬hit v i)

/-- The joint miss set has fewer elements than the prime supply, even when we count
composite times among the misses. -/
theorem joint_miss_budget_of_kernel {X s : ℕ} {κ : Type*} [Fintype κ] [Zero κ]
    (hit : ℕ → Fin s → Prop) (U : Fin s → ℕ → ℝ) (c z : Fin s → κ → ℂ)
    {a M G : ℝ} (ha : 0 ≤ a) (hG : 0 ≤ G)
    (hU : ∀ i v, 0 ≤ U i v)
    (hmiss : ∀ v ∈ thirdWindowTimes X, ∀ i, ¬hit v i → 1 ≤ U i v)
    (hexp : ∀ i v, v ∈ thirdWindowTimes X → (U i v : ℂ) = ∑ k, c i k * (z i k) ^ v)
    (hz : ∀ i, z i 0 = 1) (hzero : ∀ i, ‖c i 0‖ ≤ a) (hmass : ∀ i, ∑ k, ‖c i k‖ ≤ M)
    (hgeom : ∀ f : Fin s → κ, f ≠ 0 →
      ‖∑ v ∈ thirdWindowTimes X, (∏ i, z i (f i)) ^ v‖ ≤ G)
    (hsaving : (X : ℝ) * a ^ s + M ^ s * G < X / (5 * log X))
    (hsupply : (X : ℝ) / (5 * log X) < (thirdWindowPrimes X).card) :
    (missedTimes X hit).card < (thirdWindowPrimes X).card := by
  classical
  let E := (thirdWindowTimes X).filter (fun v => ∀ i, ¬hit v i)
  have hbound := all_rows_miss_card_le (thirdWindowTimes X) E (filter_subset ..) U c z hG hU
    (fun v hv i => hmiss v (mem_filter.mp hv).1 i ((mem_filter.mp hv).2 i))
    hexp hz hzero hmass hgeom
  have hsize : (thirdWindowTimes X).card ≤ X := by
    simp only [thirdWindowTimes, Nat.card_Ico]
    omega
  have hsize' : ((thirdWindowTimes X).card : ℝ) * a ^ s ≤ (X : ℝ) * a ^ s :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (pow_nonneg ha s)
  exact_mod_cast (lt_of_le_of_lt (hbound.trans (add_le_add hsize' (le_refl _)))
    (hsaving.trans hsupply))

/-- A prime that misses every row belongs to the joint miss set. -/
theorem prime_mem_missedTimes_of_forall_miss {s X q : ℕ} (hit : ℕ → Fin s → Prop)
    (hq : q ∈ thirdWindowPrimes X) (hm : ∀ i, ¬hit q i) : q ∈ missedTimes X hit := by
  classical
  obtain ⟨_, hlo, hhi⟩ := mem_thirdWindowPrimes.mp hq
  exact mem_filter.mpr ⟨mem_thirdWindowTimes.mpr ⟨hlo, hhi⟩, hm⟩

end AbcSubexp
