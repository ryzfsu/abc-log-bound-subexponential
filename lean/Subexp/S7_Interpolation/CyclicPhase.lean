/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Cyclic colours and admissible phase blocks

The coordinatewise slope hit supplies a cyclic interval of colours whose simplex points lie in
a prescribed phase block. This is the phase construction of Section 7.

## Main results
* `AbcSubexp.exists_cyclic_colour_phase`
* `AbcSubexp.exists_admissible_cyclic_colour_block`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators

private theorem roundedPhaseBound {m j b : ℕ} {phase w : ℝ} (hm : 0 < m)
    (hspacing : ((j + 1 : ℕ) : ℝ) / m ≤ w / 2) (hb : b ≤ j) :
    |phase + ((⌈-(m : ℝ) * (phase + w / 4)⌉ : ℤ) + (b : ℤ) : ℤ) /
      (m : ℝ)| ≤ w / 4 := by
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbReal : (b : ℝ) ≤ j := Nat.cast_le.mpr hb
  have hspacing' := (div_le_iff₀ hmReal).mp hspacing
  push_cast at hspacing'
  have hlower := Int.le_ceil (-(m : ℝ) * (phase + w / 4))
  have hupper := (Int.ceil_lt_add_one (-(m : ℝ) * (phase + w / 4))).le
  have hbNonneg : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  push_cast
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h : -(phase + w / 4) ≤
        ((⌈-(m : ℝ) * (phase + w / 4)⌉ : ℤ) + (b : ℝ)) / (m : ℝ) := by
      apply (le_div_iff₀ hmReal).mpr
      nlinarith only [hlower, hbNonneg]
    linarith only [h]
  · have h : ((⌈-(m : ℝ) * (phase + w / 4)⌉ : ℤ) + (b : ℝ)) / (m : ℝ) ≤
        w / 4 - phase := by
      apply (div_le_iff₀ hmReal).mpr
      nlinarith only [hupper, hspacing', hbReal]
    linarith only [h]

private theorem idealPhaseBound {m j : ℕ} {phase w : ℝ} {y : Fin m → ℕ}
    (hm : 0 < m) (hspacing : ((j + 1 : ℕ) : ℝ) / m ≤ w / 2)
    (hcolour : ∃ b : ℕ, b ≤ j ∧
      (∑ i, (i.val : ZMod m) * (y i : ZMod m)) =
        (⌈-(m : ℝ) * (phase + w / 4)⌉ : ℤ) + (b : ZMod m)) :
    ∃ turn : ℤ, |phase + (∑ i, ((i.val : ℝ) / m) * (y i : ℝ)) - (turn : ℝ)| ≤ w / 4 := by
  let start : ℤ := ⌈-(m : ℝ) * (phase + w / 4)⌉
  let weight : ℕ := ∑ i, i.val * y i
  obtain ⟨b, hb, heq⟩ := hcolour
  have hcast : ((start + (b : ℤ) : ℤ) : ZMod m) = ((weight : ℤ) : ZMod m) := by
    push_cast
    simpa [start, weight] using heq.symm
  obtain ⟨turn, hturn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have hturnReal : (weight : ℝ) - ((start : ℝ) + (b : ℝ)) = (m : ℝ) * (turn : ℝ) := by
    exact_mod_cast hturn
  have hweight : (∑ i, (i.val : ℝ) * (y i : ℝ)) = (weight : ℝ) := by
    simp only [weight, Nat.cast_sum, Nat.cast_mul]
  have hmNe : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hideal :
      phase + (∑ i, ((i.val : ℝ) / m) * (y i : ℝ)) - (turn : ℝ) =
        phase + ((start : ℝ) + (b : ℝ)) / (m : ℝ) := by
    simp_rw [div_mul_eq_mul_div]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, hweight]
    field_simp
    linarith only [hturnReal]
  refine ⟨turn, ?_⟩
  rw [hideal]
  simpa [start] using roundedPhaseBound (phase := phase) hm hspacing hb

/-- The cyclic colour interval from Section 7 lies in the width `W` phase strip. -/
theorem exists_cyclic_colour_phase {m j : ℕ} {slope : Fin m → ℝ} {phase w W η : ℝ}
    (hm : 0 < m) (hspacing : ((j + 1 : ℕ) : ℝ) / m ≤ w / 2)
    (herror : ((j + 1 : ℕ) : ℝ) * η ≤ w / 4) (hwidth : w ≤ W)
    (hhit : ∀ i, ∃ z : ℤ, |slope i - (i.val : ℝ) / m - (z : ℝ)| < η) :
    ∃ t : ZMod m, ∀ y : Fin m → ℕ, (∑ i, y i) ≤ j + 1 →
      (∃ b : ℕ, b ≤ j ∧ (∑ i, (i.val : ZMod m) * (y i : ZMod m)) = t + (b : ZMod m)) →
      ∃ a : ℤ, |phase + (∑ i, slope i * (y i : ℝ)) - (a : ℝ)| ≤ W / 2 := by
  classical
  choose shift hshift using hhit
  have hη : 0 ≤ η := (abs_nonneg _).trans (hshift ⟨0, hm⟩).le
  refine ⟨(⌈-(m : ℝ) * (phase + w / 4)⌉ : ℤ), ?_⟩
  intro y hy hcolour
  obtain ⟨turn, hturn⟩ := idealPhaseBound (phase := phase) hm hspacing hcolour
  let error : Fin m → ℝ := fun i => slope i - (i.val : ℝ) / m - (shift i : ℝ)
  have hyReal : (∑ i, (y i : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr hy
  have hsumError : |∑ i, error i * (y i : ℝ)| ≤ w / 4 := by
    calc
      |∑ i, error i * (y i : ℝ)| ≤ ∑ i, |error i * (y i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, η * (y i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [abs_mul, abs_of_nonneg (show 0 ≤ (y i : ℝ) from Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hshift i).le (Nat.cast_nonneg (y i))
      _ = η * ∑ i, (y i : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ η * ((j + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hyReal hη
      _ ≤ w / 4 := by simpa [mul_comm] using herror
  refine ⟨turn + ∑ i, shift i * (y i : ℤ), ?_⟩
  have heq :
      phase + (∑ i, slope i * (y i : ℝ)) -
          ((turn + ∑ i, shift i * (y i : ℤ) : ℤ) : ℝ) =
        (phase + (∑ i, ((i.val : ℝ) / m) * (y i : ℝ)) - (turn : ℝ)) +
          ∑ i, error i * (y i : ℝ) := by
    simp only [error, sub_mul, Finset.sum_sub_distrib, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast]
    ring
  rw [heq]
  exact (abs_add_le ..).trans (by linarith only [hturn, hsumError, hwidth])

/-- Section 7's cyclic witnesses lie in the actual phase simplex and have the required digits. -/
theorem exists_admissible_cyclic_colour_block {m q k D L : ℕ} {r : Fin m → ℕ}
    {slope : Fin m → ℝ} {θ w W η : ℝ}
    (hm : 0 < m) (hscale : D < q * (k + 1)) (hbaseSize : k + 1 < q)
    (hroom : D + q ≤ L) (hr : (∑ i, r i) ≤ D) (hrDigit : ∀ i, r i < q)
    (hspacing : ((k + 1 : ℕ) : ℝ) / m ≤ w / 2)
    (herror : ((k + 1 : ℕ) : ℝ) * η ≤ w / 4) (hwidth : w ≤ W)
    (hhit : ∀ i, ∃ z : ℤ, |(q : ℝ) * slope i - (i.val : ℝ) / m - (z : ℝ)| < η) :
    let j := (D - ∑ i, r i) / q
    j ≤ k ∧ ∃ t : ZMod m, ∀ y : Fin m → ℕ, (∑ i, y i) ≤ j + 1 →
      (∃ b : ℕ, b ≤ j ∧ (∑ i, (i.val : ZMod m) * (y i : ZMod m)) = t + (b : ZMod m)) →
      (∑ i, (q * y i + r i)) ≤ L ∧
      (∃ a : ℤ, |θ + (∑ i, slope i * ((q * y i + r i : ℕ) : ℝ)) - (a : ℝ)| ≤ W / 2) ∧
      ∀ i, (q * y i + r i) % q = r i ∧ (q * y i + r i) / q = y i ∧ y i < q := by
  dsimp only
  let j := (D - ∑ i, r i) / q
  have hq : 0 < q := by omega
  have hj : j ≤ k := by
    have hlt : D - ∑ i, r i < (k + 1) * q :=
      (Nat.sub_le ..).trans_lt (by simpa [Nat.mul_comm] using hscale)
    have hdiv := (Nat.div_lt_iff_lt_mul hq).mpr hlt
    change j < k + 1 at hdiv
    omega
  have hη : 0 ≤ η := by
    obtain ⟨z, hz⟩ := hhit ⟨0, hm⟩
    exact (abs_nonneg _).trans hz.le
  have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
  obtain ⟨t, ht⟩ := exists_cyclic_colour_phase
    (phase := θ + ∑ i, slope i * (r i : ℝ)) hm
    ((div_le_div_of_nonneg_right hcast (Nat.cast_nonneg m)).trans hspacing)
    ((mul_le_mul_of_nonneg_right hcast hη).trans herror) hwidth hhit
  refine ⟨hj, t, ?_⟩
  intro y hy hcolour
  have hdiv : q * j ≤ D - ∑ i, r i := by
    simpa [j, Nat.mul_comm] using Nat.div_mul_le_self (D - ∑ i, r i) q
  have hsize : (∑ i, (q * y i + r i)) ≤ L := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      q * (∑ i, y i) + ∑ i, r i ≤ q * (j + 1) + ∑ i, r i :=
        Nat.add_le_add_right (Nat.mul_le_mul_left q hy) _
      _ = q * j + (∑ i, r i) + q := by ring
      _ ≤ D + q := by omega
      _ ≤ L := hroom
  obtain ⟨a, ha⟩ := ht y hy hcolour
  have hphase :
      θ + (∑ i, slope i * ((q * y i + r i : ℕ) : ℝ)) =
        (θ + ∑ i, slope i * (r i : ℝ)) + ∑ i, ((q : ℝ) * slope i) * (y i : ℝ) := by
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    have hcomm :
        (∑ i, slope i * ((q : ℝ) * (y i : ℝ))) =
          ∑ i, ((q : ℝ) * slope i) * (y i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, mul_comm (slope i) (q : ℝ)]
    rw [hcomm]
    ring
  refine ⟨hsize, ⟨a, ?_⟩, ?_⟩
  · rwa [hphase]
  · intro i
    have hyi : y i ≤ ∑ i, y i :=
      Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine ⟨?_, ?_, lt_of_le_of_lt (hyi.trans (hy.trans (Nat.succ_le_succ hj))) hbaseSize⟩
    · rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (hrDigit i)]
    · rw [Nat.mul_add_div hq, Nat.div_eq_of_lt (hrDigit i), Nat.add_zero]

end AbcSubexp
