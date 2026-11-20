/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-!
# Simplex row sets for the two determinant blocks

Both blocks use all multi-indices of weight strictly below their respective
cutoffs. A coordinate cube contained in the second simplex bounds the ratio
of the two row counts independently of the depth.
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators

/-- All transverse row indices of weight strictly below the cutoff. -/
def simplexRows (m n : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range n).filter fun k => ∑ i, k i < n

/-- Membership in a simplex row set is exactly the strict weight bound. -/
@[simp] theorem mem_simplexRows {m n : ℕ} {k : Fin m → ℕ} :
    k ∈ simplexRows m n ↔ ∑ i, k i < n := by
  refine Finset.mem_filter.trans ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr
    ((Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)).trans_lt h)

/-- Every row set is closed under coordinatewise decrease. -/
theorem simplexRows_lower {m n : ℕ} {k l : Fin m → ℕ} (hl : l ∈ simplexRows m n)
    (hkl : k ≤ l) : k ∈ simplexRows m n :=
  mem_simplexRows.mpr ((Finset.sum_le_sum fun i _ => hkl i).trans_lt (mem_simplexRows.mp hl))

/-- A positive cutoff gives a nonempty simplex row set. -/
theorem card_simplexRows_pos {m n : ℕ} (hn : 0 < n) : 0 < (simplexRows m n).card :=
  Finset.card_pos.mpr ⟨0, by simpa using hn⟩

/-- The enclosing coordinate cube bounds the first block. -/
theorem card_simplexRows_le (m n : ℕ) : (simplexRows m n).card ≤ n ^ m := by
  unfold simplexRows
  exact (Finset.card_filter_le ..).trans_eq (by simp)

/-- A real cutoff provides exactly the strict row-degree inequality. -/
theorem weight_lt_of_mem_simplexRows_ceil {m : ℕ} {u : ℝ} {k : Fin m → ℕ}
    (hk : k ∈ simplexRows m ⌈u⌉₊) : ((∑ i, k i : ℕ) : ℝ) < u :=
  Nat.lt_ceil.mp (mem_simplexRows.mp hk)

/-- The sum of the available residual exponents exceeds the uniform bound
obtained from the second-block cutoff. -/
theorem simplexRows_residual_sum_gt {m n : ℕ} (hn : 0 < n) {c : ℝ}
    (hc : 0 < c) (hc' : c ≤ 1) :
    ((simplexRows m ⌈c * n⌉₊).card : ℝ) * ((1 - c) * n) <
      ∑ k ∈ simplexRows m ⌈c * n⌉₊, ((n - ∑ i, k i : ℕ) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS := Finset.card_pos.mp
    (card_simplexRows_pos (m := m) (Nat.ceil_pos.mpr (mul_pos hc hn')))
  have hcn : c * n ≤ (n : ℝ) := by simpa using mul_le_mul_of_nonneg_right hc' hn'.le
  calc
    _ = ∑ _k ∈ simplexRows m ⌈c * n⌉₊, (1 - c) * n := by simp
    _ < _ := by
      apply Finset.sum_lt_sum_of_nonempty hS
      intro k hk
      have hw := weight_lt_of_mem_simplexRows_ceil hk
      have hle : ∑ i, k i ≤ n := by exact_mod_cast (hw.le.trans hcn)
      rw [Nat.cast_sub hle]
      linarith

/-- A cube of side `ceil(u / m)` fits inside the simplex of real cutoff `u`. -/
theorem pow_le_card_simplexRows_ceil {m : ℕ} (hm : 0 < m) (u : ℝ) :
    ⌈u / m⌉₊ ^ m ≤ (simplexRows m ⌈u⌉₊).card := by
  let Q := Fintype.piFinset fun _ : Fin m => Finset.range ⌈u / m⌉₊
  have hQ : Q ⊆ simplexRows m ⌈u⌉₊ := by
    intro k hk
    apply mem_simplexRows.mpr
    apply Nat.lt_ceil.mpr
    push_cast
    have hex : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    have hlt : (∑ i, (k i : ℝ)) < ∑ _ : Fin m, u / m :=
      Finset.sum_lt_sum_of_nonempty hex fun i _ =>
        Nat.lt_ceil.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hk i))
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simpa [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀, hm'] using hlt
  simpa [Q] using Finset.card_le_card hQ

/-- The ratio of total rows to second-block rows has a uniform bound. -/
theorem simplexRows_ratio_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {c : ℝ} (hc : 0 < c) :
    let A := (simplexRows m n).card
    let B := (simplexRows m ⌈c * n⌉₊).card
    ((A + B : ℕ) : ℝ) / B ≤ 1 + ((m : ℝ) / c) ^ m := by
  dsimp only
  let q := ⌈c * n / m⌉₊
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hB : 0 < (simplexRows m ⌈c * n⌉₊).card :=
    card_simplexRows_pos (Nat.ceil_pos.mpr (mul_pos hc hn'))
  have hB' : (0 : ℝ) < (simplexRows m ⌈c * n⌉₊).card := by exact_mod_cast hB
  have hq : c * n / m ≤ q := Nat.le_ceil _
  have hscale : (n : ℝ) ≤ (m / c) * q := by
    calc
      (n : ℝ) = (m / c) * (c * n / m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (div_nonneg hm'.le hc.le)
  have hA : ((simplexRows m n).card : ℝ) ≤ (n : ℝ) ^ m := by
    exact_mod_cast card_simplexRows_le m n
  have hqB : (q : ℝ) ^ m ≤ (simplexRows m ⌈c * n⌉₊).card := by
    exact_mod_cast pow_le_card_simplexRows_ceil hm (c * n)
  have hAB : ((simplexRows m n).card : ℝ) ≤ ((m : ℝ) / c) ^ m * (simplexRows m ⌈c * n⌉₊).card := by
    calc
      _ ≤ (n : ℝ) ^ m := hA
      _ ≤ ((m / c) * q) ^ m := pow_le_pow_left₀ hn'.le hscale m
      _ = _ := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left hqB (by positivity)
  rw [div_le_iff₀ hB', Nat.cast_add, add_mul, one_mul]
  linarith

/-- For nested blocks the total count is at most twice the enclosing cube size. -/
theorem card_simplexRows_add_le {m n : ℕ} {c : ℝ} (hc : c ≤ 1) :
    (simplexRows m n).card + (simplexRows m ⌈c * n⌉₊).card ≤ 2 * n ^ m := by
  have hcut : ⌈c * n⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    simpa using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) n)
  have hb := (card_simplexRows_le m ⌈c * n⌉₊).trans (Nat.pow_le_pow_left hcut m)
  have ha := card_simplexRows_le m n
  omega

/-- The normalized logarithm of the total number of rows is bounded independently of depth. -/
theorem log_card_simplexRows_add_div_le {m n : ℕ} (hn : 0 < n) {c : ℝ} (hc : c ≤ 1) :
    Real.log (((simplexRows m n).card + (simplexRows m ⌈c * n⌉₊).card : ℕ) : ℝ) / n
      ≤ Real.log 2 + m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < (simplexRows m n).card + (simplexRows m ⌈c * n⌉₊).card :=
    Nat.add_pos_left (card_simplexRows_pos hn) _
  have hR : (((simplexRows m n).card + (simplexRows m ⌈c * n⌉₊).card : ℕ) : ℝ)
      ≤ 2 * (n : ℝ) ^ m := by exact_mod_cast card_simplexRows_add_le (m := m) (n := n) hc
  apply (div_le_iff₀ hn').mpr
  calc
    _ ≤ Real.log (2 * (n : ℝ) ^ m) := Real.log_le_log (by exact_mod_cast hN) hR
    _ = Real.log 2 + m * Real.log n := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn'.ne'), Real.log_pow]
    _ ≤ (Real.log 2 + m) * n := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog := mul_le_mul_of_nonneg_left hn1 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      have hp := mul_le_mul_of_nonneg_left (Real.log_le_self hn'.le) (Nat.cast_nonneg (α := ℝ) m)
      linarith

end AbcSubexp
