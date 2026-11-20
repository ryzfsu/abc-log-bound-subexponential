/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S5_Box.MinimumHeight
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# A short translation along one fresh generator

Dirichlet approximation on one phase yields the square-root height estimate
for the translation in the second set of columns.

## Main results

* `AbcSubexp.Box.short_translation_coefficients`
* `AbcSubexp.Box.shortest_translation`
-/

@[expose] public section

namespace AbcSubexp.Box

open Real

/-- A nonzero transverse coefficient and an integer axial correction give the
square-root estimate for one transverse generator. -/
theorem short_translation_coefficients (s : ℝ) {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hLH : L ≤ H) :
    ∃ a n : ℤ, 0 < n ∧ |(a : ℝ) + (n : ℝ) * s| * H + |(n : ℝ)| * (2 * L) ≤
      3 * sqrt (L / H) * H := by
  let r := sqrt (L / H)
  have hr : 0 < r := sqrt_pos.2 (div_pos hL hH)
  have hr2 : r ^ 2 = L / H := sq_sqrt (div_pos hL hH).le
  have hLH' : L = r ^ 2 * H := ((eq_div_iff hH.ne').mp hr2).symm
  have hr1 : r ≤ 1 := by
    have h := (div_le_one hH).mpr hLH
    nlinarith
  have hqpos : 0 < ⌊1 / r⌋₊ := Nat.floor_pos.mpr ((le_div_iff₀ hr).mpr (by linarith))
  obtain ⟨p, n, hn, hmax, hdist⟩ := exists_int_int_abs_mul_sub_le s hqpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr : (n : ℝ) * r ≤ 1 := by
    apply (le_div_iff₀ hr).mp
    have hceil : (n : ℝ) ≤ (⌊1 / r⌋₊ : ℝ) := by exact_mod_cast hmax
    exact hceil.trans (Nat.floor_le (by positivity))
  have hround := Nat.lt_floor_add_one (1 / r)
  have herr : 1 / ((⌊1 / r⌋₊ : ℝ) + 1) ≤ r := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_lt_iff₀ hr).mp hround
    linarith
  have hbound : |((-p : ℤ) : ℝ) + (n : ℝ) * s| ≤ r := by
    simpa only [Int.cast_neg, sub_eq_add_neg, add_comm (-(p : ℝ))] using hdist.trans herr
  have hterm : (n : ℝ) * L ≤ r * H := by
    have h := mul_le_mul_of_nonneg_right hnr (mul_pos hr hH).le
    rw [hLH']
    nlinarith
  refine ⟨-p, n, hn, ?_⟩
  rw [abs_of_pos hn']
  have h := mul_le_mul_of_nonneg_right hbound hH.le
  change _ ≤ 3 * r * H
  linarith

open Parameters

/-- The shortest nonzero character translation has the square-root height bound. -/
theorem shortest_translation {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}
    {g : GroupedTuple c} (q : HittingPrime g) (hm : 0 < dimension ε)
    (hL : 0 < log c.cutoff) (hH : 0 < AbcTwoNinths.Basic.rationalHeight c.source)
    (hLH : log c.cutoff ≤ AbcTwoNinths.Basic.rationalHeight c.source)
    (hcolumn : ∀ (i : Fin (dimension ε)) (a n : ℤ),
      AbcTwoNinths.Basic.rationalHeight (c.source ^ a * g.unit q.listIndex i ^ n) ≤
        |(a : ℝ) + (n : ℝ) * g.slope q.listIndex i| * AbcTwoNinths.Basic.rationalHeight c.source +
          |(n : ℝ)| * (2 * log c.cutoff)) :
    ∃ (a : ℤ) (y : Fin (dimension ε) → ℤ), (a, y) ≠ 0 ∧
      (∀ (a' : ℤ) (y' : Fin (dimension ε) → ℤ), (a', y') ≠ 0 →
        AbcTwoNinths.Basic.rationalHeight (q.character a y) ≤ AbcTwoNinths.Basic.rationalHeight (q.character a' y')) ∧
      AbcTwoNinths.Basic.rationalHeight (q.character a y) ≤
        (1 + 2 * (dimension ε : ℝ)) * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) *
          AbcTwoNinths.Basic.rationalHeight c.source := by
  classical
  let i : Fin (dimension ε) := ⟨0, hm⟩
  obtain ⟨a, n, hn, herr⟩ := short_translation_coefficients (g.slope q.listIndex i) hL hH hLH
  let y : Fin (dimension ε) → ℤ := Pi.single i n
  have hy : y i = n := by simp [y]
  have hne : (a, y) ≠ 0 := by
    intro hz
    have h0 := congrArg (fun v : ℤ × (Fin (dimension ε) → ℤ) => v.2 i) hz
    change y i = 0 at h0
    exact hn.ne' (hy.symm.trans h0)
  have heq : q.character a y = c.source ^ a * g.unit q.listIndex i ^ n := by
    unfold HittingPrime.character
    congr 1
    rw [Finset.prod_eq_single i, hy]
    · intro j _ hji
      simp [y, Pi.single_eq_of_ne hji]
    · simp
  obtain ⟨v, hv, hmin⟩ := exists_min_ratHeight
    (fun v : ℤ × (Fin (dimension ε) → ℤ) => v ≠ 0)
    (fun v => q.character v.1 v.2) ⟨(a, y), hne⟩
  refine ⟨v.1, v.2, hv, fun a' y' hne' => hmin (a', y') hne', ?_⟩
  calc
    AbcTwoNinths.Basic.rationalHeight (q.character v.1 v.2) ≤ AbcTwoNinths.Basic.rationalHeight (q.character a y) := hmin (a, y) hne
    _ ≤ 3 * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) * AbcTwoNinths.Basic.rationalHeight c.source := by
      rw [heq]
      exact (hcolumn i a n).trans herr
    _ ≤ _ := by
      have hm' : (1 : ℝ) ≤ dimension ε := by exact_mod_cast hm
      apply mul_le_mul_of_nonneg_right _ hH.le
      apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
      linarith

end AbcSubexp.Box
