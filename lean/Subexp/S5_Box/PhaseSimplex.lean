/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData

/-!
# Phase-restricted simplex

The integer coordinates of the lattice box project to a simplex with an axial
phase condition. The same phase condition is used at the smaller radius in
Section 5.

## Main results
* `AbcSubexp.Box.boxProjection`
* `AbcSubexp.Box.widthBounds`
* `AbcSubexp.Box.interpolationPointsSubset`
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace AbcSubexp.Box

open Parameters

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

private theorem shiftedPhase (q : HittingPrime g) (z : Fin (dimension ε) → ℕ) :
    (∑ i, g.slope q.listIndex i *
      (((z i : ℤ) - (c.shift : ℤ) : ℤ) : ℝ)) =
      q.phase + ∑ i, g.slope q.listIndex i * z i := by
  simp only [Int.cast_sub, Int.cast_natCast, mul_sub, Finset.sum_sub_distrib,
    HittingPrime.phase, mul_comm _ (c.shift : ℝ), Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  ring

private theorem transverseSum (z : Fin (dimension ε) → ℕ)
    (hcutoff : 0 < Real.log c.cutoff) (hbudget : 0 ≤ c.transverseBudget) :
    Real.log c.cutoff *
      (∑ i, (((z i : ℤ) - (c.shift : ℤ) : ℤ) : ℝ)) ≤ c.transverseBudget ↔
      (∑ i, z i) ≤ c.radius := by
  have hfloor : (c.shift : ℝ) ≤ c.transverseBudget / Real.log c.cutoff :=
    Nat.floor_le (div_nonneg hbudget hcutoff.le)
  have hnext : c.transverseBudget / Real.log c.cutoff < (c.shift : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hsum : (∑ i, (((z i : ℤ) - (c.shift : ℤ) : ℤ) : ℝ)) =
      ((∑ i, z i : ℕ) : ℝ) - ((dimension ε : ℝ) * (c.shift : ℝ)) := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  rw [mul_comm, ← le_div_iff₀ hcutoff, hsum]
  have hcard : (c.radius : ℝ) = ((dimension ε : ℝ) + 1) * (c.shift : ℝ) := by
    simp [Contact.radius]
  constructor
  · intro hz
    by_contra! hlarge
    have hlarge' : (c.radius : ℝ) + 1 ≤ ((∑ i, z i : ℕ) : ℝ) := by
      exact_mod_cast (show c.radius + 1 ≤ ∑ i, z i from Nat.succ_le_of_lt hlarge)
    rw [hcard] at hlarge'
    linarith
  · intro hz
    have hz' : ((∑ i, z i : ℕ) : ℝ) ≤ (c.radius : ℝ) := by exact_mod_cast hz
    rw [hcard] at hz'
    linarith

/-- The phase-restricted simplex is the transverse projection of the lattice box. -/
theorem boxProjection (q : HittingPrime g)
    (hcutoff : 0 < Real.log c.cutoff) (hbudget : 0 ≤ c.transverseBudget)
    (z : Fin (dimension ε) → ℕ) :
    z ∈ q.points c.radius ↔
      ∃ a : ℤ, q.box a (fun i => (z i : ℤ) - (c.shift : ℤ)) := by
  let phase := q.phase + ∑ i, g.slope q.listIndex i * z i
  have hsum := transverseSum z hcutoff hbudget
  have hlower (i : Fin (dimension ε)) :
      -c.transverseBudget ≤ Real.log c.cutoff * ((z i : ℤ) - (c.shift : ℤ) : ℤ) := by
    have hshift : (c.shift : ℝ) ≤ c.transverseBudget / Real.log c.cutoff :=
      Nat.floor_le (div_nonneg hbudget hcutoff.le)
    have hmul := (le_div_iff₀ hcutoff).mp hshift
    push_cast
    have hz : 0 ≤ Real.log c.cutoff * (z i : ℝ) := by positivity
    linarith [hmul]
  constructor
  · rintro ⟨hz, hphase⟩
    refine ⟨-round phase, ?_, hlower, hsum.mpr hz⟩
    rw [shiftedPhase, Int.cast_neg, neg_add_eq_sub]
    exact hphase
  · rintro ⟨a, ha, _, htransverse⟩
    refine ⟨hsum.mp htransverse, ?_⟩
    rw [shiftedPhase] at ha
    apply (round_le phase (-a)).trans
    simpa [sub_neg_eq_add, add_comm] using ha

/-- The interpolation simplex lies inside the determinant simplex. -/
theorem interpolationPointsSubset (q : HittingPrime g) :
    q.points (c.degree + q.prime) ⊆ q.points c.radius :=
  fun _ hz => ⟨hz.1.trans q.radius_le, hz.2⟩

/-- The full phase window has the required positive width and is shorter than one period. -/
theorem widthBounds (hε : 0 < ε) (hheight : 1 ≤ AbcTwoNinths.Basic.rationalHeight c.source) :
    windowWidth ε ≤ c.width ∧ c.width < 1 := by
  let e := exponent ε
  let k : ℝ := depthParameter ε
  let h := AbcTwoNinths.Basic.rationalHeight c.source
  let d : ℝ := (dimension ε : ℝ) + 1
  have he : 0 < e := lt_min hε (by norm_num)
  have he' : e ≤ 1 / 10 := min_le_right _ _
  have hk : 2 / e ≤ k := Nat.le_ceil _
  have hk' : 20 ≤ k := by
    apply le_trans _ hk
    apply (le_div_iff₀ he).mpr
    linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hh : 0 < h := lt_of_lt_of_le zero_lt_one hheight
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have he0 : 0 < 1 - e / 5 := by linarith
  have he1 : 1 - e / 5 ≤ 1 := by linarith
  have hrewrite :
      c.width = (1 - e / 5) * ((c.depth : ℝ) * Real.log (c.prime : ℝ)) / ((k + 1) * h) := by
    change d * ((1 - e / 5) * (c.depth : ℝ) * Real.log (c.prime : ℝ) /
      (d * (1 + 1 / k))) / (k * h) = _
    field_simp [ne_of_gt hd, ne_of_gt hh, ne_of_gt hk0, ne_of_gt hk1]
  rw [hrewrite]
  constructor
  · change e / (k + 1) ≤ _
    rw [div_le_div_iff₀ hk1 (mul_pos hk1 hh)]
    have hshare := mul_le_mul_of_nonneg_left c.depth_share.le he0.le
    have hm : e ≤ (1 - e / 5) * (2 * e) := by nlinarith
    have hscaled : e * h ≤ (1 - e / 5) * ((c.depth : ℝ) * Real.log (c.prime : ℝ)) :=
      (mul_le_mul_of_nonneg_right hm hh.le).trans
        (by simpa only [mul_assoc] using hshare)
    calc
      e * ((k + 1) * h) = (e * h) * (k + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscaled hk1.le
  · rw [div_lt_one (mul_pos hk1 hh)]
    have hlog : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    have hdepth' : (c.depth : ℝ) * Real.log (c.prime : ℝ) ≤ 2 * h := by
      linarith [c.depth_share_upper]
    have hlogPrime : 0 ≤ Real.log (c.prime : ℝ) :=
      Real.log_nonneg (by exact_mod_cast c.prime_isPrime.one_le)
    calc
      (1 - e / 5) * ((c.depth : ℝ) * Real.log (c.prime : ℝ)) ≤ 1 * (2 * h) :=
        mul_le_mul he1 hdepth' (by positivity) zero_le_one
      _ < (k + 1) * h := by nlinarith [mul_pos hh (show 0 < k - 1 by linarith)]

end AbcSubexp.Box
