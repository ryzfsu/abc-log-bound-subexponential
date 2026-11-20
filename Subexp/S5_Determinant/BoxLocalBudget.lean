/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.CharacterMinorHeight
public import Subexp.S5_Determinant.TranslationHeight
public import Subexp.S5_Box.CharacterHeight

/-!
# Local heights of columns in the determinant box

The roof projection splits the old-prime budget into the axial height times
the width and a sum of transverse errors.

## Main results
* `AbcSubexp.oldPrime_box_budget`
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real
open scoped BigOperators

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

/-- A real linear form on the box is bounded by its axial and projected coefficients. -/
theorem shearedBound (q : HittingPrime g)
    {a : ℤ} {y : Fin (dimension ε) → ℤ} (hbox : q.box a y)
    (ht : 0 < log c.cutoff) (v : ℝ) (w : Fin (dimension ε) → ℝ) :
    |(a : ℝ) * v + ∑ i, (y i : ℝ) * w i| ≤ c.width / 2 * |v| +
      (dimension ε * c.transverseBudget / log c.cutoff) *
        ∑ i, |w i - g.slope q.listIndex i * v| := by
  have heq : (a : ℝ) * v + ∑ i, (y i : ℝ) * w i =
      ((a : ℝ) + ∑ i, g.slope q.listIndex i * (y i : ℝ)) * v +
      ∑ i, (y i : ℝ) * (w i - g.slope q.listIndex i * v) := by
    rw [add_mul, add_assoc, Finset.sum_mul, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  refine (abs_add_le ..).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hbox.1 (abs_nonneg _)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((le_div_iff₀ ht).mpr (q.box_coordinate_le hbox i))
      (abs_nonneg _)

/-- The real axial coefficient at a finite place. -/
def oldAxial (c : Contact ε t) (p : ℕ) : ℝ := (padicValRat p c.source : ℝ)

/-- The transverse valuation after subtracting its roof slope times the axial valuation. -/
def oldProjection (q : HittingPrime g) (i : Fin (dimension ε)) (p : ℕ) : ℝ :=
  (padicValRat p (g.unit q.listIndex i) : ℝ) - g.slope q.listIndex i * oldAxial c p

/-- The transverse height bound extends across the roof prime, where the projection is zero. -/
theorem oldProjection_sum (q : HittingPrime g) (i : Fin (dimension ε)) :
    ∑ p ∈ t.radical.primeFactors, |oldProjection q i p| * log (p : ℝ) ≤ t.thirdLogRadical / log t.thirdLogRadical := by
  let f (p : ℕ) := |oldProjection q i p| * log (p : ℝ)
  have hr : oldProjection q i g.roof = 0 := by
    unfold oldProjection GroupedTuple.slope oldAxial
    rw [div_mul_cancel₀ _ (by exact_mod_cast g.roof_nonzero), sub_self]
  have he : ∑ p ∈ t.radical.primeFactors, f p = ∑ p ∈ t.radical.primeFactors.erase g.roof, f p := by
    by_cases hm : g.roof ∈ t.radical.primeFactors
    · simpa only [f, hr, abs_zero, zero_mul, add_zero] using
        (Finset.sum_erase_add t.radical.primeFactors f hm).symm
    · rw [Finset.erase_eq_of_notMem hm]
  exact he.le.trans (g.transverse_height q.listIndex i).le

private theorem oldAxial_sum :
    ∑ p ∈ t.radical.primeFactors, |oldAxial c p| * log (p : ℝ) ≤ 2 * AbcTwoNinths.Basic.rationalHeight c.source := by
  classical
  have hR : t.radical ≠ 0 := by
    unfold AbcTwoNinths.Basic.Triple.radical AbcTwoNinths.Basic.radical
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hs (p : ℕ) (hp : p.Prime) (hn : p ∉ t.radical.primeFactors) : padicValRat p c.source = 0 :=
    Box.sourceValuationZero hp (fun hd => hn (Nat.mem_primeFactors.mpr ⟨hp, hd, hR⟩))
  rw [Box.ratHeightCoordinates t.radical.primeFactors (fun _ => Nat.prime_of_mem_primeFactors)
    c.source c.source_principal.1 hs]
  have h := (AbcTwoNinths.PolyCap.coordHeightBounds
    (fun p : t.radical.primeFactors => (padicValRat p c.source : ℝ) * log (p : ℝ))).1
  have hsum : (∑ p : t.radical.primeFactors, |(padicValRat p c.source : ℝ) * log (p : ℝ)|) =
      ∑ p ∈ t.radical.primeFactors, |oldAxial c p| * log (p : ℝ) := by
    rw [Finset.sum_coe_sort t.radical.primeFactors (fun p : ℕ =>
      |(padicValRat p c.source : ℝ) * log (p : ℝ)|)]
    exact Finset.sum_congr rfl fun p _ => by rw [abs_mul, abs_of_nonneg (log_natCast_nonneg p)]; rfl
  rw [hsum] at h
  linarith

/-- Sum of the local column maxima on the old finite places of the first box.
The axial factor is the full width times the source height. The transverse
contribution has dimension squared and no factor counting the old primes. -/
theorem oldPrime_box_budget {I : Type*} [Fintype I] [Nonempty I]
    (q : HittingPrime g) (a : I → ℤ) (y : I → Fin (dimension ε) → ℤ)
    (hbox : ∀ j, q.box (a j) (y j)) (ht : 0 < log c.cutoff) :
    ∑ p ∈ t.radical.primeFactors,
        max (minorPrimeBudget (fun j => q.character (a j) (y j)) p : ℝ) 0 * log (p : ℝ) ≤
      c.width * AbcTwoNinths.Basic.rationalHeight c.source +
      (dimension ε : ℝ)^2 * c.transverseBudget / log c.cutoff * (t.thirdLogRadical / log t.thirdLogRadical) := by
  classical
  let k : ℝ := dimension ε * c.transverseBudget / log c.cutoff
  have hwidth := (abs_nonneg _).trans (hbox (Classical.arbitrary I)).1
  have hk : 0 ≤ k := by
    have hb := (hbox (Classical.arbitrary I)).2.2
    by_cases hm : dimension ε = 0
    · simp [k, hm]
    · let i : Fin (dimension ε) := ⟨0, Nat.pos_of_ne_zero hm⟩
      have hy := q.box_coordinate_le (hbox (Classical.arbitrary I)) i
      exact div_nonneg ((mul_nonneg (abs_nonneg _) ht.le).trans hy) ht.le
  let v (p : ℕ) := |oldAxial c p| * log (p : ℝ)
  let w (i : Fin (dimension ε)) (p : ℕ) := |oldProjection q i p| * log (p : ℝ)
  have hplace (p : ℕ) (hp : p ∈ t.radical.primeFactors) :
      max (minorPrimeBudget (fun j => q.character (a j) (y j)) p : ℝ) 0 * log (p : ℝ) ≤
      c.width / 2 * v p + k * ∑ i, w i p := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => -padicValRat p (q.character (a j) (y j)))
    rw [minorPrimeBudget, hj, Int.cast_neg]
    have hlin := shearedBound q (hbox j) ht (oldAxial c p)
      (fun i => (padicValRat p (g.unit q.listIndex i) : ℝ))
    have he := q.valuation_character (Nat.prime_of_mem_primeFactors hp) (a j) (y j)
    have he' := congrArg (fun x : ℤ => (x : ℝ)) he
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sum] at he'
    have H : -(padicValRat p (q.character (a j) (y j)) : ℝ) ≤ c.width / 2 * |oldAxial c p| +
        k * ∑ i, |oldProjection q i p| := (neg_le_abs _).trans (he' ▸ hlin)
    have hnon : 0 ≤ c.width / 2 * |oldAxial c p| + k * ∑ i, |oldProjection q i p| :=
      add_nonneg (mul_nonneg hwidth (abs_nonneg _))
        (mul_nonneg hk (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    refine (mul_le_mul_of_nonneg_right (max_le H hnon) (log_natCast_nonneg p)).trans_eq ?_
    simp only [v, w, add_mul, mul_assoc, Finset.sum_mul]
  calc
    _ ≤ ∑ p ∈ t.radical.primeFactors, (c.width / 2 * v p + k * ∑ i, w i p) :=
      Finset.sum_le_sum hplace
    _ = c.width / 2 * (∑ p ∈ t.radical.primeFactors, v p) +
        k * ∑ i, ∑ p ∈ t.radical.primeFactors, w i p := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ c.width / 2 * (2 * AbcTwoNinths.Basic.rationalHeight c.source) +
        k * ∑ _i : Fin (dimension ε), (t.thirdLogRadical / log t.thirdLogRadical) :=
      add_le_add (mul_le_mul_of_nonneg_left oldAxial_sum hwidth)
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => oldProjection_sum q i)) hk)
    _ = _ := by simp [k]; ring

/-- All finite local maxima of the unshifted box, restricted to any set of primes.
Each of the fresh primes, including the anchor, contributes at most the transverse budget. -/
theorem finite_box_budget {I : Type*} [Fintype I] [Nonempty I]
    (q : HittingPrime g) (a : I → ℤ) (y : I → Fin (dimension ε) → ℤ)
    (hbox : ∀ j, q.box (a j) (y j)) (ht : 0 < log c.cutoff) (hB : 0 ≤ c.transverseBudget)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, (minorPrimeBudget (fun j => q.character (a j) (y j)) p : ℝ) * log (p : ℝ) ≤
      c.width * AbcTwoNinths.Basic.rationalHeight c.source +
      (dimension ε : ℝ)^2 * c.transverseBudget / log c.cutoff * (t.thirdLogRadical / log t.thirdLogRadical) +
      (dimension ε + 1) * c.transverseBudget := by
  classical
  let u (j : I) := q.character (a j) (y j)
  let cost (p : ℕ) := max (minorPrimeBudget u p : ℝ) 0 * log (p : ℝ)
  let F := Finset.univ.image (g.prime q.listIndex)
  let F' := insert g.anchor F
  have hn (p : ℕ) : 0 ≤ cost p := mul_nonneg (le_max_right _ _) (log_natCast_nonneg p)
  have hscaled {p : ℕ} (hp : p.Prime) (hpL : (p : ℝ) ≤ c.cutoff)
      (hv : ∀ j, -(padicValRat p (u j) : ℝ) * log c.cutoff ≤ c.transverseBudget) :
      cost p ≤ c.transverseBudget := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => -padicValRat p (u j))
    have hv' := (le_div_iff₀ ht).mpr (hv j)
    have hm := max_le hv' (div_nonneg hB ht.le)
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
    change max ((minorPrimeBudget u p : ℤ) : ℝ) 0 * _ ≤ _
    rw [minorPrimeBudget, hj, Int.cast_neg]
    exact (mul_le_mul hm (log_le_log hp' hpL) (log_natCast_nonneg p) (div_nonneg hB ht.le)).trans_eq
      (div_mul_cancel₀ _ ht.ne')
  have hfresh (p : ℕ) (hp : p ∈ F') : cost p ≤ c.transverseBudget := by
    rcases Finset.mem_insert.mp hp with rfl | h
    · apply hscaled g.anchor_prime g.anchor_in_window.2
      intro j
      simpa only [u, q.valuation_character_anchor, Int.cast_neg, Int.cast_sum, neg_neg, mul_comm]
        using (hbox j).2.2
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      apply hscaled (g.prime_isPrime _ _) (g.primes_in_window _ _).2
      intro j
      simp only [u, q.valuation_character_fresh, neg_mul]
      linarith [(hbox j).2.1 i, mul_comm (y j i : ℝ) (log c.cutoff)]
  have hzero (p : ℕ) (hp : p.Prime) (ho : p ∉ t.radical.primeFactors) (hf : p ∉ F') :
      cost p = 0 := by
    have hR : t.radical ≠ 0 := by
      unfold AbcTwoNinths.Basic.Triple.radical AbcTwoNinths.Basic.radical
      exact Finset.prod_ne_zero_iff.mpr fun r hr => (Nat.prime_of_mem_primeFactors hr).ne_zero
    have hsource : padicValRat p c.source = 0 :=
      Box.sourceValuationZero hp (fun h => ho (Nat.mem_primeFactors.mpr ⟨hp, h, hR⟩))
    have hunit (i : Fin (dimension ε)) : padicValRat p (g.unit q.listIndex i) = 0 :=
      g.unit_support _ _ _ hp (fun h => hf (h ▸ Finset.mem_insert_self _ _))
        (fun h => hf (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)))
        hsource
    have hv (j : I) : padicValRat p (u j) = 0 := by
      simp [u, q.valuation_character hp, hsource, hunit]
    simp [cost, minorPrimeBudget, hv]
  have hcF : F'.card ≤ dimension ε + 1 := (Finset.card_insert_le ..).trans
    (Nat.add_le_add_right (by simpa [F] using (Finset.card_image_le
      (f := g.prime q.listIndex) (s := Finset.univ))) _)
  calc
    _ ≤ ∑ p ∈ S, cost p := Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_right (le_max_left _ _) (log_natCast_nonneg p)
    _ = ∑ p ∈ S ∩ (t.radical.primeFactors ∪ F'), cost p := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro p hp hn'
      have hh : p ∉ t.radical.primeFactors ∪ F' := fun h => hn' (Finset.mem_inter.mpr ⟨hp,h⟩)
      exact hzero p (hS p hp) (fun h => hh (Finset.mem_union_left _ h))
        (fun h => hh (Finset.mem_union_right _ h))
    _ ≤ ∑ p ∈ t.radical.primeFactors ∪ F', cost p :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => hn p)
    _ ≤ ∑ p ∈ t.radical.primeFactors, cost p + ∑ p ∈ F', cost p := by
      rw [← Finset.sum_union_inter]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => hn p)
    _ ≤ _ := by
      apply add_le_add (oldPrime_box_budget q a y hbox ht)
      calc
        _ ≤ ∑ _p ∈ F', c.transverseBudget := Finset.sum_le_sum hfresh
        _ = (F'.card : ℝ) * c.transverseBudget := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcF) hB

end AbcSubexp
