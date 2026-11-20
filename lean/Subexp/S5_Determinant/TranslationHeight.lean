/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxCharacter
public import Subexp.Basic.ContactValuation
public import AbcTwoNinths.Paper.S2_PolyCap.OddPrimePowerLifting
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Fresh valuations and the size of translated columns

A selected fresh prime reads its transverse coordinate. The logarithmic height
of a displacement bounds each such coordinate. Taking both translates costs
the height of the displacement once in the projective height of the column family.
-/

@[expose] public section

noncomputable section

namespace AbcSubexp

open Parameters Real

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

private theorem valuation_prod {ι : Type*} {p : ℕ} [Fact p.Prime] (S : Finset ι)
    (f : ι → ℚ) (hf : ∀ i, f i ≠ 0) :
    padicValRat p (∏ i ∈ S, f i) = ∑ i ∈ S, padicValRat p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, padicValRat.mul (hf i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hf j), ih]

/-- The local valuation of a lattice character is linear in all coordinates. -/
theorem HittingPrime.valuation_character (q : HittingPrime g) {p : ℕ} (hp : p.Prime)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    padicValRat p (q.character a y) = a * padicValRat p c.source +
      ∑ i, y i * padicValRat p (g.unit q.listIndex i) := by
  let : Fact p.Prime := ⟨hp⟩
  have h (i) := zpow_ne_zero (y i) (g.unit_principal q.listIndex i).1
  simp only [character, padicValRat.mul (zpow_ne_zero _ c.source_principal.1)
    (Finset.prod_ne_zero_iff.mpr fun i _ => h i), valuation_prod _ _ h, padicValRat.zpow]

/-- The valuation at the selected fresh prime is exactly its transverse coordinate. -/
theorem HittingPrime.valuation_character_fresh (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) (i : Fin (dimension ε)) :
    padicValRat (g.prime q.listIndex i) (q.character a y) = y i := by
  have hp := g.prime_isPrime q.listIndex i
  have hsrc := c.valuation_eq_zero_of_fresh hp (g.prime_fresh q.listIndex i)
  rw [q.valuation_character hp, hsrc, mul_zero, zero_add, Finset.sum_eq_single i,
    g.unit_fresh, mul_one]
  · intro j _ hji
    have hij : g.prime q.listIndex i ≠ g.prime q.listIndex j := fun h =>
      hji (congrArg Prod.snd (g.primes_distinct (a₁ := (q.listIndex,i))
        (a₂ := (q.listIndex,j)) h)).symm
    rw [g.valuation_eq_zero_outside_support _ _ hp (g.prime_fresh _ _)
      (g.prime_ne_anchor _ _) hij, mul_zero]
  · simp

/-- The anchor valuation is the negative sum of all transverse coordinates. -/
theorem HittingPrime.valuation_character_anchor (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    padicValRat g.anchor (q.character a y) = -(∑ i, y i) := by
  simp [q.valuation_character g.anchor_prime, c.valuation_eq_zero_of_fresh
    g.anchor_prime g.anchor_fresh, g.unit_anchor]

private theorem local_weight_le_ratHeight {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) :
    |(padicValRat p x : ℝ)| * log p ≤ AbcTwoNinths.Basic.rationalHeight x := by
  let : Fact p.Prime := ⟨hp⟩
  have hn := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hx)
  have hd := x.den_pos
  have hl : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_le)
  have hbound (n : ℕ) (hn' : 0 < n) (hnle : n ≤ max x.num.natAbs x.den) :
      (padicValNat p n : ℝ) * log p ≤ AbcTwoNinths.Basic.rationalHeight x :=
    (AbcTwoNinths.PolyCap.logIndexBound hn').trans (log_le_log (by exact_mod_cast hn')
      (by exact_mod_cast hnle))
  rw [padicValRat_def]
  change |(((padicValNat p x.num.natAbs : ℤ) - (padicValNat p x.den : ℤ) : ℤ) : ℝ)|
      * log p ≤ _
  simp only [Int.cast_sub, Int.cast_natCast]
  rcases le_total (padicValNat p x.den : ℝ) (padicValNat p x.num.natAbs : ℝ) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hl).trans
      (hbound _ hn (le_max_left _ _))
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hl).trans
      (hbound _ hd (le_max_right _ _))

/-- A fresh exponent, weighted by its own logarithm, costs at most the character height. -/
theorem HittingPrime.fresh_weight_le_height (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) (i : Fin (dimension ε)) :
    |(y i : ℝ)| * log (g.prime q.listIndex i : ℝ) ≤ AbcTwoNinths.Basic.rationalHeight (q.character a y) := by
  rw [← q.valuation_character_fresh a y i]
  exact local_weight_le_ratHeight (g.prime_isPrime _ _) (q.character_ne_zero _ _)

/-- The weight of the sum coordinate at the anchor obeys the same height bound. -/
theorem HittingPrime.anchor_weight_le_height (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) :
    |∑ i, (y i : ℝ)| * log (g.anchor : ℝ) ≤ AbcTwoNinths.Basic.rationalHeight (q.character a y) := by
  simpa [q.valuation_character_anchor] using
    local_weight_le_ratHeight g.anchor_prime (q.character_ne_zero a y)

private theorem log_cutoff_le_twice {p : ℕ} (hp : p.Prime) (hf : ¬ p ∣ t.radical)
    (hw : c.cutoff / 3 < p) (hle : (p : ℝ) ≤ c.cutoff) :
    log c.cutoff ≤ 2 * log p := by
  have hge : 3 ≤ p := by
    have hn : p ≠ 2 := by
      rintro rfl
      apply not_dvd_abc_of_fresh hp hf
      have hh : 2 ∣ t.a ∨ 2 ∣ t.b ∨ 2 ∣ t.c := by have := t.add; omega
      rcases hh with h | h | h
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
      · exact dvd_mul_of_dvd_right h _
    have := hp.two_le
    omega
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hge
  have hpos : 0 < c.cutoff := (by positivity : (0 : ℝ) < p).trans_le hle
  have hpow : c.cutoff ≤ (p : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (Nat.cast_nonneg (α := ℝ) p)]
  simpa only [log_pow, Nat.cast_ofNat] using log_le_log hpos hpow

/-- Every transverse displacement costs at most twice its height in cutoff units. -/
theorem HittingPrime.displacement_coordinate_le (q : HittingPrime g)
    (a : ℤ) (y : Fin (dimension ε) → ℤ) (i : Fin (dimension ε)) :
    |(y i : ℝ)| * log c.cutoff ≤ 2 * AbcTwoNinths.Basic.rationalHeight (q.character a y) := by
  have hw := g.primes_in_window q.listIndex i
  have h := log_cutoff_le_twice (g.prime_isPrime _ _) (g.prime_fresh _ _) hw.1 hw.2
  linarith [mul_le_mul_of_nonneg_left h (abs_nonneg (y i : ℝ)), q.fresh_weight_le_height a y i]

/-- The simplex inequalities bound each signed coordinate of every base column. -/
theorem HittingPrime.box_coordinate_le (q : HittingPrime g)
    {a : ℤ} {y : Fin (dimension ε) → ℤ} (hy : q.box a y) (i : Fin (dimension ε)) :
    |(y i : ℝ)| * log c.cutoff ≤ (dimension ε : ℝ) * c.transverseBudget := by
  have hdim := (Nat.zero_le i.val).trans_lt i.isLt
  have hd : (1 : ℝ) ≤ dimension ε := by exact_mod_cast Nat.succ_le_of_lt hdim
  have hB : 0 ≤ c.transverseBudget := by
    have he : exponent ε ≤ 1/10 := min_le_right _ _
    have hl : 0 ≤ log (c.prime : ℝ) := log_nonneg (by exact_mod_cast c.prime_isPrime.one_le)
    unfold Contact.transverseBudget
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hl) (by positivity)
  have hM : 0 ≤ log c.cutoff := log_nonneg
    ((by exact_mod_cast g.anchor_prime.one_le : (1 : ℝ) ≤ g.anchor).trans g.anchor_in_window.2)
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => log c.cutoff * y j + c.transverseBudget)
    (fun j _ => by linarith [hy.2.1 j]) (Finset.mem_univ i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hi
  rw [← abs_of_nonneg hM, ← abs_mul, mul_comm (y i : ℝ) (log c.cutoff), abs_le]
  exact ⟨by linarith [hy.2.1 i, mul_le_mul_of_nonneg_right hd hB], by linarith [hy.2.2]⟩

/-- The same bound on a translated column includes the displacement height once. -/
theorem HittingPrime.translated_box_coordinate_le (q : HittingPrime g)
    {a : ℤ} {y : Fin (dimension ε) → ℤ} (hy : q.box a y)
    (b : ℤ) (s : Fin (dimension ε) → ℤ) (i : Fin (dimension ε)) :
    |((y i + s i : ℤ) : ℝ)| * log c.cutoff ≤
      (dimension ε : ℝ) * c.transverseBudget + 2 * AbcTwoNinths.Basic.rationalHeight (q.character b s) := by
  have hM : 0 ≤ log c.cutoff := log_nonneg
    ((by exact_mod_cast g.anchor_prime.one_le : (1 : ℝ) ≤ g.anchor).trans g.anchor_in_window.2)
  push_cast
  calc
    _ ≤ (|(y i : ℝ)| + |(s i : ℝ)|) * log c.cutoff :=
      mul_le_mul_of_nonneg_right (abs_add_le ..) hM
    _ ≤ _ := by rw [add_mul]; exact add_le_add (q.box_coordinate_le hy i)
                  (q.displacement_coordinate_le b s i)

/-- A single integral shift makes both boxes nonnegative. The sum of shifted
coordinates stays within the global binomial budget of Section 5. -/
theorem HittingPrime.exists_common_coordinate_shift (q : HittingPrime g)
    (b : ℤ) (s : Fin (dimension ε) → ℤ) (n : ℕ)
    (hB : c.transverseBudget ≤ 2 * n * log c.cutoff)
    (hJ : AbcTwoNinths.Basic.rationalHeight (q.character b s) ≤ 2 * n * log c.cutoff) :
    ∃ u : ℤ, ∀ a y, q.box a y → ∀ v : Fin (dimension ε) → ℤ, v = y ∨ v = y + s →
      (∀ i, 0 ≤ v i + u) ∧ ∑ i, (v i + u).toNat ≤ 20 * dimension ε * (dimension ε + 1) * n := by
  let U : ℕ := (2 * dimension ε + 4) * n
  refine ⟨U, fun a y hy v hv => ?_⟩
  have hM : 0 < log c.cutoff := log_pos <|
    (by exact_mod_cast g.anchor_prime.one_lt : (1 : ℝ) < g.anchor).trans_le g.anchor_in_window.2
  have hcoord (i) : |(v i : ℝ)| ≤ (U : ℝ) := by
    apply (le_of_mul_le_mul_right · hM)
    have hB' := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (α := ℝ) (dimension ε))
    have hJ' := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 2)
    have hN : 0 ≤ (n : ℝ) * log c.cutoff := mul_nonneg (Nat.cast_nonneg _) hM.le
    simp only [U, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    rcases hv with rfl | rfl
    · linarith [q.box_coordinate_le hy i]
    · have ht := q.translated_box_coordinate_le hy b s i
      simp only [Pi.add_apply, Int.cast_add] at ht ⊢
      linarith
  have hbounds (i) : 0 ≤ v i + (U : ℤ) ∧ v i + (U : ℤ) ≤ 2 * (U : ℤ) := by
    have hi : |v i| ≤ (U : ℤ) := by exact_mod_cast hcoord i
    rw [abs_le] at hi
    omega
  refine ⟨fun i => (hbounds i).1, ?_⟩
  calc
    ∑ i, (v i + (U : ℤ)).toNat ≤ ∑ _ : Fin (dimension ε), 2 * U :=
      Finset.sum_le_sum fun i _ => by have := (hbounds i).2; omega
    _ = dimension ε * (2 * U) := by simp
    _ = dimension ε * (4 * dimension ε + 8) * n := by dsimp [U]; ring
    _ ≤ dimension ε * (20 * (dimension ε + 1)) * n := by gcongr; omega
    _ = 20 * dimension ε * (dimension ε + 1) * n := by ring

/-- Selecting arbitrary columns from a family and its translate costs at most one
copy of the logarithmic height of the translating character in the projective height. -/
theorem logHeight_two_boxes_le {ι κ : Type*} [Finite ι] [Finite κ]
    (w : ι → ℚ) (u : ℚ) (index : κ → ι) (block : κ → Fin 2) :
    Height.logHeight (fun k => w (index k) * ![u, 1] (block k)) ≤
      Height.logHeight w + AbcTwoNinths.Basic.rationalHeight u := by
  have h := Height.logHeight_mul_le (w ∘ index) (![u, 1] ∘ block)
  refine h.trans (add_le_add (Height.logHeight_comp_le index w) ?_)
  rw [AbcTwoNinths.Basic.rationalHeight, ← Rat.logHeight₁_eq_log_max, Height.logHeight₁_eq_logHeight]
  exact Height.logHeight_comp_le block ![u, 1]

end AbcSubexp
