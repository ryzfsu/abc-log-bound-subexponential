/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.BadTupleOnset
public import Subexp.S4_TupleCounting.DistinctPrimeTuples
public import Subexp.S4_TupleCounting.FreshThirdWindow
public import Subexp.S4_TupleCounting.ShortTupleCount
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# A growing tuple of distinct primes with no short vector

The lower bound on the common cluster exceeds the loss from the short tuples.
The selected embedding has one anchor and one block of nonanchor entries
for each of the lists used in the hitting-prime argument.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real Filter

/-- Split off the common anchor of an injective tuple. -/
def anchoredTuple {n : ℕ} {Q : Type*} (f : Fin (n+1) ↪ Q) : Q × (Fin n → Q) :=
  (f 0, fun j => f j.succ)

private theorem anchoredTuple_injective {n : ℕ} {Q : Type*} :
    Function.Injective (@anchoredTuple n Q) := by
  intro f g h
  ext i
  refine Fin.cases (congrArg Prod.fst h) (fun j => ?_) i
  exact congrFun (congrArg Prod.snd h) j

private theorem eventuallyAxisLarge {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, exp (sqrt x) < (e/2) * exp (3*e*x) := by
  have hpos := ((tendsto_const_mul_atTop_of_pos he).2 tendsto_id).eventually_gt_atTop
    (log (2/e))
  filter_upwards [eventually_ge_atTop (1/e^2), hpos] with x hx hlog
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ 1/e^2).trans hx
  have hex : 1 ≤ e^2*x := by
    have := (div_le_iff₀ (sq_pos_of_pos he)).1 hx
    nlinarith
  have hs : sqrt x ≤ e*x := by
    nlinarith [Real.sq_sqrt hx0, mul_nonneg hx0 (sub_nonneg.mpr hex), mul_nonneg he.le hx0,
      Real.sqrt_nonneg x, sq_nonneg (sqrt x - e*x)]
  have he2 : 0 < e/2 := by positivity
  rw [← Real.exp_log he2, ← Real.exp_add, Real.exp_lt_exp, Real.log_div he.ne' (by norm_num)]
  rw [Real.log_div (by norm_num) he.ne'] at hlog
  change log 2 - log e < e*x at hlog
  linarith [mul_nonneg he.le hx0]

variable {ι : Type*} [Fintype ι]

private theorem tallEmbeddingOfRatio {p k : ℕ} [Fact p.Prime]
    (P : Finset ℕ) (hprime : ∀ s : P, s.val.Prime) (hodd : ∀ s : P, s.val ≠ 2)
    (hwindow : ∀ s : P, s.val * 2 < p) (hlog : ∀ s : P, 1 ≤ log s.val)
    (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) (x rate : ℝ) (hx : 1 < x)
    (hheight : exp (sqrt x) < AbcTwoNinths.Diamond.height q v) (red : AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ)
    (haxis : AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd v)) = 1)
    (lift : ℕ → ℕ → ι → ℤ)
    (hcost : ∀ i ∈ P, ∀ j ∈ P, AbcTwoNinths.Diamond.cost q (AbcTwoNinths.Diamond.roofProjection roof v (lift i j)) ≤ x/log x)
    (hlift : ∀ i ∈ P, ∀ j ∈ P,
      Additive.ofMul (AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd (lift i j)))) +
        AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0)
    (hCluster : exp (rate * x - tupleVolumeLoss x) / (4*x^2) ≤ P.card)
    (hRank : badTupleRatio 4 rate (((k+2:ℕ) + 2 : ℝ) * sqrt x) x (k+2) < 1)
    (hRatio : badTupleRatio 80 rate (((k+2:ℕ) + 2 : ℝ) * sqrt x) x (k+2) < 1) :
    ∃ f : Fin ((k+1)+1) ↪ P, ∀ (a : ℤ) (c : Fin (k+1) → ℤ), (a ≠ 0 ∨ c ≠ 0) →
      exp (sqrt x) < AbcTwoNinths.Diamond.height (tuplePrimes q Subtype.val (anchoredTuple f))
        (tupleCombination v (fun s t : P => lift s.val t.val) (anchoredTuple f) a c) := by
  classical
  let Q := ↥P
  let n := (Fintype.card Q : ℝ)
  let d := k+2
  let z := ((d : ℝ)+2) * sqrt x
  have hN : n = (P.card : ℝ) := by simp [n, Q]
  have hC : exp (rate*x - tupleVolumeLoss x)/(4*x^2) ≤ n := hN ▸ hCluster
  have hrank := tupleRankSqLtCluster (by norm_num : (0:ℝ)<4) (zero_lt_one.trans hx)
      (Real.log_pos hx).le (show 0 ≤ z by dsimp [z]; positivity) hRank
  have hdN : d^2 < Fintype.card Q := by
    exact_mod_cast (show (d:ℝ)^2 < (Fintype.card Q:ℝ) from hrank.trans_le hC)
  let candidates := (Finset.univ : Finset (Fin ((k+1)+1) ↪ Q)).image anchoredTuple
  have htotal : n^d / 2 ≤ candidates.card := by
    simpa only [candidates, Finset.card_image_of_injective _ anchoredTuple_injective,
      Finset.card_univ] using distinctTupleCountLower Q d hdN
  have hu : 0 ≤ x/log x := div_nonneg (by linarith) (Real.log_pos hx).le
  have hBudget : 10 * (8:ℝ)^(k+2) * (exp (sqrt x))^(k+4) * (1+2*(x/log x)) *
      exp (2*(x/log x)) * n^(k+1) < candidates.card := by
    apply badTupleCountLtTotal (C := 4) (z := z) (d := d) (n := n) (by norm_num)
      (zero_lt_one.trans hx) (by dsimp [d]; omega) hC _ htotal
      (by norm_num only [show (20:ℝ)*4 = 80 by norm_num]; exact hRatio)
    dsimp [d, z]
    rw [← Real.exp_nat_mul, Real.exp_add]
    push_cast
    ring_nf
    rfl
  have freshUnits (s : P) := AbcSubexp.Prerequisites.freshLabel_nonzero (p := p) (hprime s)
    (show s.val < p by have := hwindow s; omega)
  choose unit huval hlabel using freshUnits
  let prime : P ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hunit (s t : P) : AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd (lift s.val t.val))) *
      AbcTwoNinths.Diamond.quotientLabel (unit s / unit t) = 1 := by
    have hh := hlift s s.property t t.property
    rw [hlabel s, hlabel t] at hh
    change AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd (lift s.val t.val))) * AbcTwoNinths.Diamond.quotientLabel (unit s) /
      AbcTwoNinths.Diamond.quotientLabel (unit t) = 1 at hh
    simpa only [AbcTwoNinths.Diamond.quotientLabel, div_eq_mul_inv, map_mul, map_inv, mul_assoc] using hh
  obtain ⟨t, ht, h⟩ := exists_tall_prime_tuple candidates prime hprime hodd hwindow hlog
    unit huval q hq hiq roof v hv (x/log x) (exp (sqrt x)) hu
    (Real.one_le_exp_iff.mpr (sqrt_nonneg _)) hheight red haxis
    (fun s t => lift s.val t.val) (fun s t => hcost _ s.property _ t.property) hunit hBudget
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨f, h⟩

/-- Above a threshold depending only on the contact rate and number of lists,
one counted cluster supplies a common anchor and an injective family of the
required growing size. -/
theorem eventually_tall_cluster_tuple {e : ℝ} (he : 0 < e) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x : ℝ in atTop, ∀ (J : Type*) [Fintype J] (P : Finset ℕ) (R p : ℕ) [Fact p.Prime] (M : ℝ)
      (q : J → ℕ) (roof : J) (v : J → ℤ) (red : AbcTwoNinths.ExteriorE2.Exponents J →* (ZMod p)ˣ)
      (lift : ℕ → ℕ → J → ℤ),
      0 < R → 0 ≤ M → M < p/2 → P ⊆ auxiliaryFreshPrimes R M →
      exp ((e^2/10)*x - 12*x*log (3*log x)/log x)/(4*x^2) ≤ P.card →
      (∀ i, (q i).Prime) → Function.Injective q → v roof ≠ 0 →
      (e/2) * exp (3*e*x) ≤ AbcTwoNinths.Diamond.height q v → AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd v)) = 1 →
      (∀ i ∈ P, ∀ j ∈ P, AbcTwoNinths.Diamond.cost q (AbcTwoNinths.Diamond.roofProjection roof v (lift i j)) ≤ x/log x ∧
        Additive.ofMul (AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd (lift i j)))) +
          AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0) →
      ∃ f : Fin (m * ⌊x^(1/3 : ℝ)⌋₊ + 1) ↪ P,
        ∀ (a : ℤ) (c : Fin (m * ⌊x^(1/3 : ℝ)⌋₊) → ℤ), (a ≠ 0 ∨ c ≠ 0) →
        exp (sqrt x) < AbcTwoNinths.Diamond.height (tuplePrimes q Subtype.val (anchoredTuple f))
          (tupleCombination v (fun s t : P => lift s.val t.val) (anchoredTuple f) a c) := by
  have he0 : 0 < e^2/10 := by positivity
  filter_upwards [eventuallyGrowingBadTupleRatioLtOne (by norm_num : (0:ℝ)<4) he0 m,
    eventuallyGrowingBadTupleRatioLtOne (by norm_num : (0:ℝ)<80) he0 m,
    eventually_gt_atTop (1:ℝ), eventuallyAxisLarge he] with x h4 h80 hx hAx
  intro J _ P R p _ M q roof v red lift hR hM hMp hP hCluster hq hiq hv hheight haxis hlift
  have hmem (s : P) := (mem_auxiliaryFreshPrimes hR hM).1 (hP s.property)
  have hodd (s : P) : s.val ≠ 2 := by
    intro hs
    exact (hmem s).2.2.2 (hs ▸ dvd_mul_right 2 R)
  have hwindow (s : P) : s.val * 2 < p := by
    have h := (hmem s).2.2.1.trans_lt hMp
    exact_mod_cast ((lt_div_iff₀ (by norm_num : (0:ℝ)<2)).1 h)
  have hlog (s : P) : 1 ≤ log s.val := by
    have hs : 3 ≤ s.val := by have := (hmem s).1.two_le; have := hodd s; omega
    apply (show 1 = log (exp 1) by rw [log_exp]).trans_le
    exact log_le_log (exp_pos 1) (exp_one_lt_three.le.trans (by exact_mod_cast hs))
  let b := m * ⌊x^(1/3 : ℝ)⌋₊
  have hone : 1 ≤ x^(1/3 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
  have hb : 0 < b := Nat.mul_pos hm (Nat.floor_pos.mpr hone)
  have hd : ((b+1 : ℕ) : ℝ) ≤ m * x^(1/3 : ℝ) + 1 := by
    dsimp [b]
    push_cast
    gcongr
    exact Nat.floor_le (by positivity)
  have h₁ := h4 (b+1) hd
  have h₂ := h80 (b+1) hd
  let good (j : ℕ) : Prop := ∃ f : Fin (j+1) ↪ P, ∀ (a : ℤ) (c : Fin j → ℤ),
    (a ≠ 0 ∨ c ≠ 0) → exp (sqrt x) < AbcTwoNinths.Diamond.height (tuplePrimes q Subtype.val (anchoredTuple f))
      (tupleCombination v (fun s t : P => lift s.val t.val) (anchoredTuple f) a c)
  change good b
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [hk] at h₁ h₂ ⊢
  exact tallEmbeddingOfRatio P (fun s => (hmem s).1) hodd hwindow hlog q hq hiq roof v hv
    x _ hx (hAx.trans_le hheight) red haxis lift (fun i hi j hj => (hlift i hi j hj).1)
    (fun i hi j hj => (hlift i hi j hj).2) hCluster h₁ h₂

end AbcSubexp.TupleCounting
