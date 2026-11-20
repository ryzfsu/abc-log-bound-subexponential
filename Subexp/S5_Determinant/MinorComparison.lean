/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S5_Determinant.BoxMinorHeight
public import Subexp.S5_Determinant.BudgetIdentities
public import Subexp.S5_Determinant.DeterminantTail
public import Subexp.S5_Determinant.TranslationHeight

/-! # Numerical comparison for an actual box minor -/

@[expose] public section

noncomputable section
namespace AbcSubexp
open Parameters Real
variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} {g : GroupedTuple c}

private theorem log_prime_le_twice_cutoff (hx : 0 ≤ t.thirdLogRadical) (c : Contact ε t) :
    log c.prime ≤ 2 * log c.cutoff := by
  have hβ : 0 ≤ auxiliaryRate ε := by unfold auxiliaryRate; positivity
  have hp : (0 : ℝ) < c.prime := Nat.cast_pos.mpr c.prime_isPrime.pos
  have hs : sqrt (c.prime : ℝ) ≤ c.cutoff :=
    (le_max_left _ _).trans (le_mul_of_one_le_left (le_max_of_le_left (sqrt_nonneg _))
      (one_le_exp (mul_nonneg hβ hx)))
  have hlog := log_le_log (sqrt_pos.mpr hp) hs
  rw [log_sqrt hp.le] at hlog
  linarith

/-- The two translated boxes have total node weight within the combinatorial
allowance provided the displacement height is at most the depth scale. -/
theorem HittingPrime.columnWeight_le_depth (q : HittingPrime g) (hε : 0 < ε)
    (hx : 0 ≤ t.thirdLogRadical) (hn : 0 < c.depth) (a : ℤ) (s : Fin (dimension ε) → ℤ)
    (hJ : AbcTwoNinths.Basic.rationalHeight (q.character a s) ≤ (c.depth : ℝ) * log c.prime) :
    c.radius + ∑ i, (s i).natAbs ≤ 20 * dimension ε * (dimension ε + 1) * c.depth := by
  let m := dimension ε
  let n := c.depth
  let L := log c.cutoff
  have hp : 0 < log (c.prime : ℝ) := log_pos (by exact_mod_cast c.prime_isPrime.one_lt)
  have ht := log_prime_le_twice_cutoff hx c
  have hL : 0 < L := by dsimp [L]; linarith
  obtain ⟨hA, hw⟩ := c.transverseBudget_width_pos hε hn
  have he := exponentPos hε
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have heq := c.width_height_add_transverse hε
  have hscale : ((m : ℝ) + 1) * c.transverseBudget ≤ (n : ℝ) * log c.prime := by
    dsimp [m,n]
    nlinarith only [heq, mul_nonneg hw.le hh.le,
      mul_nonneg (mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) c.depth)) hp.le]
  have ht' : (n : ℝ) * log c.prime ≤ 2 * n * L := by
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℝ) n)
  have hr : c.radius ≤ 2 * n := by
    have hf : (c.shift : ℝ) ≤ c.transverseBudget / L :=
      Nat.floor_le (div_nonneg hA.le hL.le)
    have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL).mp hf)
      (show 0 ≤ (m : ℝ) + 1 by positivity)
    have h := (le_of_eq (mul_assoc ((m : ℝ) + 1) (c.shift : ℝ) L)).trans
      (hmul.trans (hscale.trans ht'))
    have hh' := (mul_le_mul_iff_left₀ hL).mp h
    unfold Contact.radius
    exact_mod_cast hh'
  have hs (i) : (s i).natAbs ≤ 4 * n := by
    have hv := q.displacement_coordinate_le a s i
    have hh' : |(s i : ℝ)| * L ≤ (4 * n : ℝ) * L := by
      nlinarith only [hv, hJ, ht']
    have hab := (mul_le_mul_iff_left₀ hL).mp hh'
    exact_mod_cast (show ((s i).natAbs : ℝ) ≤ 4 * n by simpa using hab)
  have hsum : (∑ i, (s i).natAbs) ≤ m * (4 * n) := by
    simpa [m] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hs i)
  have hm : 1 ≤ dimension ε := dimensionPos hε
  have hcoef : 2 + m * 4 ≤ 20 * m * (m + 1) := by
    dsimp [m]; nlinarith only [hm, Nat.zero_le (dimension ε ^ 2)]
  calc
    _ ≤ 2 * n + m * (4 * n) := Nat.add_le_add hr hsum
    _ = (2 + m * 4) * n := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcoef

/-- The height allowance of the selected columns before adding the binomial
and permutation contributions. -/
def Contact.selectedHeightAllowance (c : Contact ε t) (J : ℝ) : ℝ :=
  c.width * AbcTwoNinths.Basic.rationalHeight c.source + ((dimension ε : ℝ) + 1) * c.transverseBudget +
    c.width / 2 * (exponent ε / 50 * AbcTwoNinths.Basic.rationalHeight c.source) +
    (dimension ε : ℝ)^2 * c.transverseBudget / log c.cutoff * (2 * t.thirdLogRadical / log t.thirdLogRadical + log 3) + J

private theorem heightAllowance_le (hε : 0 < ε) (hx : 1 < t.thirdLogRadical) (hn : 0 < c.depth)
    (J : ℝ) :
    let S := (c.depth : ℝ) * log c.prime
    let W := 3 * (dimension ε : ℝ)^2 * (t.thirdLogRadical / log t.thirdLogRadical + log 3) / log c.cutoff
    c.selectedHeightAllowance J ≤ (1 - exponent ε / 5 + exponent ε / 50 + W + J / S) * S := by
  dsimp only
  let S := (c.depth : ℝ) * log c.prime
  let m : ℝ := dimension ε
  let A := c.transverseBudget
  let L := log c.cutoff
  let u := t.thirdLogRadical / log t.thirdLogRadical
  let e := exponent ε
  have he : 0 < e := exponentPos hε
  have hlog : 0 < log (c.prime : ℝ) := log_pos (by exact_mod_cast c.prime_isPrime.one_lt)
  have hS : 0 < S := mul_pos (Nat.cast_pos.mpr hn) hlog
  have hL : 0 < L := by
    have h := log_prime_le_twice_cutoff (zero_lt_one.trans hx).le c
    dsimp [L]; linarith
  have hu : 0 ≤ u := div_nonneg (zero_lt_one.trans hx).le (log_pos hx).le
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hln : 0 ≤ log 3 := log_nonneg (by norm_num)
  obtain ⟨hA, hw⟩ := c.transverseBudget_width_pos hε hn
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have heq : c.width * AbcTwoNinths.Basic.rationalHeight c.source + (m + 1) * A = (1 - e / 5) * S := by
    simpa only [S, mul_assoc] using c.width_height_add_transverse hε
  have heq' : c.width * AbcTwoNinths.Basic.rationalHeight c.source + (m + 1) * A ≤ S := by
    nlinarith only [heq, mul_nonneg he.le hS.le]
  have hAS : A ≤ S := by
    nlinarith only [heq', mul_nonneg hm hA.le, mul_nonneg hw.le hh.le]
  have hwS : c.width * AbcTwoNinths.Basic.rationalHeight c.source ≤ S := by
    nlinarith only [heq', mul_nonneg (add_nonneg hm zero_le_one) hA.le]
  have hreal : c.width / 2 * (e / 50 * AbcTwoNinths.Basic.rationalHeight c.source) ≤ e / 50 * S := by
    nlinarith only [mul_le_mul_of_nonneg_left hwS he.le, mul_nonneg he.le hS.le]
  have ht : m^2 * A / L * (2 * u + log 3) ≤ (3 * m^2 * (u + log 3) / L) * S := by
    calc
      _ = (m^2 / L) * ((2 * u + log 3) * A) := by ring
      _ ≤ (m^2 / L) * ((3 * (u + log 3)) * S) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (by linarith) hAS hA.le (by positivity)) (by positivity)
      _ = _ := by ring
  have hJ := div_mul_cancel₀ J hS.ne'
  change c.width * AbcTwoNinths.Basic.rationalHeight c.source + (m+1)*A + c.width/2*(e/50*AbcTwoNinths.Basic.rationalHeight c.source) +
    m^2*A/L*(2*t.thirdLogRadical/log t.thirdLogRadical + log 3) + J ≤ (1-e/5+e/50+3*m^2*(u+log 3)/L+J/S)*S
  rw [heq, show 2 * t.thirdLogRadical / log t.thirdLogRadical = 2 * u by dsimp [u]; ring]
  linarith only [hreal, ht, hJ]

private theorem entropy_scale {N B n ℓ T F : ℝ} (hN : 0 ≤ N) (hB : 0 < B)
    (hn : 0 < n) (hℓ : 0 < ℓ) (hT : T ≤ F * n) :
    N * (T * log 2 + log N) ≤
      B * ((N/B) * (F * log 2 + log N/n) / ℓ) * (n*ℓ) := by
  calc
    _ ≤ N * (F*n*log 2 + log N) := by gcongr
    _ = _ := by field_simp

/-- Beyond a fixed exponent-dependent threshold, the native local depth and
single global column-height allowance force each selected box minor to vanish. -/
theorem eventual_boxMinor_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ (t : AbcTwoNinths.Basic.Triple) (c : Contact ε t), X ≤ t.thirdLogRadical →
      ∀ (g : GroupedTuple c) (q : HittingPrime g) (b : BoxData q)
        (a : ℤ) (s : Fin (dimension ε) → ℤ),
      AbcTwoNinths.Basic.rationalHeight (q.character a s) ≤ (1 + 2 * (dimension ε : ℝ)) *
        sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) * AbcTwoNinths.Basic.rationalHeight c.source →
      let I := simplexRows (dimension ε) c.depth
      let J := simplexRows (dimension ε) ⌈degreeMargin ε * c.depth⌉₊
      ∀ [Nonempty (↥I ⊕ ↥J)] (f : (↥I ⊕ ↥J) ↪ (q.BoxPoint ⊕ q.BoxPoint)),
        let Δ := ((q.boxMinorMatrix b a s (HittingPrime.columnOrigin s) I J).submatrix id f).det
        let γ := fun j => q.columnCharacter b a s (f j)
        (Δ ≠ 0 → ((∑ k ∈ J, (c.depth - (∑ i, k i)) : ℕ) : ℤ) ≤ padicValRat c.prime Δ) →
        minorRealBudget γ + (∑ p ∈ minorCharacterPrimes c.prime γ,
          (minorPrimeBudget γ p : ℝ) * log p) ≤ c.selectedHeightAllowance (AbcTwoNinths.Basic.rationalHeight (q.character a s)) →
        Δ = 0 := by
  obtain ⟨X, hX⟩ := eventual_determinant_errors hε
  refine ⟨max 2 X, ?_⟩
  intro t c hx g q b a s hJ
  dsimp only
  intro inst f hd hcost
  let e := exponent ε
  let m := dimension ε
  let n := c.depth
  let ℓ := log (c.prime : ℝ)
  let S := (n : ℝ)*ℓ
  let I := simplexRows m n
  let J := simplexRows m ⌈degreeMargin ε * n⌉₊
  let K : ℝ := J.card
  let N : ℝ := I.card + J.card
  let H := AbcTwoNinths.Basic.rationalHeight (q.character a s)
  let W := 3 * (m : ℝ)^2 * (t.thirdLogRadical / log t.thirdLogRadical + log 3) / log c.cutoff
  let E := ∑ k ∈ J, (n - (∑ i, k i))
  have he := exponentPos hε
  have he' := (exponentBounds hε).2.2
  have hm : 0 < degreeMargin ε := by unfold degreeMargin; positivity
  have hm' : degreeMargin ε ≤ 1 := by unfold degreeMargin; linarith
  have hℓ : 0 < ℓ := log_pos (by exact_mod_cast c.prime_isPrime.one_lt)
  have hh : 0 < AbcTwoNinths.Basic.rationalHeight c.source :=
    (mul_pos (div_pos he zero_lt_two) (exp_pos _)).trans_le c.axial_height_lower
  have hS : 0 < S := (mul_pos (mul_pos zero_lt_two he) hh).trans c.depth_share
  have hn : 0 < n := by by_contra! hz; simp [S, Nat.eq_zero_of_le_zero hz] at hS
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hK : 0 < K := Nat.cast_pos.mpr (card_simplexRows_pos
    (Nat.ceil_pos.mpr (mul_pos hm hn')))
  have hx1 : 1 < t.thirdLogRadical := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ((le_max_left _ _).trans hx)
  obtain ⟨hent, htrans, hdisp⟩ := hX t c ((le_max_right _ _).trans hx)
  have hJsmall := hdisp H hJ
  have hH : H ≤ S := by
    apply (div_le_one hS).mp
    exact hJsmall.le.trans (by linarith)
  have hT := q.columnWeight_le_depth hε (zero_lt_one.trans hx1).le hn a s hH
  have hTR : ((c.radius + ∑ i, (s i).natAbs : ℕ) : ℝ) ≤
      20 * (m : ℝ) * (m + 1) * n := by exact_mod_cast hT
  have hcomb : N * (((c.radius + ∑ i, (s i).natAbs : ℕ) : ℝ)*log 2 + log N) ≤
      K*c.determinantEntropy*S := by
    have ha := entropy_scale (N := N) (by dsimp [N]; positivity) hK hn' hℓ hTR
    simpa only [Contact.determinantEntropy, Nat.cast_add, I, J, N, K, m, n, S, ℓ] using ha
  have hres : K * ((1 - degreeMargin ε) * n) < (E : ℝ) := by
    simpa only [E, Nat.cast_sum] using simplexRows_residual_sum_gt (m := m) hn hm hm'
  have hlow : K*(1-degreeMargin ε)*S < (E : ℝ)*ℓ := by
    simpa only [S, mul_assoc] using mul_lt_mul_of_pos_right hres hℓ
  by_contra hd'
  have hhgt := q.boxMinor_depth_height b a s I J f E hd' (hd hd')
  have hbudget := (heightAllowance_le (c := c) hε hx1 hn H)
  let δ := e/50 + W + H/S + c.determinantEntropy
  have hδ : δ < exponent ε / 10 := by
    change e/50 + W + H/S + c.determinantEntropy < e/10
    change W < e/40 at htrans
    change H/S < e/40 at hJsmall
    change c.determinantEntropy < e/40 at hent
    linarith
  apply Contact.determinant_budget_contradiction hK hS hlow _ hδ
  have hglobal : (E : ℝ)*ℓ ≤ K*c.selectedHeightAllowance H +
      N*(((c.radius + ∑ i, (s i).natAbs : ℕ) : ℝ)*log 2 + log N) := by
    dsimp only at hhgt
    push_cast at hhgt ⊢
    exact hhgt.trans (add_le_add (mul_le_mul_of_nonneg_left hcost hK.le) le_rfl)
  calc
    _ ≤ _ := hglobal
    _ ≤ K*((1-e/5+e/50+W+H/S)*S) + K*c.determinantEntropy*S :=
      add_le_add (mul_le_mul_of_nonneg_left hbudget hK.le) hcomb
    _ = _ := by dsimp only [δ,e]; ring

end AbcSubexp
