/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S3_ExteriorE1.ActualPlaneContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.OrientedContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.OrderedRealContact
public import AbcTwoNinths.Paper.S3_ExteriorE1.RealContactFromSlab

/-!
# Real contact at any positive exponential rate

On the ordered high-height tail, the logarithm of the real ratio `c/a` is
at most any prescribed positive fraction of the height. The onset depends
on the rate and the allowed fraction.

## Main results
* `AbcSubexp.ContactPrime.realContact_of_posRate`
-/

@[expose] public section

namespace AbcSubexp.ContactPrime


private structure SlabBounds (t : AbcTwoNinths.Basic.Triple) (κ : ℝ) : Prop where
  onset : Real.exp 4 ≤ t.thirdLogRadical
  height : 1 < t.logHeight
  width : t.thirdLogRadical / Real.log t.thirdLogRadical ≤ t.logHeight
  scale : Real.log (9 * t.thirdLogRadical ^ 2 / κ) ≤ Real.log t.logHeight / 8
  rank (d : ℕ) (hd : (d : ℝ) ≤ 12 * t.thirdLogRadical / Real.log t.thirdLogRadical) :
    d * Real.log (1 + 3 * Real.log t.thirdLogRadical) ≤ Real.log t.logHeight / 8

private theorem two_le_support (t : AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hH : 1 < t.logHeight) :
    2 ≤ (AbcTwoNinths.Basic.supp t).card := by
  by_contra! hs
  rcases AbcTwoNinths.ExteriorE1.rankLeTwoShapes t hab (by omega) with h | ⟨p, q, m, n, hp, hq, hne, hm, hn, hb, hc⟩
  · rw [AbcTwoNinths.Basic.Triple.logHeight, h.2.2, Nat.cast_ofNat] at hH
    linarith [Real.log_two_lt_d9]
  · unfold AbcTwoNinths.Basic.supp at hs
    rw [hb, hc, Nat.primeFactors_prime_pow hm.ne' hp, Nat.primeFactors_prime_pow hn.ne' hq] at hs
    simp [hne] at hs

private theorem primitivePivot (t : AbcTwoNinths.Basic.Triple) (hrank : 2 ≤ (AbcTwoNinths.Basic.supp t).card) :
    ∃ (w : AbcTwoNinths.Basic.supp t → ℤ) (r : AbcTwoNinths.Basic.supp t),
      AbcTwoNinths.Basic.PrimitiveIn ⊤ w ∧
      (∀ i, AbcTwoNinths.ExteriorE1.quotientVec t i = (AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * w i) ∧
      (∀ i, |w i| ≤ |w r|) ∧
      t.logHeight / ((AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical)) ≤ |(w r : ℝ)| := by
  classical
  have hg := AbcTwoNinths.ExteriorE1.quotientGcdPos t
  have : Nonempty (AbcTwoNinths.Basic.supp t) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (AbcTwoNinths.Basic.supp t).card by omega)
    exact ⟨⟨i, hi⟩⟩
  obtain ⟨w, hw⟩ := AbcTwoNinths.ExteriorE1.quotientFromGcd t
  let a : AbcTwoNinths.Basic.supp t → ℝ := fun i => Real.log (i.val : ℝ)
  have ha (i : AbcTwoNinths.Basic.supp t) : 0 < a i := by
    apply Real.log_pos
    exact_mod_cast (AbcTwoNinths.Basic.suppPrime t i.property).one_lt
  have hH : t.logHeight ≤ ∑ i, a i * |(AbcTwoNinths.ExteriorE1.quotientVec t i : ℝ)| := by
    rw [AbcTwoNinths.ExteriorE1.quotientSignedHeight t]
    exact AbcTwoNinths.ExteriorE1.signedHeightLeWeightedAbs a _ fun i => (ha i).le
  obtain ⟨r, hr, _, hlow⟩ := AbcTwoNinths.ExteriorE1.existsPivot a (AbcTwoNinths.ExteriorE1.quotientVec t) w (AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ)
    (by exact_mod_cast hg.ne') ha hw t.logHeight hH
  have hgR : 0 < (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by exact_mod_cast hg
  push_cast at hlow
  rw [abs_of_pos hgR] at hlow
  have hsum : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hx : 0 < 3 * t.thirdLogRadical := hsum.trans_le (AbcTwoNinths.ExteriorE1.quotientSupportWeight t)
  refine ⟨w, r, AbcTwoNinths.ExteriorE1.quotientPrimitive t w hw, hw, hr,
    (div_le_iff₀ (mul_pos hgR hx)).mpr ?_⟩
  exact ((div_le_iff₀ (mul_pos hgR hsum)).mp hlow).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (AbcTwoNinths.ExteriorE1.quotientSupportWeight t) hgR.le)
      (abs_nonneg _))

private theorem positivePivot (t : AbcTwoNinths.Basic.Triple) (hrank : 2 ≤ (AbcTwoNinths.Basic.supp t).card)
    (hH : 0 < t.logHeight) (hx : 0 < 3 * t.thirdLogRadical) :
    ∃ (v : AbcTwoNinths.Basic.supp t → ℤ) (s : ℤ) (r : AbcTwoNinths.Basic.supp t), (s = 1 ∨ s = -1) ∧
      (∀ i, AbcTwoNinths.ExteriorE1.quotientVec t i = (AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * (s * v i)) ∧
      AbcTwoNinths.Basic.PrimitiveIn ⊤ v ∧ 0 < v r ∧ (∀ i, |v i| ≤ v r) ∧
      t.logHeight / ((AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical)) ≤ (v r : ℝ) ∧
      (v r : ℝ) ≤ 2 * t.logHeight := by
  obtain ⟨w, r, hp, hw, hmax, hlo⟩ := primitivePivot t hrank
  have hg := AbcTwoNinths.ExteriorE1.quotientGcdPos t
  have hgR : (1 : ℝ) ≤ (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by exact_mod_cast hg
  have hwr : w r ≠ 0 := by
    intro hz
    simp [hz] at hlo
    exact (not_le_of_gt (div_pos hH (mul_pos (by linarith) hx))) hlo
  obtain ⟨v, s, hs, hv, hvr, hpos, hmax'⟩ := AbcTwoNinths.ExteriorE1.normalizePivot w r hwr hmax
  have hvprim : AbcTwoNinths.Basic.PrimitiveIn ⊤ v := by
    intro n u _ hu
    apply hp n (s • u) (by simp)
    funext i
    have hi := congrFun hu i
    change (n : ℤ) * u i = v i at hi
    change (n : ℤ) * (s * u i) = w i
    rw [hv i, ← hi]
    ring
  have hvR : (v r : ℝ) = |(w r : ℝ)| := by exact_mod_cast hvr
  refine ⟨v, s, r, hs, fun i => by rw [hw, hv], hvprim, hpos, hmax',
    by rwa [hvR], ?_⟩
  have hlog : (1 : ℝ) / 2 ≤ Real.log (r.val : ℝ) := by
    have hp2 : (2 : ℝ) ≤ (r.val : ℝ) := by
      exact_mod_cast (AbcTwoNinths.Basic.suppPrime t r.property).two_le
    exact (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hp2)
  have he := AbcTwoNinths.ExteriorE1.quotientCoordinateHeight t r
  rw [hw, Int.cast_mul, abs_mul] at he
  push_cast at he
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ)), ← hvR] at he
  have hpv : (0 : ℝ) ≤ (v r : ℝ) := by exact_mod_cast hpos.le
  have hfactor : (1 : ℝ) / 2 ≤ Real.log (r.val : ℝ) * (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log (r.val : ℝ) by linarith)
      (sub_nonneg.mpr hgR)]
  nlinarith [mul_le_mul_of_nonneg_right hfactor hpv]

private theorem slabBudget (κ : ℝ) (hκ : 0 < κ)
    (t : AbcTwoNinths.Basic.Triple) (r : AbcTwoNinths.Basic.supp t) [Nonempty {i : AbcTwoNinths.Basic.supp t // i ≠ r}]
    (m : ℝ) (hm : 0 < m) (hlo : κ * t.logHeight / (3 * t.thirdLogRadical) ≤ m) (hhi : m ≤ 2 * t.logHeight)
    (bounds : SlabBounds t κ) :
    let T := t.thirdLogRadical / Real.log t.thirdLogRadical
    let d := Fintype.card {i : AbcTwoNinths.Basic.supp t // i ≠ r}
    let ε := (3 * T / m) * (1 + 3 * Real.log t.thirdLogRadical) ^ d
    1 ≤ T ∧ T ≤ t.logHeight ∧ 0 < ε ∧ ε < T ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
    1 / t.logHeight < ε ∧ (⌈T / ε⌉₊ : ℝ) *
      (∏ i : {i : AbcTwoNinths.Basic.supp t // i ≠ r},
        (⌈(d : ℝ) * Real.log (i.val.val : ℝ) / T⌉₊ : ℝ)) < m := by
  classical
  let x := t.thirdLogRadical
  let T := x / Real.log x
  let α := {i : AbcTwoNinths.Basic.supp t // i ≠ r}
  let d := Fintype.card α
  let a : α → ℝ := fun i => Real.log (i.val.val : ℝ)
  let B := 1 + 3 * Real.log x
  have ha (i : α) : 0 < a i := Real.log_pos (by
    exact_mod_cast (AbcTwoNinths.Basic.suppPrime t i.val.property).one_lt)
  have hxp : 0 < x := (Real.exp_pos _).trans_le bounds.onset
  have hy : 4 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos 4) bounds.onset
  have hyp : 0 < Real.log x := by linarith
  have hT : 1 ≤ T := (le_div_iff₀ hyp).2 (by
    linarith [Real.log_le_sub_one_of_pos hxp])
  have hTp : 0 < T := by linarith
  have hTx : T ≤ x := (div_le_iff₀ hyp).2 (by nlinarith)
  have hH := bounds.height
  have hd : (d : ℝ) ≤ 12 * x / Real.log x := by
    have hc := Fintype.card_le_of_injective (fun i : α => i.val) Subtype.val_injective
    exact (show (d : ℝ) ≤ ((AbcTwoNinths.Basic.supp t).card : ℝ) by simpa using (Nat.cast_le (α := ℝ)).mpr hc).trans
      (AbcTwoNinths.ExteriorE1.tripleRankBound t bounds.onset)
  have hsum : (∑ i, a i) ≤ 3 * x := by
    let f : AbcTwoNinths.Basic.supp t → ℝ := fun i => Real.log (i.val : ℝ)
    have hf (i : AbcTwoNinths.Basic.supp t) : 0 ≤ f i := Real.log_nonneg (by
      exact_mod_cast (AbcTwoNinths.Basic.suppPrime t i.property).one_le)
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : AbcTwoNinths.Basic.supp t => i ≠ r) f
    have hnon : 0 ≤ ∑ i : {i : AbcTwoNinths.Basic.supp t // ¬ i ≠ r}, f i.val :=
      Finset.sum_nonneg fun i _ => hf i.val
    exact (show (∑ i, a i) ≤ ∑ i, f i by
      change (∑ i : α, f i.val) ≤ _
      rw [← hsplit]
      exact le_add_of_nonneg_right hnon).trans (AbcTwoNinths.ExteriorE1.quotientSupportWeight t)
  have hpen := AbcTwoNinths.ExteriorE1.slabPenalty t.logHeight T m B x κ d hH hTp hTx hκ hlo
    bounds.scale (bounds.rank d hd)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  obtain ⟨he, heT, helog, helo⟩ := AbcTwoNinths.ExteriorE1.slabLogBudget t.logHeight T m B d hH hT hm hhi hB hpen
  have hrewrite : 1 + 3 * x / T = B := by
    dsimp [T, B]; field_simp [hxp.ne', hyp.ne']
  have hcap := AbcTwoNinths.ExteriorE1.strictCapacity a ha T (3 * x) m hTp (by positivity) hm hsum
  dsimp only at hcap
  rw [hrewrite] at hcap
  exact ⟨hT, bounds.width, he, heT, helog, helo, hcap heT⟩

private theorem integerSlab (κ : ℝ) (hκ : 0 < κ)
    (t : AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hf : ¬ AbcTwoNinths.Statement.RealContactBound κ t) (bounds : SlabBounds t κ) :
    ∃ (u w : AbcTwoNinths.Basic.supp t → ℤ) (r : AbcTwoNinths.Basic.supp t) (ε : ℝ) (s : ℤ),
      (s = 1 ∨ s = -1) ∧ (∀ i, AbcTwoNinths.ExteriorE1.quotientVec t i = (AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * (s * w i)) ∧
      AbcTwoNinths.Basic.PrimitiveIn ⊤ w ∧ 0 < w r ∧ |u r| < w r ∧ (∀ i, |w i| ≤ w r) ∧
      ¬ (∃ z : ℝ, ∀ i, (u i : ℝ) = z * (w i : ℝ)) ∧
      1 / t.logHeight < ε ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
      (∑ i : {i : AbcTwoNinths.Basic.supp t // i ≠ r},
        |Real.log (i.val.val : ℝ) *
        ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))|) ≤
        t.thirdLogRadical / Real.log t.thirdLogRadical ∧
      |∑ i : {i : AbcTwoNinths.Basic.supp t // i ≠ r}, Real.log (i.val.val : ℝ) *
        ((u i.val : ℝ) - (w i.val : ℝ) / (w r : ℝ) * (u r : ℝ))| < ε := by
  classical
  have hxp : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le bounds.onset
  have hcard := two_le_support t hab bounds.height
  have hg := AbcTwoNinths.ExteriorE1.quotientGcdPos t
  have hgk := AbcTwoNinths.ExteriorE1.quotientGcdLtOfNotE1 t κ hκ hf
  obtain ⟨w, s, r, hs, hw, hprim, hwr, hmax, hlo, hhi⟩ :=
    positivePivot t hcard (by linarith [bounds.height]) (by positivity)
  let α := {i : AbcTwoNinths.Basic.supp t // i ≠ r}
  have : Nontrivial (AbcTwoNinths.Basic.supp t) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [Fintype.card_coe] using (show 1 < (AbcTwoNinths.Basic.supp t).card by omega))
  obtain ⟨i, hi⟩ := exists_ne r
  have : Nonempty α := ⟨⟨i, hi⟩⟩
  have hm : (0 : ℝ) < w r := by exact_mod_cast hwr
  have hgR : (0 : ℝ) < AbcTwoNinths.ExteriorE1.quotientGcd t := by exact_mod_cast hg
  have hlow : κ * t.logHeight / (3 * t.thirdLogRadical) ≤ (w r : ℝ) := by
    have hga := (lt_div_iff₀ hκ).mp hgk
    have hw' := (div_le_iff₀ (by positivity : 0 < (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) * (3 * t.thirdLogRadical))).mp hlo
    apply (div_le_iff₀ (by positivity : 0 < 3 * t.thirdLogRadical)).mpr
    calc
      κ * t.logHeight ≤ (κ * (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ)) * ((w r : ℝ) * (3 * t.thirdLogRadical)) := by
        convert mul_le_mul_of_nonneg_left hw' hκ.le using 1
        ring
      _ ≤ _ := by
        have hga' : κ * (AbcTwoNinths.ExteriorE1.quotientGcd t : ℝ) ≤ 1 := by linarith
        exact mul_le_of_le_one_left (by positivity) hga'
  let T := t.thirdLogRadical / Real.log t.thirdLogRadical
  let a : α → ℝ := fun i => Real.log (i.val.val : ℝ)
  let d := Fintype.card α
  let ε := (3 * T / (w r : ℝ)) * (1 + 3 * Real.log t.thirdLogRadical) ^ d
  let N : α → ℕ := fun i => ⌈(d : ℝ) * a i / T⌉₊
  let M : ℕ := ⌈T / ε⌉₊
  obtain ⟨hT, _, he, _, helog, helo, hc⟩ :=
    slabBudget κ hκ t r (w r : ℝ) hm hlow hhi bounds
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha (i : α) : 0 < a i := Real.log_pos (by
    exact_mod_cast (AbcTwoNinths.Basic.suppPrime t i.val.property).one_lt)
  obtain ⟨hN, _, hbudget⟩ := AbcTwoNinths.ExteriorE1.ceilCapacity a ha T hTp
  have hM : 0 < M := Nat.ceil_pos.mpr (div_pos hTp he)
  have hc' : M * (∏ i, N i) < (w r).toNat := by
    have hcast : ((w r).toNat : ℝ) = (w r : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hwr.le
    apply (Nat.cast_lt (α := ℝ)).mp
    rw [Nat.cast_mul, Nat.cast_prod, hcast]
    exact hc
  obtain ⟨u, _, hur, hcoord, hsum, hind⟩ :=
    AbcTwoNinths.ExteriorE1.integerSlab r w hwr hprim N hN hM a ha T hTp hbudget hc'
  refine ⟨u, w, r, ε, s, hs, hw, hprim, hwr, hur, hmax, hind, helo, helog, ?_, ?_⟩
  · exact (Finset.sum_le_sum fun i _ => (hcoord i).le).trans hbudget
  · have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    refine hsum.trans_le ((div_le_iff₀ hMR).mpr ?_)
    have := (div_le_iff₀ he).mp (Nat.le_ceil (T / ε))
    change T ≤ (M : ℝ) * ε at this
    rwa [mul_comm]

private theorem reducedLogSlab (κ : ℝ) (hκ : 0 < κ)
    (t : AbcTwoNinths.Basic.Triple) (hab : t.a ≤ t.b) (hf : ¬ AbcTwoNinths.Statement.RealContactBound κ t) (bounds : SlabBounds t κ)
    (hcontact : Real.log ((t.c : ℝ) / t.b) ≤ 1 / t.logHeight) :
    ∃ (x y : AbcTwoNinths.Basic.supp t → ℤ) (a b : ℤ) (d ε : ℝ),
      0 < d ∧ d ≤ t.thirdLogRadical / Real.log t.thirdLogRadical ∧ 0 < ε ∧ Real.log t.logHeight / 2 ≤ -Real.log ε ∧
      (∀ m n : ℤ, m • x + n • y = 0 → m = 0 ∧ n = 0) ∧
      AbcTwoNinths.ExteriorE1.quotientVec t = a • x + b • y ∧
      let A := fun i : AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)
      let L₁ := AbcTwoNinths.ExteriorE1.signedHeight A x
      let L₂ := AbcTwoNinths.ExteriorE1.signedHeight A y
      L₁ * L₂ ≤ 4 * t.logHeight * d ∧ |(a : ℝ)| * L₁ ≤ 3 * t.logHeight ∧ |(b : ℝ)| * L₂ ≤ 2 * t.logHeight ∧
      |∑ i, A i * (x i : ℝ)| ≤ 7 * L₁ * ε / d ∧
      |∑ i, A i * (y i : ℝ)| ≤ 7 * L₂ * ε / d := by
  classical
  obtain ⟨u, w, r, ε, sign, hs, hw, hprim, hr, hur, _, hind, helo, helog, hsum, hlog⟩ :=
    integerSlab κ hκ t hab hf bounds
  have hH : 0 < t.logHeight := zero_lt_one.trans bounds.height
  have hTH := bounds.width
  let g : ℤ := (AbcTwoNinths.ExteriorE1.quotientGcd t : ℤ) * sign
  have hs0 : sign ≠ 0 := by rcases hs with h | h <;> simp [h]
  have hg : g ≠ 0 := mul_ne_zero (by exact_mod_cast (AbcTwoNinths.ExteriorE1.quotientGcdPos t).ne') hs0
  have hw' (i : AbcTwoNinths.Basic.supp t) : AbcTwoNinths.ExteriorE1.quotientVec t i = g * w i := by rw [hw]; simp only [g, mul_assoc]
  let A := fun i : AbcTwoNinths.Basic.supp t => Real.log (i.val : ℝ)
  let p : ℝ := (u r : ℝ) / ((w r : ℝ) * (g : ℝ))
  have hwR : 0 < (w r : ℝ) := by exact_mod_cast hr
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have hgp : (1 : ℝ) ≤ |(g : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |g| by have := abs_pos.mpr hg; omega)
  have hp : |p| ≤ 1 := by
    dsimp [p]
    rw [abs_div, abs_mul, abs_of_pos hwR, div_le_iff₀ (by positivity), one_mul]
    have h : |(u r : ℝ)| < (w r : ℝ) := by exact_mod_cast hur
    exact h.le.trans (by simpa using mul_le_mul_of_nonneg_left hgp hwR.le)
  let R := fun i : AbcTwoNinths.Basic.supp t => (u i : ℝ) - p * ((g * w i : ℤ) : ℝ)
  have hR (i : AbcTwoNinths.Basic.supp t) : R i = (u i : ℝ) - (w i : ℝ) / (w r : ℝ) * (u r : ℝ) := by
    change (u i : ℝ) - ((u r : ℝ) / ((w r : ℝ) * (g : ℝ))) * ((g * w i : ℤ) : ℝ) = _
    simp only [Int.cast_mul]
    generalize (g : ℝ) = G at hgR ⊢
    field_simp [hgR, hwR.ne']
  have hR0 : R r = 0 := by rw [hR, div_self hwR.ne', one_mul, sub_self]
  have hhs : AbcTwoNinths.ExteriorE1.height A (fun i => ((g * w i : ℤ) : ℝ)) = t.logHeight := by
    simp_rw [← hw']
    exact (AbcTwoNinths.ExteriorE1.quotientSignedHeight t).symm
  have hres : AbcTwoNinths.ExteriorE1.height A R ≤ t.thirdLogRadical / Real.log t.thirdLogRadical := by
    refine (AbcTwoNinths.ExteriorE1.weightAbsLe A R (fun i => Real.log_nonneg (by
      exact_mod_cast (AbcTwoNinths.Basic.suppPrime t i.property).one_le))).trans ?_
    rw [AbcTwoNinths.ExteriorE1.sumExcludePivot r _ (by rw [hR0, mul_zero, abs_zero])]
    simpa only [hR] using hsum
  have hsource : |AbcTwoNinths.ExteriorE1.weightedLog A (fun i => ((g * w i : ℤ) : ℝ))| ≤ ε := by
    simp_rw [← hw']
    rw [AbcTwoNinths.ExteriorE1.quotientWeightedLog, abs_of_nonneg]
    · exact hcontact.trans helo.le
    · apply Real.log_nonneg
      have hb : (0 : ℝ) < t.b := by exact_mod_cast t.bpos
      apply (le_div_iff₀ hb).2
      rw [one_mul]
      exact_mod_cast (show t.b ≤ t.c by have := t.add; omega)
  have htarget : |AbcTwoNinths.ExteriorE1.weightedLog A R| ≤ ε := by
    rw [AbcTwoNinths.ExteriorE1.weightedLogApply, AbcTwoNinths.ExteriorE1.sumExcludePivot r _ (by rw [hR0, mul_zero])]
    exact (by simpa only [hR] using hlog.le)
  obtain ⟨x, y, a, b, d, hd, hdT, hi, he, hprod, ha, hb, h₁, h₂⟩ :=
    AbcTwoNinths.ExteriorE1.reducedLogSlab Subtype.val w u r hr.ne' (fun i => AbcTwoNinths.Basic.suppPrime t i.property)
      (AbcTwoNinths.ExteriorE1.primitiveRealMultiple w r hr.ne' hprim) hind g hg p _ ε hp (by rwa [hhs])
      hres hsource htarget
  rw [hhs] at hprod ha hb
  have heq : AbcTwoNinths.ExteriorE1.quotientVec t = g • w := funext hw'
  rw [AbcTwoNinths.ExteriorE1.weightedLogApply] at h₁ h₂
  exact ⟨x, y, a, b, d, ε, hd, hdT, (by positivity : 0 < 1 / t.logHeight).trans helo,
    helog, hi, heq.trans he, hprod, ha, hb, h₁, h₂⟩

/-- At any positive height rate, ordered triples eventually satisfy the prescribed real margin. -/
theorem realContact_of_posRate (beta ν : ℝ) (hbeta : 0 < beta) (hν : 0 < ν) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ t : AbcTwoNinths.Basic.Triple, t.a ≤ t.b → X ≤ t.thirdLogRadical →
      Real.exp (beta * t.thirdLogRadical) ≤ t.logHeight → AbcTwoNinths.Statement.RealContactBound ν t := by
  let θ := ν / 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let X := max (Real.exp 4) (max (2 / beta ^ 2)
    (max (Real.exp (320000 * 2048 / (θ * beta))) (max (48 / beta)
      (max (320000 * 13824 / (θ * beta)) (max (Real.exp (192 * Real.log (768 / beta) / beta))
        ((16 / beta) * (max 0 (Real.log (9 / ν)) + 2 * Real.log (32 / beta))))))))
  refine ⟨X, (Real.exp_pos _).le.trans (le_max_left _ _), fun t hab hX hh => ?_⟩
  by_contra hf
  let u := Real.log t.logHeight
  simp only [X, max_le_iff] at hX
  obtain ⟨hx, hquad, hon, hu₀, hs₀, hon₁, hon₂⟩ := hX
  have hx0 : 0 < t.thirdLogRadical := (Real.exp_pos _).trans_le hx
  have hH : 0 < t.logHeight := (Real.exp_pos _).trans_le hh
  have hHu : Real.exp u = t.logHeight := Real.exp_log hH
  have hlogH : beta * t.thirdLogRadical ≤ u := by
    simpa only [u, Real.log_exp] using Real.log_le_log (Real.exp_pos (beta * t.thirdLogRadical)) hh
  have h48 : 48 ≤ 3 * (beta / 3) * t.thirdLogRadical := by
    have hb := (div_le_iff₀ hbeta).mp hu₀
    nlinarith only [hb]
  have hsmall0 : 320000 * 13824 ≤ θ * (3 * (beta / 3) * t.thirdLogRadical) := by
    have hb := (div_le_iff₀ (mul_pos hθ hbeta)).mp hs₀
    nlinarith only [hb]
  have windows (d : ℝ) (hd : d ≤ t.thirdLogRadical / Real.log t.thirdLogRadical) :=
    AbcTwoNinths.ExteriorE1.highRadiusWindows (show 0 < beta / 3 by positivity) hθ hx0
      (by rw [show 3 * (beta / 3) = beta by ring]; exact hon)
      (by linarith : 3 * (beta / 3) * t.thirdLogRadical ≤ u)
      h48 hsmall0 hd
  obtain ⟨hu, hs, _⟩ := windows (t.thirdLogRadical / Real.log t.thirdLogRadical) le_rfl
  have hpow := Real.pow_div_factorial_le_exp u (by linarith : 0 ≤ u) 2
  norm_num at hpow
  rw [hHu] at hpow
  have hmul : 320000 * 13824 * (u / 2) ≤ θ * t.logHeight := by
    have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ u / 2 by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hpow hθ.le
    nlinarith only [h₁, h₂]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hl2 : Real.log (2 : ℝ) ≤ θ * t.logHeight := by linarith
  have hfail : ν * t.logHeight < Real.log ((t.c : ℝ) / t.a) := lt_of_not_ge hf
  have hcontact := AbcTwoNinths.ExteriorE1.contactOfOrdered t hab
  have hlt : θ * t.logHeight < -Real.log (Real.log ((t.c : ℝ) / t.b)) := by
    have he : ν = 2 * θ := by dsimp [θ]; ring
    rw [he] at hfail
    nlinarith only [hfail, hcontact.2, hl2]
  have hclose : Real.log ((t.c : ℝ) / t.b) ≤ 1 / t.logHeight := by
    have he : θ * t.logHeight ≥ u := by linarith
    have h := (Real.log_le_iff_le_exp hcontact.1).mp
      (show Real.log (Real.log ((t.c : ℝ) / t.b)) ≤ -u by linarith)
    simpa only [Real.exp_neg, hHu, one_div] using h
  have bounds : SlabBounds t ν := by
    have hlogx : 4 ≤ Real.log t.thirdLogRadical := by simpa using Real.log_le_log (Real.exp_pos 4) hx
    refine ⟨hx, (Real.one_lt_exp_iff.mpr (mul_pos hbeta hx0)).trans_le hh, ?_, ?_, ?_⟩
    · have hwidth : t.thirdLogRadical / Real.log t.thirdLogRadical ≤ t.thirdLogRadical :=
        (div_le_iff₀ (by linarith)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hlogx hx0.le])
      have h2 := (div_le_iff₀ (sq_pos_of_pos hbeta)).mp hquad
      have hexp := Real.pow_div_factorial_le_exp (beta * t.thirdLogRadical) (mul_pos hbeta hx0).le 2
      norm_num at hexp
      exact hwidth.trans ((show t.thirdLogRadical ≤ (beta * t.thirdLogRadical) ^ 2 / 2 by
        nlinarith only [mul_le_mul_of_nonneg_left h2 hx0.le]).trans (hexp.trans hh))
    · linarith only [AbcTwoNinths.ExteriorE1.onsetScalePenalty t.thirdLogRadical beta ν hx0 hbeta hν hon₂, hlogH]
    · intro d hd
      have h₂ := AbcTwoNinths.ExteriorE1.onsetRankPenalty t.thirdLogRadical beta d hx0 hbeta hlogx
        (by simpa using Real.log_le_log (Real.exp_pos _) hon₁) hd
      linarith only [h₂, hlogH]
  obtain ⟨x, y, a, b, d, ε, hd, hdT, he, hell, hi, hv, hprod, ha, hb, hxlog, hylog⟩ :=
    reducedLogSlab ν hν t hab hf bounds hclose
  obtain ⟨q₁, q₂, c, e, hq₁, hq₂, hqi, hL₁, hL₂, hLp₁, hLp₂, hlo₁, hhi₁, hlo₂, hhi₂,
    hxq, hyq, hc, he', hform⟩ := AbcTwoNinths.ExteriorE1.orientedBasis t x y a b hi hv
  let ell := -Real.log ε
  have hε : Real.exp (-ell) = ε := by simp [ell, Real.exp_log he]
  have hcp : |(c : ℝ)| = |(a : ℝ)| := by exact_mod_cast hc
  have hep : |(e : ℝ)| = |(b : ℝ)| := by exact_mod_cast he'
  refine AbcTwoNinths.ExteriorE1.excludeOrientedContact AbcTwoNinths.ExteriorE1.variableRadius hq₁ hq₂ hqi hform.symm hθ hu hs (windows d hdT).2.2
    hell hd hLp₁ hLp₂ ?_ rfl rfl hhi₁ hhi₂ ?_ ?_ hlo₁ hlo₂ ?_ ?_ hcontact.1 ?_
  · rw [hHu, hL₁, hL₂]
    exact hprod.trans (by nlinarith only [mul_nonneg hH.le hd.le])
  · rw [hxq, hL₁, hε]
    exact hxlog
  · rw [hyq, hL₂, hε]
    exact hylog
  · rw [hcp, hL₁, hHu]
    exact ha
  · rw [hep, hL₂, hHu]
    exact hb.trans (by linarith)
  · rwa [hHu]

end AbcSubexp.ContactPrime
