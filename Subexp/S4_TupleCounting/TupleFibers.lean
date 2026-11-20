/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Paper.S6_Diamond.FreshPrimePair

/-!
# Counting the completions of an auxiliary prime tuple

After fixing the anchor and all entries except one, a short vector supplies a roof
coordinate and a congruence class for its axial coefficient. In each such cell the
varying prime is counted by its old exponent vector and a signed residue equation.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting


variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]

/-- An odd prime is recorded as a pair with fixed denominator two. -/
def markedPrime (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) : AbcTwoNinths.Diamond.Pair :=
  ⟨(q, 2), hq, Nat.prime_two, hodd⟩

omit [Fact p.Prime] in
/-- The signed-root count applies to the marked primes throughout the window below
half the contact prime. -/
theorem markedPrime_crossBound {Q : Type*} (q : Q → ℕ) (hq : ∀ t, (q t).Prime)
    (hodd : ∀ t, q t ≠ 2) (hwindow : ∀ t, q t * 2 < p) :
    AbcTwoNinths.Diamond.CrossBound p (Set.range fun t => markedPrime (q t) (hq t) (hodd t)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨_, rfl⟩
  exact hwindow a

/-- A fixed fiber has at most the sharp old-image count times twice the pivot
exponent. Here the index can be a complete tuple, as long as its pivot determines
the remaining data in the fiber. -/
theorem fixedTupleFiber_card_le {α : Type*} (F : Finset α) (pivot : α → AbcTwoNinths.Diamond.Pair)
    (hinj : Set.InjOn pivot (↑F : Set α))
    (hcross : AbcTwoNinths.Diamond.CrossBound p (↑(F.image pivot) : Set AbcTwoNinths.Diamond.Pair))
    (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) {b : ℕ} (hb : 0 < b)
    (T : ℝ) (axial : α → ℤ) (lift : α → ι → ℤ) (c r : ℤ)
    (hcell : ∀ t ∈ F, (axial t • v + b • lift t) roof = c ∧
      axial t % (b : ℤ) = r ∧ AbcTwoNinths.Diamond.cost q (AbcTwoNinths.Diamond.roofProjection roof v (lift t)) ≤ T)
    (eval : (ι → ℤ) → ZMod p)
    (hsigned : ∀ t ∈ F, let z := eval (axial t • v + b • lift t) * AbcTwoNinths.Diamond.ratio p (pivot t) ^ b
      z = 1 ∨ z = -1) :
    F.card ≤ (AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2*T)⌋₊).card * (2*b) := by
  classical
  rcases F.eq_empty_or_nonempty with he | hne
  · simp [he]
  let : Nonempty α := ⟨hne.choose⟩
  let S := F.image pivot
  let rep := Function.invFunOn pivot (↑F : Set α)
  have hrep (s : AbcTwoNinths.Diamond.Pair) (hs : s ∈ S) : rep s ∈ F ∧ pivot (rep s) = s :=
    Function.invFunOn_pos (Finset.mem_image.mp hs)
  let old := fun s => axial (rep s) • v + b • lift (rep s)
  let codes := S.image old
  have hcodes : codes.card ≤ (AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2*T)⌋₊).card :=
    AbcTwoNinths.Diamond.oldImageCardLe q hq hiq roof v hv hb T S (axial ∘ rep) (lift ∘ rep) c r
      (fun s hs => hcell (rep s) (hrep s hs).1)
  calc
    F.card = S.card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ∑ _w ∈ codes, 2 * b :=
      AbcTwoNinths.Diamond.cardLeSumSignedFibers S hcross codes old (fun _ => b) eval
        (fun s hs => Finset.mem_image_of_mem old hs) (fun _ _ => hb)
        (fun s hs => by simpa only [(hrep s hs).2] using hsigned (rep s) (hrep s hs).1)
    _ = codes.card * (2*b) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcodes


omit [Fintype ι] in
/-- The axial vector and each corrected fresh ratio have trivial signed residue.
Factoring the actual ratio into a marked ratio and an anchor-dependent factor
places the last fresh prime in a signed power fiber. -/
theorem signedMarkedPower (red : AbcTwoNinths.ExteriorE2.Exponents ι →* (ZMod p)ˣ)
    (v u : ι → ℤ) (a : ℤ) (b : ℕ) (fresh : AbcTwoNinths.Diamond.Pair) (anchorFactor : ZMod p)
    (actual : (ZMod p)ˣ) (hactual : (actual : ZMod p) = anchorFactor * AbcTwoNinths.Diamond.ratio p fresh)
    (haxis : AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd v)) = 1)
    (hlift : AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd u)) * AbcTwoNinths.Diamond.quotientLabel actual = 1) :
    let z := ((red (Multiplicative.ofAdd (a • v + b • u)) : ZMod p) * anchorFactor ^ b)
      * AbcTwoNinths.Diamond.ratio p fresh ^ b
    z = 1 ∨ z = -1 := by
  let R := AbcTwoNinths.ExteriorE2.reduction red
  have h : R (Multiplicative.ofAdd (a • v + b • u)) * AbcTwoNinths.Diamond.quotientLabel actual ^ b = 1 := by
    change R ((Multiplicative.ofAdd v) ^ a * (Multiplicative.ofAdd u) ^ b) * _ = _
    rw [map_mul, map_zpow, map_pow, show R (Multiplicative.ofAdd v) = 1 from haxis,
      one_zpow, one_mul]
    exact (mul_pow (R (Multiplicative.ofAdd u)) (AbcTwoNinths.Diamond.quotientLabel actual) b).symm.trans
      (by rw [show R (Multiplicative.ofAdd u) * AbcTwoNinths.Diamond.quotientLabel actual = 1 from hlift, one_pow])
  simpa only [hactual, mul_pow, mul_assoc] using AbcTwoNinths.Diamond.signedOfQuotient _ actual b h

/-- Old coordinates of an integral combination of the axis and the corrected
prime differences of an ordered tuple. -/
def oldCombination {Q : Type*} {n : ℕ} (v : ι → ℤ) (lift : Q → Q → ι → ℤ)
    (t : Q × (Fin n → Q)) (a : ℤ) (c : Fin n → ℤ) : ι → ℤ :=
  a • v + ∑ j, c j • lift (t.2 j) t.1

/-- Count ordered tuples that admit oriented integral coefficient witnesses.
The pivot and its entire signed coefficient pattern are selected separately for
each bad tuple. All constants are uniform in the number of slots. -/
theorem badTupleCertificate_card_le {Q : Type*} [Fintype Q] {k : ℕ}
    (S : Finset (Q × (Fin (k+1) → Q))) (mark : Q ↪ AbcTwoNinths.Diamond.Pair)
    (cross : AbcTwoNinths.Diamond.CrossBound p (Set.range mark))
    (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (hiq : Function.Injective q)
    (roof : ι) (v : ι → ℤ) (hv : v roof ≠ 0) (T : ℝ) (B C : ℕ)
    (lift : Q → Q → ι → ℤ) (hT : ∀ s t, AbcTwoNinths.Diamond.cost q (AbcTwoNinths.Diamond.roofProjection roof v (lift s t)) ≤ T)
    (eval : Q → ℕ → (ι → ℤ) → ZMod p)
    (hsigned : ∀ (anchor s : Q) (a : ℤ) (b : ℕ), let w := a • v + b • lift s anchor
      let z := eval anchor b w * AbcTwoNinths.Diamond.ratio p (mark s) ^ b
      z = 1 ∨ z = -1)
    (hbad : ∀ t ∈ S, ∃ (i : Fin (k+1)) (a : ℤ) (c : Fin (k+1) → ℤ),
      0 < c i ∧ (∀ j, c j ∈ Finset.Icc (-(B : ℤ)) B) ∧
      oldCombination v lift t a c roof ∈ Finset.Icc (-(C : ℤ)) C) :
    S.card ≤ ((AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2*T)⌋₊).card * (2*B)) *
      ((k+1) * (2*B+1)^(k+1) * (Fintype.card Q)^(k+1) * (2*C+1) * B) := by
  classical
  let tuples := Q × (Fin (k+1) → Q)
  have pick (t : tuples) : ∃ (i : Fin (k+1)) (a : ℤ) (c : Fin (k+1) → ℤ),
      t ∈ S → 0 < c i ∧ (∀ j, c j ∈ Finset.Icc (-(B : ℤ)) B) ∧
        oldCombination v lift t a c roof ∈ Finset.Icc (-(C : ℤ)) C := by
    by_cases ht : t ∈ S
    · obtain ⟨i, a, c, h⟩ := hbad t ht
      exact ⟨i, a, c, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => (ht h).elim⟩
  choose pivot axial coeff hw using pick
  let code (t : tuples) := (pivot t, coeff t, t.1, t.2 ∘ (pivot t).succAbove,
    oldCombination v lift t (axial t) (coeff t) roof, axial t % coeff t (pivot t))
  let codes := (Finset.univ : Finset (Fin (k+1))) ×ˢ
    (Fintype.piFinset (fun _ : Fin (k+1) => Finset.Icc (-(B : ℤ)) B) ×ˢ
    ((Finset.univ : Finset Q) ×ˢ ((Finset.univ : Finset (Fin k → Q)) ×ˢ
    (Finset.Icc (-(C : ℤ)) C ×ˢ Finset.Ico 0 (B : ℤ)))))
  have hmaps : ∀ t ∈ S, code t ∈ codes := by
    intro t ht
    obtain ⟨hb, hc, hr⟩ := hw t ht
    simpa only [code, codes, Finset.mem_product, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_Ico] using
      And.intro hc (And.intro hr (And.intro (Int.emod_nonneg (axial t) hb.ne')
        ((Int.emod_lt_of_pos _ hb).trans_le (Finset.mem_Icc.mp (hc (pivot t))).2)))
  let D := (AbcTwoNinths.Diamond.productPairs ⌊Real.exp (2*T)⌋₊).card
  have hfib : ∀ s ∈ codes, (S.filter (fun t => code t = s)).card ≤ D * (2*B) := by
    rintro ⟨i, c, anchor, rest, top, rem⟩ _
    let F := S.filter (fun t => code t = (i, c, anchor, rest, top, rem))
    change F.card ≤ _
    rcases F.eq_empty_or_nonempty with he | hne
    · simp [he]
    have data (t : tuples) (ht : t ∈ F) :
        t ∈ S ∧ pivot t = i ∧ coeff t = c ∧ t.1 = anchor ∧ t.2 ∘ i.succAbove = rest ∧
        oldCombination v lift t (axial t) c roof = top ∧ axial t % c i = rem := by
      obtain ⟨hS, hcode⟩ := Finset.mem_filter.mp ht
      simp only [code, Prod.mk.injEq] at hcode
      rcases hcode with ⟨hi, hc, ha, hs, ho, hm⟩
      exact ⟨hS, hi, hc, ha, hi ▸ hs, hc ▸ ho, hi ▸ hc ▸ hm⟩
    obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨hm, hi, hc, -⟩ := data t₀ ht₀
    obtain ⟨hbpos, hbbox, -⟩ := hw t₀ hm
    rw [hc, hi] at hbpos
    have hB : c i ≤ B := by simpa only [hc] using (Finset.mem_Icc.mp (hbbox i)).2
    let b := (c i).toNat
    have hb : 0 < b := by omega
    have hbz : (b : ℤ) = c i := Int.toNat_of_nonneg hbpos.le
    let fixedPart := ∑ j : Fin k, c (i.succAbove j) • lift (rest j) anchor
    let varying (t : tuples) := mark (t.2 i)
    have inj : Set.InjOn varying (↑F : Set tuples) := by
      intro t ht t' ht' he
      obtain ⟨-, -, -, ha, hr, -⟩ := data t ht
      obtain ⟨-, -, -, ha', hr', -⟩ := data t' ht'
      refine Prod.ext (ha.trans ha'.symm) (funext fun j => ?_)
      by_cases hj : j = i
      · subst j
        exact mark.injective he
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
        exact congrFun (hr.trans hr'.symm) l
    have hcross : AbcTwoNinths.Diamond.CrossBound p (↑(F.image varying) : Set AbcTwoNinths.Diamond.Pair) := by
      rintro _ hs _ ht
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ht
      exact cross _ ⟨s.2 i, rfl⟩ _ ⟨t.2 i, rfl⟩
    apply (fixedTupleFiber_card_le F varying inj hcross q hq hiq roof v hv hb T axial
      (fun t => lift (t.2 i) anchor) (top - fixedPart roof) rem ?_ (eval anchor b)
      (fun t _ => hsigned anchor (t.2 i) (axial t) b)).trans
    · apply Nat.mul_le_mul_left
      omega
    · intro t ht
      obtain ⟨-, -, -, ha, hr, htop, hrem⟩ := data t ht
      refine ⟨?_, hbz ▸ hrem, hT _ _⟩
      have hold : oldCombination v lift t (axial t) c =
          (axial t • v + b • lift (t.2 i) anchor) + fixedPart := by
        unfold oldCombination
        rw [Fin.sum_univ_succAbove _ i, ha, ← natCast_zsmul, hbz, add_assoc]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [show t.2 (i.succAbove j) = rest j
          from congrFun hr j]
      rw [hold, Pi.add_apply] at htop
      omega
  have h := Finset.card_le_mul_card_image_of_maps_to hmaps (D * (2*B)) hfib
  apply h.trans_eq
  congr 1
  have hI (n : ℕ) : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by rw [Int.card_Icc]; omega
  simp only [codes, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Fintype.card_piFinset, Finset.prod_const, hI, Finset.card_univ, Fintype.card_fun,
    Int.card_Ico, sub_zero, Int.toNat_natCast, pow_succ (Fintype.card Q) k]
  ring

end AbcSubexp.TupleCounting
