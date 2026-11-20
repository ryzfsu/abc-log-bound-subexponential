/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S7_Interpolation.DigitBlockElimination
public import Subexp.S7_Interpolation.HighDigitInterpolation

/-!
# Lifting interpolation from the high digits

Partition integral binomial columns by their low digits and lift high-digit polynomial
interpolation to the original columns. This is the Lucas lifting step of Section 7.

## Main results

* `AbcSubexp.lucasBlockCoefficients_of_highDigitCoefficients`
* `AbcSubexp.lucasBlockCoefficients_eq_zero`
* `AbcSubexp.actualRowsCoefficients_eq_zero`
-/

@[expose] public section

namespace AbcSubexp

open scoped BigOperators

/-- Injective high-digit evaluation in each represented residue class gives injective
evaluation on the corresponding lifted rows for the original columns. -/
theorem lucasBlockCoefficients_of_highDigitCoefficients {m q D : ℕ} [Fact q.Prime]
    (A : Finset (Fin m → ℕ)) (W : (Fin m → ℕ) → (Fin m → ℕ) → Prop)
    (c : (Fin m → ℕ) → ZMod q) (hdeg : ∀ a ∈ A, (∑ i, a i) ≤ D)
    (hhigh : ∀ r ∈ A.image (fun a i => a i % q),
      ∀ (H : Finset (Fin m → ℕ)) (c' : (Fin m → ℕ) → ZMod q),
        (∀ u ∈ H, (∑ i, u i) ≤ (D - ∑ i, r i) / q) →
        (∀ y, W r y → ∑ u ∈ H, c' u * digitBinomial q y u = 0) → ∀ u ∈ H, c' u = 0)
    (hrow : ∀ r ∈ A.image (fun a i => a i % q), ∀ y, W r y →
      ∑ a ∈ A, c a * digitBinomial q (fun i => q * y i + r i) a = 0) :
    ∀ a ∈ A, c a = 0 := by
  let low (a : Fin m → ℕ) : Fin m → ℕ := fun i => a i % q
  let high (a : Fin m → ℕ) : Fin m → ℕ := fun i => a i / q
  let join (u r : Fin m → ℕ) : Fin m → ℕ := fun i => q * u i + r i
  let R := A.image low
  let F := fun r => A.filter fun a => low a = r
  let H := fun r => (F r).image high
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hjoin (a : Fin m → ℕ) : join (high a) (low a) = a := by
    funext i
    exact Nat.div_add_mod (a i) q
  have hinj (r : Fin m → ℕ) : Set.InjOn high ↑(F r) := by
    intro a ha b hb hab
    change a ∈ A.filter (fun a => low a = r) at ha
    change b ∈ A.filter (fun b => low b = r) at hb
    rw [← hjoin a, ← hjoin b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab]
  have hsum (u r : Fin m → ℕ) : (∑ i, join u r i) = q * (∑ i, u i) + ∑ i, r i := by
    simp only [join, Finset.sum_add_distrib, Finset.mul_sum]
  have hhighdeg (r u : Fin m → ℕ) (hu : u ∈ H r) :
      (∑ i, u i) ≤ (D - ∑ i, r i) / q := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    have ha' := Finset.mem_filter.mp ha
    have ha_deg := hdeg a ha'.1
    rw [← hjoin a, hsum, ha'.2] at ha_deg
    apply (Nat.le_div_iff_mul_le hq).2
    rw [Nat.mul_comm]
    omega
  have hmaps (a : Fin m → ℕ) (ha : a ∈ A) : low a ∈ R :=
    Finset.mem_image_of_mem low ha
  have hzero : ∀ r ∈ R, ∀ u ∈ H r, c (join u r) = 0 := by
    apply digitBlockCoefficients_eq_zero R H W (fun r u => c (join u r))
    · intro r hr i
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
      exact Nat.mod_lt (a i) hq
    · intro r hr hvanish
      exact hhigh r hr (H r) (fun u => c (join u r)) (hhighdeg r) hvanish
    · intro r hr y hy
      change ∑ s ∈ R, ∑ u ∈ H s, c (join u s) * digitBinomial q (join y r) (join u s) = 0
      calc
        _ = ∑ s ∈ R, ∑ a ∈ F s, c a * digitBinomial q (join y r) a := by
          apply Finset.sum_congr rfl
          intro s _
          change ∑ u ∈ (F s).image high, c (join u s) * digitBinomial q (join y r) (join u s) = _
          rw [Finset.sum_image (hinj s)]
          apply Finset.sum_congr rfl
          intro a ha
          have hlow : low a = s := (Finset.mem_filter.mp ha).2
          rw [← hlow, hjoin]
        _ = ∑ a ∈ A, c a * digitBinomial q (join y r) a :=
          Finset.sum_fiberwise_of_maps_to hmaps _
        _ = 0 := hrow r hr y hy
  intro a ha
  have haH : high a ∈ H (low a) := Finset.mem_image_of_mem high
    (Finset.mem_filter.mpr ⟨ha, rfl⟩)
  simpa only [hjoin] using hzero (low a) (hmaps a ha) (high a) haH

/-- A binomial combination of total degree at most `D < q * q` has zero coefficients if it
vanishes on the lifted witness rows, provided the witnesses in each represented residue class
detect all polynomials through that class's high-digit degree. -/
theorem lucasBlockCoefficients_eq_zero {m q D : ℕ} [Fact q.Prime] (hD : D < q * q)
    (A : Finset (Fin m → ℕ)) (W : (Fin m → ℕ) → (Fin m → ℕ) → Prop)
    (c : (Fin m → ℕ) → ZMod q) (hdeg : ∀ a ∈ A, (∑ i, a i) ≤ D)
    (hdet : ∀ r ∈ A.image (fun a i => a i % q), ∀ P : MvPolynomial (Fin m) (ZMod q),
      P.totalDegree ≤ (D - ∑ i, r i) / q →
      (∀ y, W r y → MvPolynomial.eval (fun i => (y i : ZMod q)) P = 0) → P = 0)
    (hrow : ∀ r ∈ A.image (fun a i => a i % q), ∀ y, W r y →
      ∑ a ∈ A, c a * digitBinomial q (fun i => q * y i + r i) a = 0) :
    ∀ a ∈ A, c a = 0 := by
  apply lucasBlockCoefficients_of_highDigitCoefficients A W c hdeg _ hrow
  intro r hr H c' hdegree hvanish
  have hj : (D - ∑ i, r i) / q < q :=
    (Nat.div_lt_iff_lt_mul (Fact.out : q.Prime).pos).2 ((Nat.sub_le D _).trans_lt hD)
  apply highDigitCoefficients_eq_zero hj H (W r) c' hdegree (hdet r hr)
  simpa only [digitBinomial] using hvanish

/-- A binomial combination vanishing on `B` has zero coefficients when each represented
residue class of `B` detects the polynomials through its high-digit degree. -/
theorem actualRowsCoefficients_eq_zero {m q D : ℕ} [Fact q.Prime] (hD : D < q * q)
    (A : Finset (Fin m → ℕ)) (B : (Fin m → ℕ) → Prop)
    (c : (Fin m → ℕ) → ZMod q) (hdeg : ∀ a ∈ A, (∑ i, a i) ≤ D)
    (hdet : ∀ r ∈ A.image (fun a i => a i % q), ∀ P : MvPolynomial (Fin m) (ZMod q),
      P.totalDegree ≤ (D - ∑ i, r i) / q →
      (∀ y : Fin m → ℕ, B (fun i => q * y i + r i) →
        MvPolynomial.eval (fun i => (y i : ZMod q)) P = 0) → P = 0)
    (hrow : ∀ z, B z → ∑ a ∈ A, c a * digitBinomial q z a = 0) :
    ∀ a ∈ A, c a = 0 :=
  lucasBlockCoefficients_eq_zero hD A (fun r y => B (fun i => q * y i + r i))
    c hdeg hdet (fun r _ y hy => hrow (fun i => q * y i + r i) hy)

end AbcSubexp
