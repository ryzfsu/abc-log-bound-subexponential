/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S4_TupleCounting.CountedPrimeLifts
public import Subexp.S4_TupleCounting.GrowingPrimeTuples
public import Subexp.Prerequisites.PrimitiveTaggedLattice

/-!
# Growing tall prime families from the old support

The selected axis and projected separation yield one counted family with fixed
signed corrections. The distinct growing tuple is chosen inside this same family.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

open Real Filter

/-- Enumerate the roof first and then the other primes of the old support. -/
def oldSupportPrime (S : Finset ℕ) (roof : ℕ) : Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S roof → ℕ :=
  Sum.elim (fun _ => roof) Subtype.val

private theorem oldSupportPrime_injective (S : Finset ℕ) (roof : ℕ) :
    Function.Injective (oldSupportPrime S roof) := by
  rintro (a | i) (b | j) h
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · exact ((Finset.mem_erase.mp j.property).1 h.symm).elim
  · exact ((Finset.mem_erase.mp i.property).1 h).elim
  · exact congrArg Sum.inr (Subtype.ext h)

/-- For each fixed contact rate and positive block size there exists a uniform
onset. Past this onset, the selected old data supply a single anchor and
the full growing family of prime differences with height separation. -/
theorem exists_tall_prime_family {e : ℝ} (he : 0 < e) (heCap : e ≤ 1/10)
    (m : ℕ) (hm : 0 < m) :
    ∃ X : ℝ, 0 < X ∧ ∀ x ≥ X, ∀ (S : Finset ℕ) (roof R p : ℕ)
      [Fact p.Prime] [Fact (2 < p)]
      (red : AbcTwoNinths.ExteriorE2.Exponents (Unit ⊕ AbcTwoNinths.ExteriorE2.OldIndex S roof) →* (ZMod p)ˣ)
      (s : (AbcTwoNinths.ExteriorE2.reduction red).toAdditive.ker),
      let q := oldSupportPrime S roof
      let v : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof) := s.val
      let h := AbcTwoNinths.Diamond.height q v
      let M := auxiliaryPrimeCutoff e x p h
      0 < R → log R = 3*x → roof ∈ S → (∀ i ∈ S, i.Prime) → (∀ i ∈ S, i ∣ R) →
      (2.94*e)*x < log p → log p ≤ x → (e/2)*exp (3*e*x) ≤ h →
      h/(2*x) ≤ |(v (.inl ()) : ℝ)| →
      (∀ (a : ℤ) (w : (AbcTwoNinths.ExteriorE2.reduction red).toAdditive.ker), a • w = s → IsUnit a) →
      (∀ w ∈ (AbcTwoNinths.ExteriorE2.reduction red).toAdditive.ker,
        AbcTwoNinths.ExteriorE2.cost (fun j => log (j.val : ℝ)) (AbcTwoNinths.ExteriorE2.project v w) < x/log x →
          AbcTwoNinths.ExteriorE2.project v w = 0) →
      ∃ (P : Finset ℕ) (lift : ℕ → ℕ → AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof))
        (f : Fin (m*⌊x^(1/3:ℝ)⌋₊+1) ↪ P),
        P ⊆ auxiliaryFreshPrimes R M ∧
        (∀ i ∈ P, ∀ j ∈ P,
          AbcTwoNinths.ExteriorE2.cost (fun k => log (k.val : ℝ)) (AbcTwoNinths.ExteriorE2.project v (lift i j)) < x/log x ∧
          (AbcTwoNinths.ExteriorE2.reduction red).toAdditive (lift i j) + AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0) ∧
        ∀ (a : ℤ) (c : Fin (m*⌊x^(1/3:ℝ)⌋₊) → ℤ), (a ≠ 0 ∨ c ≠ 0) →
          exp (sqrt x) < AbcTwoNinths.Diamond.height (tuplePrimes q Subtype.val (anchoredTuple f))
            (tupleCombination v (fun i j : P => lift i.val j.val) (anchoredTuple f) a c) := by
  classical
  obtain ⟨Xₜ, htall⟩ := eventually_atTop.1 (eventually_tall_cluster_tuple he m hm)
  obtain ⟨Xₛ, hsupply⟩ := eventually_atTop.1 (eventually_auxiliaryFreshPrimes_card he heCap)
  let X := max (exp 1) (max (20/e^2) (max Xₛ Xₜ))
  refine ⟨X, (exp_pos 1).trans_le (le_max_left _ _), ?_⟩
  intro x hx S roof R p _ _ red s
  dsimp only
  intro hR hxR hRoofMem hS hdiv hContact hContactUp hHeight hRoof hprim hshort
  have hx' : exp 1 ≤ x := (le_max_left _ _).trans hx
  have hxPos : 0 < x := (exp_pos 1).trans_le hx'
  have hon : 20 ≤ e^2*x := by
    have := (le_max_left (20/e^2) _).trans ((le_max_right _ _).trans hx)
    linarith only [(div_le_iff₀ (sq_pos_of_pos he)).1 this]
  have hcut := auxiliaryPrimeCutoffBounds he heCap
    (by exact_mod_cast (Fact.out : p.Prime).pos : 0 < (p:ℝ)) hon hContact hContactUp hHeight
  let q := oldSupportPrime S roof
  let v : AbcTwoNinths.ExteriorE2.Old (AbcTwoNinths.ExteriorE2.OldIndex S roof) := s.val
  let h := AbcTwoNinths.Diamond.height q v
  let M := auxiliaryPrimeCutoff e x p h
  have hh : 0 < h := (by positivity : 0 < (e/2)*exp (3*e*x)).trans_le hHeight
  have hlogM : 0 < log M := (mul_pos (by positivity : 0 < e^2/10) hxPos).trans_le hcut.2.2.2.1
  have hM : 0 ≤ M := (mul_pos (exp_pos _) ((Real.rpow_pos_of_pos
      (by exact_mod_cast (Fact.out : p.Prime).pos : 0 < (p:ℝ)) _).trans_le (le_max_left _ _))).le
  have hXₛ : Xₛ ≤ x := by dsimp [X] at hx; exact le_trans (by grind) hx
  have hSupply := hsupply x hXₛ R p h hR hxR (by exact_mod_cast (Fact.out : p.Prime).pos)
    hContact hContactUp hHeight
  obtain ⟨P, lift, hsub, hsize, hpairs⟩ := exists_countedPrimeLifts S roof hR hS hdiv hx' hxR hh
    hlogM hcut.2.2.2.2.1 hSupply (AbcTwoNinths.ExteriorE2.reduction red).toAdditive s hRoof hprim hshort
  have hv : v (.inl ()) ≠ 0 := by
    intro hz
    have hRoofPos := (div_pos hh (show 0 < 2*x by positivity)).trans_le hRoof
    simp [v] at hz
    rw [hz, Int.cast_zero, abs_zero] at hRoofPos
    exact (lt_irrefl _ hRoofPos)
  have hp (i) : (q i).Prime := by
    rcases i with i | j
    · exact hS _ hRoofMem
    · exact hS _ (Finset.mem_erase.mp j.property).2
  have costs (i : ℕ) (hi : i ∈ P) (j : ℕ) (hj : j ∈ P) :
      AbcTwoNinths.Diamond.cost q (AbcTwoNinths.Diamond.roofProjection (.inl ()) v (lift i j)) ≤ x/log x ∧
      Additive.ofMul (AbcTwoNinths.Diamond.quotientLabel (red (Multiplicative.ofAdd (lift i j)))) +
        AbcSubexp.Prerequisites.freshLabel p i - AbcSubexp.Prerequisites.freshLabel p j = 0 := by
    rw [AbcTwoNinths.Diamond.costProjectEq q v _ hv]
    exact ⟨(hpairs i hi j hj).1.le, (hpairs i hi j hj).2⟩
  obtain ⟨f, hf⟩ := htall x ((by dsimp [X]; grind : Xₜ ≤ X).trans hx)
    _ P R p M q (.inl ()) v red lift hR hM hcut.2.2.2.2.2 hsub hsize hp
    (oldSupportPrime_injective S roof) hv hHeight s.property costs
  exact ⟨P, lift, f, hsub, hpairs, hf⟩

end AbcSubexp.TupleCounting
