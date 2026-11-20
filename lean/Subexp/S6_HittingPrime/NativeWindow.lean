/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.Basic.ThirdWindow

/-! # The third-window joint choice in the native contact data -/

@[expose] public section

noncomputable section

open Finset Real

namespace AbcSubexp

open Parameters

/-- Third-window endpoint rounded up before choosing the list or prime. -/
def Contact.hittingWindow {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t) : ℕ :=
  ⌈3 * (c.degree : ℝ) / (depthParameter ε + 1)⌉₊

/-- A strict exceptional-set budget and the two contact size estimates suffice for
the same prime and the same ordered list to satisfy every native hitting field. -/
theorem exists_hittingPrime_of_miss_budget {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}
    (g : GroupedTuple c) (bad : Finset ℕ)
    (hlarge : (depthParameter ε + 1) ^ 2 ≤ c.degree)
    (hradius : c.degree + c.hittingWindow ≤ c.radius)
    (hcard : bad.card < (thirdWindowPrimes c.hittingWindow).card)
    (hmiss : ∀ q ∈ thirdWindowPrimes c.hittingWindow,
      (∀ b, ¬ ∀ i, ∃ z : ℤ,
        |(q : ℝ) * g.slope b i - (i.val : ℝ) / dimension ε - (z : ℝ)| < phaseTolerance ε) →
      q ∈ bad) :
    Nonempty (HittingPrime g) := by
  obtain ⟨q, b, hprime, hlo, hhi, hhit⟩ := exists_thirdWindow_prime_and_block bad
    (fun q b => ∀ i, ∃ z : ℤ,
      |(q : ℝ) * g.slope b i - (i.val : ℝ) / dimension ε - (z : ℝ)| < phaseTolerance ε)
    hcard hmiss
  let k := depthParameter ε
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hceil : 3 * (c.degree : ℝ) / (k + 1) ≤ (c.hittingWindow : ℝ) :=
    Nat.le_ceil _
  have hlo' : (c.hittingWindow : ℝ) < 3 * (q : ℝ) := by exact_mod_cast hlo
  have hquot : (c.degree : ℝ) / (k + 1) < (q : ℝ) := by
    rw [mul_div_assoc] at hceil
    linarith
  have hprod' := (div_lt_iff₀ hk).mp hquot
  have hprod : c.degree < q * (k + 1) := by exact_mod_cast hprod'
  have hq : k + 1 < q := by
    by_contra! hc
    have hlim := Nat.mul_le_mul_right (k + 1) hc
    change (k + 1) ^ 2 ≤ c.degree at hlarge
    rw [pow_two] at hlarge
    omega
  refine ⟨⟨b, q, hprime, hquot, (Nat.add_le_add_left hhi _).trans hradius, hq, ?_, ?_⟩⟩
  · calc
      c.degree + q < q * (k + 1) + q := Nat.add_lt_add_right hprod _
      _ = q * (k + 2) := by ring
      _ ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_left q hq
  · intro i
    obtain ⟨z, hz⟩ := hhit i
    exact (round_le _ z).trans_lt hz

end AbcSubexp
