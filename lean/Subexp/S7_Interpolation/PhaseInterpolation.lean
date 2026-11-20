/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.Basic.ProofData
public import Subexp.S7_Interpolation.ColorInterpolation
public import Subexp.S7_Interpolation.CyclicPhase
public import Subexp.S7_Interpolation.DigitBlockLifting
public import Subexp.S7_Interpolation.InterpolationParameters
public import Subexp.S7_Interpolation.RationalDetection

/-!
# Interpolation at the hitting prime

Each represented low digit contains a consecutive-colour witness set in the actual phase
window. These witnesses detect every high-digit block, and the resulting modular column
rank lifts to the rational polynomial space.

## Main results

* `AbcSubexp.interpolation_injective`
-/

@[expose] public section

namespace AbcSubexp

open Parameters
open scoped BigOperators

/-- The phase-restricted simplex of Section 7 detects rational polynomials through the
degree supplied by the determinant argument. -/
theorem interpolation_injective {ε : ℝ} {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t}
    {g : GroupedTuple c} (hε : 0 < ε) (q : HittingPrime g)
    (hwidth : windowWidth ε ≤ c.width) (P : MvPolynomial (Fin (dimension ε)) ℚ)
    (hdegree : P.totalDegree ≤ c.degree)
    (hvanish : ∀ z ∈ q.points (c.degree + q.prime),
      MvPolynomial.eval (fun i => (z i : ℚ)) P = 0) : P = 0 := by
  classical
  let : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨hm, hspacing, herror⟩ := interpolationParameterBounds hε
  let : NeZero (dimension ε) := ⟨hm.ne'⟩
  have hscale : c.degree < q.prime * (depthParameter ε + 1) := by
    have hk : 0 < (depthParameter ε : ℝ) + 1 := by positivity
    have hd := (div_lt_iff₀ hk).mp q.degree_lt
    exact_mod_cast hd
  have hsquare : c.degree < q.prime * q.prime := by
    have hs := q.radius_lt_square
    rw [pow_two] at hs
    omega
  have hhit (i : Fin (dimension ε)) :
      ∃ a : ℤ, |(q.prime : ℝ) * g.slope q.listIndex i - (i.val : ℝ) / dimension ε -
        (a : ℝ)| < phaseTolerance ε :=
    ⟨_, q.phase_hit i⟩
  apply eq_zero_of_modular_binomial_kernel q.prime
    (fun z => z ∈ q.points (c.degree + q.prime)) (c.degree + q.prime)
    (fun _ hz => hz.1) _ P hdegree hvanish
  intro A hdeg coeff hrow
  apply actualRowsCoefficients_eq_zero hsquare A (fun z => z ∈ q.points (c.degree + q.prime))
    coeff hdeg _ hrow
  intro r hr F hF hvan
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
  let r := fun i => a i % q.prime
  have hrw : (∑ i, r i) ≤ c.degree :=
    (Finset.sum_le_sum (fun i _ => Nat.mod_le (a i) _)).trans (hdeg a ha)
  obtain ⟨hj, colour, hnodes⟩ := exists_admissible_cyclic_colour_block
    (r := r) (θ := q.phase) hm hscale q.depth_lt (le_refl (c.degree + q.prime))
    hrw (fun i => Nat.mod_lt _ q.prime_isPrime.pos) hspacing herror hwidth hhit
  apply polynomial_eq_zero_of_consecutive_colors (hj.trans_lt (Nat.lt_succ_self _ |>.trans q.depth_lt))
    F hF colour
  intro y hy hcol
  obtain ⟨hsize, ⟨b, hb⟩, _⟩ := hnodes y hy hcol
  apply hvan y
  exact ⟨hsize, (round_le _ b).trans hb⟩

end AbcSubexp
