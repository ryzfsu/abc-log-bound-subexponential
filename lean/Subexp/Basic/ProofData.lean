/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S2_Parameters.Parameters
public import AbcTwoNinths.Paper.S1_Statement.OrderedTriple

/-!
# Data for the logarithmic height argument

The contact source, auxiliary tuples, and hitting prime determine the common
evaluation domain for the determinant and interpolation arguments.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace AbcSubexp

open Parameters Real

/-- The tail domain for the contradiction in Section 2. -/
def High (ε : ℝ) (t : AbcTwoNinths.Basic.Triple) : Prop := exp (3 * exponent ε * t.thirdLogRadical) ≤ t.logHeight

/-- A contact prime and its principal axial unit in Section 3. -/
structure Contact (ε : ℝ) (t : AbcTwoNinths.Basic.Triple) where
  prime : ℕ
  prime_isPrime : prime.Prime
  prime_gt_five : 5 < prime
  prime_dvd_side : prime ∣ AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t)
  log_lower : (3 - 6 / 100) * exponent ε * t.thirdLogRadical < log (prime : ℝ)
  log_upper : log (prime : ℝ) ≤ t.thirdLogRadical
  source : ℚ
  source_principal : AbcTwoNinths.Basic.RatPrincipalUnit prime source
  source_ne_one : source ≠ 1
  sourcePower : ℕ
  sourcePower_pos : 0 < sourcePower
  sourcePower_le : (sourcePower : ℝ) ≤ 1 / exponent ε
  source_eq : source ^ sourcePower = AbcTwoNinths.Statement.selectedSource t
  source_primitive : ∀ (u : ℚ) (k : ℕ), AbcTwoNinths.Basic.RatPrincipalUnit prime u → u ^ k = source → k = 1
  depth : ℕ
  depth_eq : padicValRat prime (source - 1) = depth
  depth_side : depth = padicValNat prime (AbcTwoNinths.Statement.sideValue t (AbcTwoNinths.Statement.minRadicalSide t))
  height_cap : t.logHeight ≤ exp t.thirdLogRadical
  axial_height_lower : (exponent ε / 2) * exp (3 * exponent ε * t.thirdLogRadical) ≤ AbcTwoNinths.Basic.rationalHeight source
  axial_height_upper : AbcTwoNinths.Basic.rationalHeight source ≤ t.logHeight
  depth_share : 2 * exponent ε * AbcTwoNinths.Basic.rationalHeight source < (depth : ℝ) * log (prime : ℝ)
  depth_share_upper : (depth : ℝ) * log (prime : ℝ) ≤ AbcTwoNinths.Basic.rationalHeight source + log 2
  real_contact : |log (|(source : ℝ)|)| ≤ (exponent ε / 50) * AbcTwoNinths.Basic.rationalHeight source

variable {ε : ℝ} {t : AbcTwoNinths.Basic.Triple}

/-- Auxiliary-prime cutoff in Section 4. -/
def Contact.cutoff (c : Contact ε t) : ℝ :=
  exp (auxiliaryRate ε * t.thirdLogRadical) * max (sqrt c.prime) (c.prime / AbcTwoNinths.Basic.rationalHeight c.source)

/-- A finite family of disjoint lists of auxiliary generators from Section 4. -/
structure GroupedTuple (c : Contact ε t) where
  anchor : ℕ
  anchor_prime : anchor.Prime
  anchor_fresh : ¬ anchor ∣ t.radical
  anchor_in_window : c.cutoff / 3 < anchor ∧ (anchor : ℝ) ≤ c.cutoff
  prime : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ → Fin (dimension ε) → ℕ
  prime_isPrime : ∀ b i, (prime b i).Prime
  prime_fresh : ∀ b i, ¬ prime b i ∣ t.radical
  prime_ne_anchor : ∀ b i, prime b i ≠ anchor
  primes_distinct : Function.Injective
    (fun j : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ × Fin (dimension ε) => prime j.1 j.2)
  primes_in_window : ∀ b i, c.cutoff / 3 < prime b i ∧ (prime b i : ℝ) ≤ c.cutoff
  roof : ℕ
  roof_prime : roof.Prime
  roof_dvd_radical : roof ∣ t.radical
  roof_nonzero : padicValRat roof c.source ≠ 0
  unit : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ → Fin (dimension ε) → ℚ
  unit_principal : ∀ b i, AbcTwoNinths.Basic.RatPrincipalUnit c.prime (unit b i)
  unit_anchor : ∀ b i, padicValRat anchor (unit b i) = -1
  unit_fresh : ∀ b i, padicValRat (prime b i) (unit b i) = 1
  unit_support : ∀ b i p, p.Prime → p ≠ anchor → p ≠ prime b i →
    padicValRat p c.source = 0 → padicValRat p (unit b i) = 0
  roof_normalized : ∀ b i,
    |(padicValRat roof (unit b i) : ℝ) / (padicValRat roof c.source : ℝ)| ≤ 1 / 2
  transverse_height : ∀ b i,
    (∑ p ∈ t.radical.primeFactors.erase roof,
      |(padicValRat p (unit b i) : ℝ) -
        ((padicValRat roof (unit b i) : ℝ) / (padicValRat roof c.source : ℝ)) *
          (padicValRat p c.source : ℝ)| * log (p : ℝ)) < t.thirdLogRadical / log t.thirdLogRadical
  height_separation :
    ∀ (a : ℤ) (y : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊ → Fin (dimension ε) → ℤ),
      (a, y) ≠ 0 → exp (sqrt t.thirdLogRadical) <
        AbcTwoNinths.Basic.rationalHeight (c.source ^ a * ∏ b, ∏ i, unit b i ^ y b i)

variable {c : Contact ε t}

/-- The roof slope is the ratio of the generator and axial valuations at the roof prime.
These slopes give the axial coordinate in Section 5. -/
def GroupedTuple.slope (g : GroupedTuple c) (b : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊)
    (i : Fin (dimension ε)) : ℝ :=
  (padicValRat g.roof (g.unit b i) : ℝ) / (padicValRat g.roof c.source : ℝ)

/-- The degree limit for the elimination polynomial in Section 5. -/
def Contact.degree (c : Contact ε t) : ℕ := ⌈(1 + degreeMargin ε) * c.depth⌉₊ - 1

/-- The transverse budget for the lattice box in Section 5. -/
def Contact.transverseBudget (c : Contact ε t) : ℝ :=
  (1 - exponent ε / 5) * (c.depth : ℝ) * log (c.prime : ℝ) /
    ((dimension ε + 1) * (1 + 1 / (depthParameter ε : ℝ)))

/-- The integer transverse shift in Section 5. -/
def Contact.shift (c : Contact ε t) : ℕ := ⌊c.transverseBudget / log c.cutoff⌋₊

/-- The degree-simplex radius in Section 5. -/
def Contact.radius (c : Contact ε t) : ℕ := (dimension ε + 1) * c.shift

/-- The full width of the axial window in Section 5. -/
def Contact.width (c : Contact ε t) : ℝ :=
  (dimension ε + 1) * c.transverseBudget / ((depthParameter ε : ℝ) * AbcTwoNinths.Basic.rationalHeight c.source)

/-- Distance to an integer in the real phase coordinate. -/
def circleDistance (u : ℝ) : ℝ := |u - (round u : ℤ)|

/-- One list and one prime satisfying the joint choice in Section 6. -/
structure HittingPrime (g : GroupedTuple c) where
  listIndex : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊
  prime : ℕ
  prime_isPrime : prime.Prime
  degree_lt : (c.degree : ℝ) / (depthParameter ε + 1) < prime
  radius_le : c.degree + prime ≤ c.radius
  depth_lt : depthParameter ε + 1 < prime
  radius_lt_square : c.degree + prime < prime ^ 2
  phase_hit : ∀ i, circleDistance
    (prime * g.slope listIndex i - (i.val : ℝ) / dimension ε) < phaseTolerance ε

variable {g : GroupedTuple c}

/-- The character on the lattice generated by the selected list and the axial unit. -/
def HittingPrime.character (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ) : ℚ :=
  c.source ^ a * ∏ i, g.unit q.listIndex i ^ y i

/-- The phase after shifting from the box to the nonnegative simplex in Section 5. -/
def HittingPrime.phase (q : HittingPrime g) : ℝ :=
  -(c.shift : ℝ) * ∑ i, g.slope q.listIndex i

/-- The phase-restricted evaluation points in the simplex of the given radius. -/
def HittingPrime.points (q : HittingPrime g) (radius : ℕ) : Set (Fin (dimension ε) → ℕ) :=
  {z | (∑ i, z i) ≤ radius ∧
    circleDistance (q.phase + ∑ i, g.slope q.listIndex i * z i) ≤ c.width / 2}

/-- The unshifted lattice box with the axial and transverse inequalities of Section 5. -/
def HittingPrime.box (q : HittingPrime g) (a : ℤ) (y : Fin (dimension ε) → ℤ) : Prop :=
  |(a : ℝ) + ∑ i, g.slope q.listIndex i * y i| ≤ c.width / 2 ∧
  (∀ i, -c.transverseBudget ≤ log c.cutoff * y i) ∧
  log c.cutoff * (∑ i, (y i : ℝ)) ≤ c.transverseBudget

/-- Projection of the box and a shortest translation for the second set of columns. -/
structure BoxData (q : HittingPrime g) : Prop where
  width_lower : windowWidth ε ≤ c.width
  width_upper : c.width < 1
  box_projection : ∀ z : Fin (dimension ε) → ℕ, z ∈ q.points c.radius ↔
    ∃ a : ℤ, q.box a (fun i => (z i : ℤ) - (c.shift : ℤ))
  translation : ∃ (a : ℤ) (y : Fin (dimension ε) → ℤ), (a, y) ≠ 0 ∧
    (∀ (a' : ℤ) (y' : Fin (dimension ε) → ℤ), (a', y') ≠ 0 →
      AbcTwoNinths.Basic.rationalHeight (q.character a y) ≤ AbcTwoNinths.Basic.rationalHeight (q.character a' y')) ∧
    AbcTwoNinths.Basic.rationalHeight (q.character a y) ≤
      (1 + 2 * (dimension ε : ℝ)) * sqrt (log c.cutoff / AbcTwoNinths.Basic.rationalHeight c.source) *
        AbcTwoNinths.Basic.rationalHeight c.source

end AbcSubexp
