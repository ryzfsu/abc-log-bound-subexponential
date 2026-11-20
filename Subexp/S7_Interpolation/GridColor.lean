/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic

/-!
# Consecutive colors in a lattice simplex

This module formalizes the simplex colour decomposition used in Section 7.

Functions of bounded finite-difference degree are determined by consecutive
colors in a simplex, with values in any additive commutative group.

## Main results
* `AbcSubexp.gridDegreeLE_eq_zero_of_consecutive_colors`
-/

@[expose] public section

open scoped BigOperators

namespace AbcSubexp

variable {m : ℕ} {A : Type*} [AddCommGroup A]

/-- The cyclic color of an integer lattice point in the positive orthant. -/
def simplexColor (x : Fin m → ℕ) : ZMod m :=
  ∑ i, (i.val : ZMod m) * (x i : ZMod m)

/-- A bound on degree measured by iterated unit forward differences. -/
def gridDegreeLE : ℕ → ((Fin m → ℕ) → A) → Prop
  | 0, f => ∀ x, f x = f 0
  | j + 1, f => ∀ i : Fin m,
      gridDegreeLE j (fun x => f (x + Pi.single i 1) - f x)

private theorem gridDegreeLE_sub {j : ℕ} {f g : (Fin m → ℕ) → A}
    (hf : gridDegreeLE j f) (hg : gridDegreeLE j g) :
    gridDegreeLE j (fun x => f x - g x) := by
  induction j generalizing f g with
  | zero => exact fun x => congrArg₂ (· - ·) (hf x) (hg x)
  | succ j ih =>
    intro i
    convert ih (hf i) (hg i) using 1
    funext x
    simp only [sub_sub_sub_comm (f (x + Pi.single i 1)) (g (x + Pi.single i 1)) (f x) (g x)]

private theorem weight_step (x : Fin m → ℕ) (i : Fin m) :
    (∑ k, (x + Pi.single i 1 : Fin m → ℕ) k) = (∑ k, x k) + 1 := by
  simp [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply]

private theorem color_step (x : Fin m → ℕ) (i : Fin m) :
    simplexColor (x + Pi.single i 1) = simplexColor x + (i.val : ZMod m) := by
  classical
  simp [simplexColor, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply,
    mul_ite]

omit [AddCommGroup A] in
private theorem const_of_unit_steps {f : (Fin m → ℕ) → A}
    (step : ∀ (x : Fin m → ℕ) (i : Fin m), f (x + Pi.single i 1) = f x) :
    ∀ x, f x = f 0 := by
  classical
  intro x
  induction h : ∑ i, x i using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hz : x = 0
    · rw [hz]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hall
      exact hz (funext hall)
    let y := x - Pi.single i 1
    have hxy : x = y + Pi.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst k; simp [y, Pi.sub_apply, Pi.add_apply]; omega
      · simp [y, Pi.sub_apply, Pi.add_apply, hk]
    have hw := weight_step y i
    rw [← hxy] at hw
    calc
      f x = f (y + Pi.single i 1) := congrArg f hxy
      _ = f y := step y i
      _ = f 0 := ih (∑ i, y i) (by omega) y rfl

/-- Values on consecutive colors in the simplex of radius `j + 1`
determine a lattice function of finite-difference degree at most `j`. -/
theorem gridDegreeLE_eq_zero_of_consecutive_colors [NeZero m]
    {j : ℕ} (f : (Fin m → ℕ) → A) (hf : gridDegreeLE j f) (a : ZMod m)
    (hvan : ∀ x, (∑ i, x i) ≤ j + 1 →
      (∃ r : ℕ, r ≤ j ∧ simplexColor x = a + (r : ZMod m)) → f x = 0) :
    ∀ x, f x = 0 := by
  classical
  have detect (d : ℕ) (b : ZMod m) (g : (Fin m → ℕ) → A)
      (hc : ∀ x, g x = g 0)
      (hv : ∀ x, (∑ i, x i) ≤ d + 1 →
        (∃ r : ℕ, r ≤ d ∧ simplexColor x = b + (r : ZMod m)) → g x = 0) :
      ∀ x, g x = 0 := by
    let k : Fin m := ⟨b.val, b.val_lt⟩
    let z : Fin m → ℕ := 0 + Pi.single k 1
    have hz : (∑ i, z i) ≤ d + 1 := by simp [z]
    have hb : simplexColor z = b + ((0 : ℕ) : ZMod m) := by
      rw [show simplexColor z = simplexColor 0 + (k.val : ZMod m) from color_step 0 k]
      simp [simplexColor, k]
    exact fun x => (hc x).trans ((hc z).symm.trans (hv z hz ⟨0, Nat.zero_le _, hb⟩))
  induction j generalizing f a with
  | zero => exact detect 0 a f hf hvan
  | succ j ih =>
    have hzero : ∀ x, f (x + Pi.single (0 : Fin m) 1) = f x := by
      intro x
      apply sub_eq_zero.mp
      apply ih _ (hf 0) a _ x
      intro y hy hr
      obtain ⟨r, hr, hc⟩ := hr
      have hr' : r ≤ j + 1 := by omega
      exact sub_eq_zero.mpr ((hvan _ (by rw [weight_step]; omega)
        ⟨r, hr', by simpa [color_step] using hc⟩).trans
          (hvan y (by omega) ⟨r, hr', hc⟩).symm)
    have moving (i k : Fin m) (hik : k.val = i.val + 1) :
        ∀ x : Fin m → ℕ, f (x + Pi.single k 1) = f (x + Pi.single i 1) := by
      let g := fun (x : Fin m → ℕ) => f (x + Pi.single k 1) - f (x + Pi.single i 1)
      have hg : gridDegreeLE j g := by
        convert gridDegreeLE_sub (hf k) (hf i) using 1
        funext x
        dsimp [g]
        abel
      intro x
      apply sub_eq_zero.mp
      apply ih g hg (a - (i.val : ZMod m)) _ x
      intro y hy hr
      obtain ⟨r, hr, hc⟩ := hr
      have h1 := hvan (y + Pi.single i 1) (by rw [weight_step]; omega)
        ⟨r, by omega, by rw [color_step, hc]; abel⟩
      have h2 := hvan (y + Pi.single k 1) (by rw [weight_step]; omega)
        ⟨r + 1, by omega, by rw [color_step, hc, hik]; push_cast; abel⟩
      exact sub_eq_zero.mpr (h2.trans h1.symm)
    apply detect _ a f _ hvan
    apply const_of_unit_steps
    intro x i
    have hall (n : ℕ) (hn : n < m) : f (x + Pi.single (⟨n, hn⟩ : Fin m) 1) = f x := by
      induction n with
      | zero => exact hzero x
      | succ n ihn =>
        let k : Fin m := ⟨n, by omega⟩
        exact (moving k ⟨n + 1, hn⟩ rfl x).trans (ihn k.isLt)
    exact hall i.val i.isLt

end AbcSubexp
