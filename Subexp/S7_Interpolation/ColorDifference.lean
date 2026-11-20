/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic.Abel

/-!
# Consecutive colours determine functions of bounded difference degree

This module formalizes the finite-difference step of Section 7.

Colour labels form a cyclic group. A multiset of labels represents the vector
of their multiplicities. Its cardinality is the simplex level and its sum is its colour.

## Main results
* `AbcSubexp.ColorDifference.eq_zero_of_color_vanishing`
* `AbcSubexp.ColorDifference.highDigitCoefficients_of_consecutive_colors`
-/

@[expose] public section

namespace AbcSubexp.ColorDifference

variable {ι A : Type*} [AddCommGroup A]

/-- Insertion of one label, with the empty insertion as a possible direction. -/
def insertLabel : Option ι → Multiset ι → Multiset ι
  | none, s => s
  | some i, s => i ::ₘ s

/-- All iterated insertion differences of order one more than the bound vanish. -/
def DifferenceDegree : ℕ → (Multiset ι → A) → Prop
  | 0, f => ∀ s, f s = f 0
  | j + 1, f => ∀ a b : Option ι, DifferenceDegree j
      (fun s => f (insertLabel a s) - f (insertLabel b s))

private theorem eq_zero_on_ray {f : Multiset ι → A} (i : ι) (j : ℕ)
    (hd : DifferenceDegree j f) (h : ∀ n ≤ j, f (Multiset.replicate (n + 1) i) = 0) :
    ∀ n, f (Multiset.replicate n i) = 0 := by
  induction j generalizing f with
  | zero =>
    intro n
    rw [hd, ← hd (Multiset.replicate 1 i)]
    exact h 0 le_rfl
  | succ j ih =>
    let g := fun s => f (i ::ₘ s) - f s
    have hg : DifferenceDegree j g := hd (some i) none
    have hz : ∀ n, g (Multiset.replicate n i) = 0 := by
      apply ih hg
      intro n hn
      change f (i ::ₘ Multiset.replicate (n + 1) i) - f (Multiset.replicate (n + 1) i) = 0
      rw [← Multiset.replicate_succ i (n := n + 1), h (n + 1) (by omega),
        h n (by omega), sub_self]
    have step (n : ℕ) : f (Multiset.replicate (n + 1) i) = f (Multiset.replicate n i) := by
      rw [Multiset.replicate_succ]
      exact sub_eq_zero.mp (hz n)
    intro n
    induction n with
    | zero => exact (step 0).symm.trans (h 0 (by omega))
    | succ n ihn => exact (step n).trans ihn

/-- Vanishing on the selected colours through level `j+1` forces global vanishing. -/
theorem eq_zero_of_color_vanishing {m : ℕ} [NeZero m] (j : ℕ)
    (f : Multiset (ZMod m) → A) (a : ZMod m) (hd : DifferenceDegree j f)
    (h : ∀ s : Multiset (ZMod m), s.card ≤ j + 1 →
      (∃ t : ℕ, t ≤ j ∧ s.sum = a + t) → f s = 0) : ∀ s, f s = 0 := by
  induction j generalizing f a with
  | zero =>
    intro s
    rw [hd, ← hd {a}]
    apply h
    · simp
    · exact ⟨0, le_rfl, by simp⟩
  | succ j ih =>
    have adjacent (i : ZMod m) (s : Multiset (ZMod m)) :
        f ((i + 1) ::ₘ s) = f (i ::ₘ s) := by
      apply sub_eq_zero.mp
      apply ih (fun s => f ((i + 1) ::ₘ s) - f (i ::ₘ s)) (a - i)
        (hd (some (i + 1)) (some i)) _ s
      intro z hcard hz
      obtain ⟨t, ht, hsum⟩ := hz
      have h₁ : f ((i + 1) ::ₘ z) = 0 := by
        apply h
        · simp only [Multiset.card_cons]; omega
        · refine ⟨t + 1, by omega, ?_⟩
          simp only [Multiset.sum_cons, hsum, Nat.cast_succ]
          abel
      have h₀ : f (i ::ₘ z) = 0 := by
        apply h
        · simp only [Multiset.card_cons]; omega
        · exact ⟨t, by omega, by rw [Multiset.sum_cons, hsum]; abel⟩
      rw [h₁, h₀, sub_self]
    have flat (i : ZMod m) (s : Multiset (ZMod m)) : f (i ::ₘ s) = f (0 ::ₘ s) := by
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective i
      induction n with
      | zero => simp
      | succ n ihn => simpa only [Nat.cast_succ] using (adjacent n s).trans ihn
    have move (u v : Multiset (ZMod m)) :
        f (u + v) = f (Multiset.replicate u.card 0 + v) := by
      induction u using Multiset.induction_on generalizing v with
      | empty => simp
      | cons i u ihu =>
        calc
          f ((i ::ₘ u) + v) = f (i ::ₘ (u + v)) := by rw [Multiset.cons_add]
          _ = f (0 ::ₘ (u + v)) := flat i _
          _ = f (u + (0 ::ₘ v)) := by rw [Multiset.add_cons]
          _ = f (Multiset.replicate u.card 0 + (0 ::ₘ v)) := ihu _
          _ = f (Multiset.replicate (i ::ₘ u).card 0 + v) := by
            rw [Multiset.card_cons, Multiset.replicate_succ, Multiset.cons_add,
              Multiset.add_cons]
    have ray : ∀ n, f (Multiset.replicate n 0) = 0 := by
      apply eq_zero_on_ray 0 (j + 1) hd
      intro n hn
      rw [Multiset.replicate_succ, ← flat a]
      apply h
      · simp; omega
      · exact ⟨0, by omega, by simp⟩
    intro s
    simpa using (move s 0).trans (by simpa using ray s.card)

private theorem degree_const (j : ℕ) (c : A) :
    DifferenceDegree j (fun _ : Multiset ι => c) := by
  induction j generalizing c with
  | zero => intro s; rfl
  | succ j ih =>
    intro a b
    simpa only [sub_self] using ih (0 : A)

private theorem degree_add (j : ℕ) {f g : Multiset ι → A}
    (hf : DifferenceDegree j f) (hg : DifferenceDegree j g) :
    DifferenceDegree j (fun s => f s + g s) := by
  induction j generalizing f g with
  | zero => intro s; exact congrArg₂ (· + ·) (hf s) (hg s)
  | succ j ih =>
    intro a b
    simpa only [add_sub_add_comm] using ih (hf a b) (hg a b)

private theorem degree_sub (j : ℕ) {f g : Multiset ι → A}
    (hf : DifferenceDegree j f) (hg : DifferenceDegree j g) :
    DifferenceDegree j (fun s => f s - g s) := by
  induction j generalizing f g with
  | zero => intro s; exact congrArg₂ (· - ·) (hf s) (hg s)
  | succ j ih =>
    intro a b
    convert ih (hf a b) (hg a b) using 2 with s
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
    simp only [add_assoc, add_left_comm, add_comm]

section Binomial

variable [DecidableEq ι] [Fintype ι]

/-- Integer entry of the multivariate binomial evaluation matrix. -/
def binomialEntry (s u : Multiset ι) : ℕ :=
  ∏ i : ι, (s.count i).choose (u.count i)

private theorem entry_cons (s u : Multiset ι) (i : ι) :
    binomialEntry (i ::ₘ s) u =
      binomialEntry s u + if i ∈ u then binomialEntry s (u.erase i) else 0 := by
  classical
  let tail := ∏ k ∈ Finset.univ.erase i, (s.count k).choose (u.count k)
  have split (s u : Multiset ι) : binomialEntry s u =
      (∏ k ∈ Finset.univ.erase i, (s.count k).choose (u.count k)) *
        (s.count i).choose (u.count i) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  have consTail : (∏ k ∈ Finset.univ.erase i, ((i ::ₘ s).count k).choose (u.count k)) =
      tail := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hk)]
  rw [split (i ::ₘ s), consTail, Multiset.count_cons_self, split s u]
  change tail * _ = tail * _ + _
  by_cases hi : i ∈ u
  · rw [ite_eq_left hi, split s (u.erase i)]
    have eraseTail : (∏ k ∈ Finset.univ.erase i, (s.count k).choose ((u.erase i).count k)) =
        tail := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hk)]
    rw [eraseTail, Multiset.count_erase_self, ← Nat.mul_add]
    have hp := Multiset.count_pos.mpr hi
    cases hn : u.count i with
    | zero => omega
    | succ n =>
      rw [Nat.choose_succ_succ']
      simp [add_comm]
  · rw [ite_eq_right hi, Multiset.count_eq_zero.mpr hi]
    simp

private theorem degree_entry (j : ℕ) (u : Multiset ι) (hc : u.card ≤ j) (c : A) :
    DifferenceDegree j (fun s => binomialEntry s u • c) := by
  induction j generalizing u with
  | zero =>
    have hu : u = 0 := Multiset.card_eq_zero.mp (by omega)
    subst u
    simpa [binomialEntry] using degree_const (ι := ι) 0 c
  | succ j ih =>
    let extra (a : Option ι) (s : Multiset ι) : ℕ :=
      match a with
      | none => 0
      | some i => if i ∈ u then binomialEntry s (u.erase i) else 0
    have inc (a : Option ι) (s : Multiset ι) :
        binomialEntry (insertLabel a s) u = binomialEntry s u + extra a s := by
      cases a with
      | none => simp [insertLabel, extra]
      | some i => exact entry_cons s u i
    have low (a : Option ι) : DifferenceDegree j (fun s => extra a s • c) := by
      cases a with
      | none => simpa [extra] using degree_const (ι := ι) j (0 : A)
      | some i =>
        by_cases hi : i ∈ u
        · have := Multiset.card_erase_add_one hi
          simpa [extra, hi] using ih (u.erase i) (by omega)
        · simpa [extra, hi] using degree_const (ι := ι) j (0 : A)
    intro a b
    simpa only [inc, add_nsmul, add_sub_add_left_eq_sub] using degree_sub j (low a) (low b)

private theorem degree_expansion (j : ℕ) (U : Finset (Multiset ι)) (c : Multiset ι → A)
    (hc : ∀ u ∈ U, u.card ≤ j) :
    DifferenceDegree j (fun s => ∑ u ∈ U, binomialEntry s u • c u) := by
  classical
  induction U using Finset.induction_on with
  | empty => simpa using degree_const (ι := ι) j (0 : A)
  | @insert u U hu ih =>
    rw [Finset.forall_mem_insert] at hc
    simpa [Finset.sum_insert hu] using degree_add j (degree_entry j u hc.1 (c u)) (ih hc.2)

end Binomial

private theorem entry_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    {s u : Multiset ι} (h : ¬u ≤ s) : binomialEntry s u = 0 := by
  rw [Multiset.le_iff_count] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi)

/-- Consecutive colours in the radius-`j+1` simplex determine every coefficient
of a multivariate binomial expansion of order at most `j`. -/
theorem binomial_coefficients_zero {m : ℕ} [NeZero m] (j : ℕ)
    (U : Finset (Multiset (ZMod m))) (c : Multiset (ZMod m) → A) (a : ZMod m)
    (hU : ∀ u ∈ U, u.card ≤ j)
    (h : ∀ s : Multiset (ZMod m), s.card ≤ j + 1 →
      (∃ t : ℕ, t ≤ j ∧ s.sum = a + t) → ∑ u ∈ U, binomialEntry s u • c u = 0) :
    ∀ u ∈ U, c u = 0 := by
  classical
  have hall := eq_zero_of_color_vanishing j _ a (degree_expansion j U c hU) h
  intro u hu
  induction u using WellFoundedLT.induction with
  | ind u ih =>
    have vanish (v : Multiset (ZMod m)) (hv : v ∈ U) (hne : v ≠ u) :
        binomialEntry u v • c v = 0 := by
      by_cases hle : v ≤ u
      · rw [ih v (lt_of_le_of_ne hle hne) hv, nsmul_zero]
      · rw [entry_zero hle, zero_nsmul]
    have hz := hall u
    change ∑ v ∈ U, binomialEntry u v • c v = 0 at hz
    rw [Finset.sum_eq_single_of_mem u hu vanish] at hz
    simpa [binomialEntry] using hz

section Vectors

variable {m : ℕ} [NeZero m]

private noncomputable def countsEquiv : Multiset (ZMod m) ≃ (Fin m → ℕ) :=
  (Multiset.toFinsupp.toEquiv.trans Finsupp.equivFunOnFinite).trans
    ((ZMod.finEquiv m).toEquiv.symm.arrowCongr (Equiv.refl ℕ))

private theorem counts_card (s : Multiset (ZMod m)) : (∑ i, countsEquiv s i) = s.card := by
  change (∑ i, s.count ((ZMod.finEquiv m) i)) = _
  exact ((ZMod.finEquiv m).toEquiv.sum_comp s.count).trans
    (Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _))

private theorem counts_color (s : Multiset (ZMod m)) :
    (∑ i : Fin m, (i.val : ZMod m) * (countsEquiv s i : ZMod m)) = s.sum := by
  have he (i : Fin m) : (i.val : ZMod m) = (ZMod.finEquiv m) i := by
    cases m with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact ZMod.natCast_zmod_val (ZMod.finEquiv (n+1) i)
  simp only [he]
  change (∑ i, ((ZMod.finEquiv m) i) * (s.count ((ZMod.finEquiv m) i) : ZMod m)) = _
  refine ((ZMod.finEquiv m).toEquiv.sum_comp (fun k => k * (s.count k : ZMod m))).trans ?_
  have H := Finsupp.sum_toMultiset s.toFinsupp
  rw [← Multiset.toFinsupp_symm_apply, AddEquiv.symm_apply_apply,
    Finsupp.sum_fintype _ _ (by simp)] at H
  simpa only [Multiset.toFinsupp_apply, nsmul_eq_mul, mul_comm] using H.symm

private theorem counts_entry (s u : Multiset (ZMod m)) :
    (∏ i, (countsEquiv s i).choose (countsEquiv u i)) = binomialEntry s u :=
  (ZMod.finEquiv m).toEquiv.prod_comp (fun k => (s.count k).choose (u.count k))

/-- The consecutive-colour condition directly detects the high-digit binomial
columns on the positive lattice in their ordinary coordinate representation. -/
theorem highDigitCoefficients_of_consecutive_colors {q j : ℕ}
    (H : Finset (Fin m → ℕ)) (c : (Fin m → ℕ) → ZMod q) (a : ZMod m)
    (hdeg : ∀ u ∈ H, ∑ i, u i ≤ j)
    (hrow : ∀ y : Fin m → ℕ, (∑ i, y i) ≤ j + 1 →
      (∃ t : ℕ, t ≤ j ∧ (∑ i, (i.val : ZMod m) * (y i : ZMod m)) = a + t) →
      ∑ u ∈ H, c u * ∏ i, ((y i).choose (u i) : ZMod q) = 0) :
    ∀ u ∈ H, c u = 0 := by
  classical
  let E := countsEquiv (m := m)
  let U := H.map E.symm.toEmbedding
  have hz := binomial_coefficients_zero j U (fun s => c (E s)) a
  have hsize : ∀ s ∈ U, s.card ≤ j := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hs
    rw [← counts_card]
    exact (by simpa [E] using hdeg u hu)
  have hval (s : Multiset (ZMod m)) (hs : s.card ≤ j+1)
      (hcol : ∃ t : ℕ, t ≤ j ∧ s.sum = a + t) :
      ∑ u ∈ U, binomialEntry s u • c (E u) = 0 := by
    have hr := hrow (E s) (by simpa [E, counts_card] using hs)
      (by simpa [E, counts_color] using hcol)
    rw [Finset.sum_map]
    convert hr using 1
    apply Finset.sum_congr rfl
    intro u hu
    change binomialEntry s (E.symm u) • c (E (E.symm u)) = _
    rw [E.apply_symm_apply, ← counts_entry, nsmul_eq_mul, Nat.cast_prod, mul_comm]
    simp [E]
  intro u hu
  simpa using hz hsize hval (E.symm u) (Finset.mem_map.mpr ⟨u, hu, rfl⟩)

end Vectors

end AbcSubexp.ColorDifference
