/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S7_Interpolation.PolynomialTranslation
public import Mathlib.Tactic.LinearCombination

/-!
# Elimination on a box and its translate

Two polynomial rows are evaluated against a character at a family of points and at its
translate. Eliminating the character gives a nonzero polynomial on the original points.
-/

@[expose] public section

namespace AbcSubexp

open MvPolynomial

variable {σ ι : Type*} {K : Type*} [Field K]

private theorem translationDifference_degree_lt (s : σ → K) (P : MvPolynomial σ K)
    (h : polynomialTranslation s P - P ≠ 0) :
    (polynomialTranslation s P - P).totalDegree < P.totalDegree := by
  cases hd : P.totalDegree with
  | zero =>
    obtain ⟨c, hc⟩ : ∃ c : K, P = C c :=
      ⟨_, totalDegree_eq_zero_iff_eq_C.mp hd⟩
    simp [hc, polynomialTranslation] at h
  | succ n => exact Nat.lt_succ_of_le (totalDegree_translation_sub_le s P hd.le)

private theorem translation_degree_le (s : σ → K) (P : MvPolynomial σ K) :
    (polynomialTranslation s P).totalDegree ≤ P.totalDegree := by
  by_cases h : polynomialTranslation s P - P = 0
  · rw [sub_eq_zero.mp h]
  · have hb := totalDegree_add (polynomialTranslation s P - P) P
    simpa [max_eq_right (translationDifference_degree_lt s P h).le] using hb

private theorem translation_ne_zero (s : σ → K) {P : MvPolynomial σ K} (hP : P ≠ 0) :
    polynomialTranslation s P ≠ 0 := by
  intro h
  have hi : (polynomialTranslation (-s)).comp (polynomialTranslation s) = AlgHom.id K _ := by
    ext i
    simp [polynomialTranslation, Pi.neg_apply, add_assoc]
  have hcancel := DFunLike.congr_fun hi P
  simp [AlgHom.comp_apply, h, hP.symm] at hcancel

private theorem coeff_translate_mul_top (s : σ → K) (P Q : MvPolynomial σ K)
    (d : σ →₀ ℕ) (hd : (d.sum fun _ e => e) = P.totalDegree + Q.totalDegree) :
    (polynomialTranslation s P * Q).coeff d = (P * Q).coeff d := by
  apply sub_eq_zero.mp
  rw [← coeff_sub, ← sub_mul]
  by_cases h : polynomialTranslation s P - P = 0
  · simp [h]
  · apply coeff_eq_zero_of_totalDegree_lt
    change ((polynomialTranslation s P - P) * Q).totalDegree < d.sum (fun _ e => e)
    rw [hd]
    exact (totalDegree_mul _ _).trans_lt (Nat.add_lt_add_right
      (translationDifference_degree_lt s P h) _)

/-- With two nonzero blocks, the character multiplier leaves a nonzero top coefficient. -/
theorem twoBlockEliminant_ne_zero (s : σ → K) {g : K} (hg : g ≠ 1)
    {P Q : MvPolynomial σ K} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    polynomialTranslation s P * Q - C g * (P * polynomialTranslation s Q) ≠ 0 := by
  classical
  have hPQ := mul_ne_zero hP hQ
  obtain ⟨d, hd, he⟩ := (P * Q).support.exists_mem_eq_sup (by simpa using hPQ)
    (fun a : σ →₀ ℕ => a.sum fun _ e => e)
  have hdeg : (d.sum fun _ e => e) = P.totalDegree + Q.totalDegree :=
    he.symm.trans (totalDegree_mul_of_isDomain hP hQ)
  have hleft := coeff_translate_mul_top s P Q d hdeg
  have hright : (P * polynomialTranslation s Q).coeff d = (P * Q).coeff d := by
    simpa only [mul_comm] using coeff_translate_mul_top s Q P d (hdeg.trans (Nat.add_comm _ _))
  intro hz
  have h := congrArg (fun F : MvPolynomial σ K => F.coeff d) hz
  simp [coeff_C_mul, hleft, hright] at h
  exact (mul_ne_zero (sub_ne_zero.mpr hg.symm) (mem_support_iff.mp hd))
    (by simpa only [sub_mul, one_mul] using h)

/-- The two relations yield a nonzero polynomial of degree at most the sum of the
two block degrees, vanishing at every base point. The node family may have repetitions. -/
theorem exists_vanishing_polynomial_of_two_blocks
    (y : ι → σ → K) (s : σ → K) (r : ι → K) {g : K} (hg : g ≠ 1)
    (hr : ∀ i, r i ≠ 0) {P Q : MvPolynomial σ K} (hnz : P ≠ 0 ∨ Q ≠ 0)
    {d₀ d₁ : ℕ} (hP : P.totalDegree ≤ d₀) (hQ : Q.totalDegree ≤ d₁)
    (hbase : ∀ i, eval (y i) P + r i * eval (y i) Q = 0)
    (hshift : ∀ i, eval (y i + s) P + r i * g * eval (y i + s) Q = 0) :
    ∃ F : MvPolynomial σ K, F ≠ 0 ∧ F.totalDegree ≤ d₀ + d₁ ∧
      ∀ i, eval (y i) F = 0 := by
  by_cases hp : P = 0
  · refine ⟨Q, hnz.resolve_left (not_not.mpr hp), by omega, fun i => ?_⟩
    have h : r i * eval (y i) Q = 0 := by simpa [hp] using hbase i
    exact (mul_eq_zero.mp h).resolve_left (hr i)
  by_cases hq : Q = 0
  · exact ⟨P, hp, by omega, fun i => by simpa [hq] using hbase i⟩
  refine ⟨_, twoBlockEliminant_ne_zero s hg hp hq, (totalDegree_sub _ _).trans
    (max_le ?_ ?_), fun i => ?_⟩
  · exact (totalDegree_mul _ _).trans
      (Nat.add_le_add ((translation_degree_le s P).trans hP) hQ)
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add hP ((translation_degree_le s Q).trans hQ))
  · simp only [map_sub, map_mul, eval_C, eval_polynomialTranslation]
    change eval (y i + s) P * eval (y i) Q - g * (eval (y i) P * eval (y i + s) Q) = 0
    linear_combination eval (y i) Q * hshift i - g * eval (y i + s) Q * hbase i

/-- Change the origin of the box coordinates after eliminating the character. -/
theorem exists_vanishing_polynomial_of_translated_nodes (z : ι → σ → K) (u : σ → K)
    {D : ℕ} {P : MvPolynomial σ K} (hp : P ≠ 0) (hd : P.totalDegree ≤ D)
    (hv : ∀ i, eval (z i + u) P = 0) :
    ∃ F : MvPolynomial σ K, F ≠ 0 ∧ F.totalDegree ≤ D ∧ ∀ i, eval (z i) F = 0 :=
  ⟨polynomialTranslation u P, translation_ne_zero u hp, (translation_degree_le u P).trans hd,
    fun i => (eval_polynomialTranslation (z i) u P).trans (hv i)⟩

end AbcSubexp
