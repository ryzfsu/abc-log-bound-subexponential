/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Tactic

/-!
# Distinct auxiliary prime tuples

When the prime cluster has more than the square of the tuple length, at least
half of all ordered tuples have distinct entries. This gives the denominator
in the bad-tuple comparison in Section 4.
-/

@[expose] public section

namespace AbcSubexp.TupleCounting

private theorem collisionLossBound (n d : ℕ) (hd : d ≤ n) :
    2 * (n : ℝ) * n ^ d ≤ 2 * n * (n.descFactorial d : ℝ) +
      (d : ℝ) * (d - 1) * n ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hdn : d ≤ n := by omega
    have h := mul_le_mul_of_nonneg_left (ih hdn) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hf : (n.descFactorial d : ℝ) ≤ (n : ℝ) ^ d := by
      exact_mod_cast Nat.descFactorial_le_pow n d
    have he := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ 2 * n * d by positivity)
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hdn, Nat.cast_succ, pow_succ]
    linarith only [h, he]

/-- At least half the ordered tuples have distinct entries once the square of
the number of slots is smaller than the prime cluster. -/
theorem distinctTupleCountLower (Q : Type*) [Fintype Q] (d : ℕ)
    (hcount : d ^ 2 < Fintype.card Q) :
    (Fintype.card Q : ℝ) ^ d / 2 ≤ Fintype.card (Fin d ↪ Q) := by
  classical
  let n := Fintype.card Q
  have hn : 0 < n := (Nat.zero_le _).trans_lt hcount
  have hd : d ≤ n := le_trans (by nlinarith : d ≤ d ^ 2) hcount.le
  have hs : (d : ℝ) * (d - 1) ≤ n := by
    have hsq : (d : ℝ) ^ 2 < n := by exact_mod_cast hcount
    nlinarith
  have hloss := mul_le_mul_of_nonneg_right hs (show 0 ≤ (n : ℝ) ^ d by positivity)
  have hbound := collisionLossBound n d hd
  rw [Fintype.card_embedding_eq, Fintype.card_fin]
  change (n : ℝ) ^ d / 2 ≤ (n.descFactorial d : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_of_mul_le_mul_left (a := (n : ℝ)) _ hn')
  linarith only [hbound, hloss]

end AbcSubexp.TupleCounting
