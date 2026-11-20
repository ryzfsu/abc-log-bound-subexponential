/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp.S6_HittingPrime.CutoffMargin
public import Subexp.S6_HittingPrime.DepthGrowth
public import Subexp.S6_HittingPrime.RadiusMargin
public import Subexp.S6_HittingPrime.PrimeSpectrum

/-! # Native conditions for the choice of a prime and a list -/

@[expose] public section

noncomputable section

open Finset Real
open AbcSubexp.Parameters

namespace AbcSubexp

/-- The enlarged third window lies in the allowed native interval on a uniform tail. -/
theorem Contact.exists_hittingWindow_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ {t : AbcTwoNinths.Basic.Triple} (c : Contact ε t), X ≤ t.thirdLogRadical →
      (depthParameter ε + 1) ^ 2 ≤ c.degree ∧ c.degree + c.hittingWindow ≤ c.radius := by
  have he : 0 < exponent ε := lt_min hε (by norm_num)
  obtain ⟨X, hX⟩ := Contact.eventually_log_cutoff_margin hε
  obtain ⟨Y, hY⟩ := Contact.exists_depth_degree_threshold hε
    (4 * ((dimension ε : ℝ) + 2) / exponent ε)
  refine ⟨max X Y, ?_⟩
  intro t c hxy
  obtain ⟨hpos, hupper⟩ := hX c ((le_max_left ..).trans hxy)
  obtain ⟨hshare, hdegree⟩ := hY t c ((le_max_right ..).trans hxy)
  exact ⟨hdegree, c.degree_add_hittingWindow_le_radius hε hpos hupper
    (by simpa only [mul_comm (c.depth : ℝ)] using (div_le_iff₀ he).mp hshare)⟩

/-- On the native tail a strict budget for all-row misses supplies the complete witness. -/
theorem exists_hittingPrime_of_eventual_miss_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} (g : GroupedTuple c), X ≤ t.thirdLogRadical →
      ∀ bad : Finset ℕ, bad.card < (thirdWindowPrimes c.hittingWindow).card →
      (∀ q ∈ thirdWindowPrimes c.hittingWindow, (∀ b, ¬ ∀ i, ∃ z : ℤ,
        |(q : ℝ) * g.slope b i - (i.val : ℝ) / dimension ε - (z : ℝ)| < phaseTolerance ε) →
        q ∈ bad) → Nonempty (HittingPrime g) := by
  obtain ⟨X, hX⟩ := Contact.exists_hittingWindow_bounds hε
  refine ⟨X, ?_⟩
  intro t c g hx bad hcard hmiss
  obtain ⟨hdegree, hradius⟩ := hX c hx
  exact exists_hittingPrime_of_miss_budget g bad hdegree hradius hcard hmiss

/-- A finite Fourier certificate on any single preassigned native row suffices
on the same uniform tail for all grouped tuples and all spectra. -/
theorem exists_hittingPrime_of_weighted_prime_spectrum {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ {t : AbcTwoNinths.Basic.Triple} {c : Contact ε t} (g : GroupedTuple c), X ≤ t.thirdLogRadical →
      ∀ (b : Fin ⌊t.thirdLogRadical ^ ((1 : ℝ) / 3)⌋₊) {κ : Type} [Fintype κ] [Zero κ] [DecidableEq κ]
        (test : ℕ → ℝ) (a node : κ → ℂ) (center off err : ℝ),
      let P := thirdWindowPrimes c.hittingWindow
      (∀ q ∈ P, (¬ ∀ i, ∃ z : ℤ,
        |(q : ℝ) * g.slope b i - (i.val : ℝ) / dimension ε - (z : ℝ)| < phaseTolerance ε) →
        test q ≤ off) →
      (∀ q ∈ P, (test q : ℂ) = ∑ k, a k * node k ^ q) →
      a 0 = (center : ℂ) → node 0 = 1 →
      (∑ k ∈ (univ : Finset κ).erase 0, ‖a k‖ *
        ‖∑ q ∈ P, (log (q : ℝ) : ℂ) * node k ^ q‖ ≤ err) →
      err < (center - off) * ∑ q ∈ P, log (q : ℝ) →
      Nonempty (HittingPrime g) := by
  classical
  obtain ⟨X, hX⟩ := exists_hittingPrime_of_eventual_miss_budget hε
  refine ⟨X, ?_⟩
  intro t c g hx b κ _ _ _ test a node center off err
  dsimp only
  intro hmiss hexp hc hz herr hgap
  let P := thirdWindowPrimes c.hittingWindow
  have hw (q : ℕ) (hq : q ∈ P) : 0 ≤ log (q : ℝ) := by
    exact log_nonneg (by exact_mod_cast (mem_thirdWindowPrimes.mp hq).1.one_le)
  obtain ⟨q, hq, hit⟩ := exists_prime_hit_of_weighted_spectrum P _ test a node
    (fun q => log (q : ℝ)) hw hmiss hexp hc hz herr hgap
  apply hX g hx (P.erase q) (card_erase_lt_of_mem hq)
  intro v hv hm
  exact mem_erase.mpr ⟨fun h => hm b (h.symm ▸ hit), hv⟩

end AbcSubexp
