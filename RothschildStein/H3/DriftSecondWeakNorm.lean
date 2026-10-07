-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakJetNormFacts
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- All words of drift weight exactly two, including mixed words. -/
def driftSecondWordFamily (q : ℕ) : Finset (List (Fin (q+1))) :=
  (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 2)

/-- The complete weighted second-order weak norm used in the
half-radius estimate. -/
def driftSecondWeakENorm {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ driftSecondWordFamily q, weakWordENorm X Ω I p u

/-- The finite family is precisely the words of drift weight two. -/
theorem mem_driftSecondWordFamily_iff {q : ℕ} (I : List (Fin (q+1))) :
    I ∈ driftSecondWordFamily q ↔ wordWeight driftWeight I = 2 := by
  simp only [driftSecondWordFamily, Finset.mem_filter, S.mem_wordFamily_iff]
  exact ⟨And.right, fun h => ⟨h.le, h⟩⟩

/-- Actual Sobolev membership makes the full second norm finite. -/
theorem driftSecondWeakENorm_lt_top {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) : driftSecondWeakENorm X Ω p u < ⊤ := by
  unfold driftSecondWeakENorm
  apply ENNReal.sum_lt_top.mpr
  intro I hI
  exact weakWordENorm_lt_top_of_memSobolev driftWeight X Ω 2 p u hu I
    (Finset.mem_filter.mp hI).1

/-- Uniform individual word bounds sum with the exact finite-family
cardinality, with no need to count words in the analytic argument. -/
theorem driftSecondWeakENorm_le_of_word_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (B : ℝ≥0∞)
    (hb : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
      weakWordENorm X Ω I p u ≤ B) :
    driftSecondWeakENorm X Ω p u ≤ (driftSecondWordFamily q).card * B := by
  have hs := Finset.sum_le_sum (s := driftSecondWordFamily q)
    (fun I hI => hb I ((mem_driftSecondWordFamily_iff I).mp hI))
  simpa only [driftSecondWeakENorm, Finset.sum_const, nsmul_eq_mul] using hs

end RothschildStein.H3
