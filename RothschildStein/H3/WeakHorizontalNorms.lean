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
open TopologicalSpace
open scoped ENNReal BigOperators

/-- The horizontal first derivative norm as a finite sum of fixed weak norms. -/
def horizontalWeakENorm {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u

/-- The sum of horizontal square norms, bounded by the full second jet norm. -/
def horizontalSquareWeakENorm {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ i : Fin q, weakWordENorm X Ω [i.succ,i.succ] p u

/-- Sobolev membership makes the horizontal first derivative sum finite. -/
theorem horizontalWeakENorm_lt_top {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) : horizontalWeakENorm X Ω p u < ⊤ := by
  unfold horizontalWeakENorm
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply weakWordENorm_lt_top_of_memSobolev driftWeight X Ω 2 p u hu
  simp [S.mem_wordFamily_iff, wordWeight, driftWeight, Fin.succ_ne_zero]

/-- Sobolev membership makes the horizontal square sum finite. -/
theorem horizontalSquareWeakENorm_lt_top {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) : horizontalSquareWeakENorm X Ω p u < ⊤ := by
  unfold horizontalSquareWeakENorm
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply weakWordENorm_lt_top_of_memSobolev driftWeight X Ω 2 p u hu
  simp [S.mem_wordFamily_iff, wordWeight, driftWeight, Fin.succ_ne_zero]

end RothschildStein.H3
