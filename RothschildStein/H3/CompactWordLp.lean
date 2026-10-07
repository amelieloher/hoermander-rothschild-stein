-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- Compact smooth inputs and smooth fields give all classical word
 actions finite Lp norms, including the endpoint exponents. -/
theorem memLp_wordDerivative_compact {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (I : List (Fin m))
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) (p : ℝ≥0∞) : MemLp (wordDerivative X I u) p volume := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative X I u) :=
    contDiffOn_univ.mp (RothschildStein.S.contDiffOn_wordDerivative ⊤ X
      (fun i => (hX i).contDiffOn) I u hu.contDiffOn)
  exact hs.continuous.memLp_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (RothschildStein.S.tsupport_wordDerivative_subset X I u))

end RothschildStein.H3
