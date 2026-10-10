-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScaledEnergyOperators
import Mathlib.Tactic.Linter

/-! # Scalar scaling of the horizontal form and its inclusion -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Horizontal energy scales bilinearly under real scalar multiplication. -/
theorem horizontalEnergy_smul_smul {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (c d : ℝ) (u v : energyGraph U X) :
    horizontalEnergy U X (c • u) (d • v) = c * d * horizontalEnergy U X u v := by
  simp only [horizontalEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

end HeatKernel
