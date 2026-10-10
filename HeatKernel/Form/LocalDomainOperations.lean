-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalEnergyAlgebra
import Mathlib.Tactic.Linter

/-! # Restriction and linear operations in local horizontal energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Restricting the ambient open set preserves local energy membership. -/
theorem MemLocalEnergy.restrict {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (W : Opens (Fin N → ℝ)) (hWU : W ≤ U) :
    MemLocalEnergy W X f := by
  refine ⟨hf.1.mono_measure (Measure.restrict_mono hWU le_rfl), fun V hc hs => ?_⟩
  exact hf.2 V hc (hs.trans hWU)

end HeatKernel
