-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.BallVolume
public import HeatKernel.Geometry.SmoothCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Smooth horizontal ball cutoffs and their bounded derivatives. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set RothschildStein
open scoped BigOperators
namespace HeatKernel

/-- The horizontal gradient norm of a differentiable scalar function in coordinates. -/
def horizontalGradientNorm {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, (fderiv ℝ f x (X i x)) ^ 2)

end HeatKernel
