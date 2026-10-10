-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothGradientCore
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Scalar composition of smooth gradient pairs

The ordinary scalar chain rule preserves the smooth compact gradient core for smooth scalar
functions vanishing at zero. Its derivative formula fixes the pointwise convention for passing
to the closed energy domain.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- The scalar chain rule along a vector field. -/
theorem fieldDerivative_comp {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ))
    {η : ℝ → ℝ} {f : (Fin N → ℝ) → ℝ} (hη : Differentiable ℝ η)
    (hf : Differentiable ℝ f) (x : Fin N → ℝ) :
    fieldDerivative V (η ∘ f) x = deriv η (f x) * fieldDerivative V f x := by
  have hd := ((hη (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt).fderiv
  exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (V x)) hd

end HeatKernel
