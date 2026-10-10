-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Differentials of spatial sections of spacetime functions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HeatKernel

/-- The differential of a spatial section is the spacetime differential applied
to a vector with zero time component. -/
theorem fderiv_spatial_section_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × E → F} {t : ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (t, x)) (v : E) :
    fderiv ℝ (fun y => u (t, y)) x v = fderiv ℝ u (t, x) (0, v) := by
  have hd := hu.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  simpa [Function.comp_def] using congrArg (fun L => L v) hd.fderiv

end HeatKernel
