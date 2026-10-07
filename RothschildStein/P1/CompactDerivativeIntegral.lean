-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSupport
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- The integral of a derivative of a compactly supported
C¹ function vanishes. This is the analytic identity for the added
diffusion directions in the arbitrary-distribution tensor. -/
theorem integral_fderiv_compactSupport_eq_zero {d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {g : (Fin d → ℝ) → B} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : Fin d → ℝ) :
    (∫ z, fderiv ℝ g z v) = 0 := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdc : Continuous (fun z => fderiv ℝ g z v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdcs : HasCompactSupport (fun z => fderiv ℝ g z v) := hgc.fderiv_apply ℝ v
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin d → ℝ)))
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := fun _ : Fin d → ℝ => (1 : ℝ)) (f' := fun _ => (0 : ℝ))
    (g := g) (g' := fun z => fderiv ℝ g z v) (v := v)
    (by simp)
    (by simpa using hdc.integrable_of_hasCompactSupport hdcs)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
    (fun z _ => (hasFDerivAt_const (1 : ℝ) z).hasLineDerivAt v)
    (fun z _ => (hd z).hasFDerivAt.hasLineDerivAt v)
  simpa using h

end RothschildStein.P1
