-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralDerivative
public import RothschildStein.P1.CompactDerivativeIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Base directional derivatives commute with actual fiber
integration; compact support supplies the integrability of the derivative. -/
theorem fderiv_fiberIntegral_apply {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => ∫ z, F (y, z)) x v =
      ∫ z, fderiv ℝ F (x, z) (v, (0 : Fin d → ℝ)) := by
  let D : ((Fin n → ℝ) × (Fin d → ℝ)) → ((Fin n → ℝ) →L[ℝ] B) :=
    fun p => (fderiv ℝ F p).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))
  have hD : Continuous D :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hDc : HasCompactSupport D :=
    (hc.fderiv ℝ).comp_left
      (g := fun L : ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] B => L.comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) (by simp)
  rw [(hasFDerivAt_fiberIntegral hF hc x).fderiv]
  exact ContinuousLinearMap.integral_apply (integrable_fiberSection hD hDc x) v

/-- Added-coordinate directional derivatives integrate to
zero on every fiber, by compact-support integration by parts. -/
theorem integral_fderiv_fiberDirection_eq_zero {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (x : Fin n → ℝ) (v : Fin d → ℝ) :
    (∫ z, fderiv ℝ F (x, z) ((0 : Fin n → ℝ), v)) = 0 := by
  have hg : ContDiff ℝ 1 (fun z => F (x, z)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have he : ∀ z, fderiv ℝ (fun w => F (x, w)) z =
      (fderiv ℝ F (x, z)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin d → ℝ)) := fun z =>
    ((hF.differentiable (by norm_num) (x, z)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right x z)).fderiv
  have h := integral_fderiv_compactSupport_eq_zero hg (hasCompactSupport_fiberSection hc x) v
  simpa only [he, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using h

end RothschildStein.P1
