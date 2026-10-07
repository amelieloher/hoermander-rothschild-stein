-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSmoothness
public import RothschildStein.P1.PaddingCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Smoothness of the joined-coordinate fiber integral;
no smooth-fiber-average hypothesis is added to the lifting interface. -/
theorem contDiff_joinPoint_fiberIntegral {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {φ : (Fin (n + d) → ℝ) → B}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z : Fin d → ℝ, φ (joinPoint x z)) := by
  let F : ((Fin n → ℝ) × (Fin d → ℝ)) → B :=
    φ ∘ (paddingCoordinates n d).symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    hφ.comp (paddingCoordinates n d).symm.contDiff
  have hFc : HasCompactSupport F :=
    hc.comp_homeomorph (paddingCoordinates n d).symm.toHomeomorph
  have he : F = fun p => φ (joinPoint p.1 p.2) := by
    funext p
    change φ (paddingJoinCLM n d p) = φ (joinPoint p.1 p.2)
    congr 1
    exact paddingJoinCLM_apply n d p.1 p.2
  simpa only [he] using contDiff_fiberIntegral hF hFc

end RothschildStein.P1
