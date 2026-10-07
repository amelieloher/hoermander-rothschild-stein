-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralDirections
public import RothschildStein.P1.PaddingCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Base derivatives commute with integration of an actual
joined-coordinate compact smooth function. -/
theorem fderiv_joinPoint_fiberIntegral_apply {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {φ : (Fin (n + d) → ℝ) → B}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => ∫ z : Fin d → ℝ, φ (joinPoint y z)) x v =
      ∫ z : Fin d → ℝ, fderiv ℝ φ (joinPoint x z) (joinPoint v (0 : Fin d → ℝ)) := by
  let F : ((Fin n → ℝ) × (Fin d → ℝ)) → B := φ ∘ paddingJoinCLM n d
  have hF : ContDiff ℝ 1 F := (hφ.of_le (by simp)).comp (paddingJoinCLM n d).contDiff
  have hFc : HasCompactSupport F :=
    hc.comp_homeomorph (paddingCoordinates n d).symm.toHomeomorph
  have hi : (fun y => ∫ z, F (y, z)) =
      (fun y => ∫ z : Fin d → ℝ, φ (joinPoint y z)) := by
    funext y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => congrArg φ (paddingJoinCLM_apply n d y z)
  rw [← hi, fderiv_fiberIntegral_apply hF hFc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have he : fderiv ℝ F (x, z) = (fderiv ℝ φ (paddingJoinCLM n d (x, z))).comp
      (paddingJoinCLM n d) :=
    ((hφ.differentiable (by simp) _).hasFDerivAt.comp (x, z)
      (paddingJoinCLM n d).hasFDerivAt).fderiv
  change fderiv ℝ F (x, z) (v, (0 : Fin d → ℝ)) =
    fderiv ℝ φ (joinPoint x z) (joinPoint v (0 : Fin d → ℝ))
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, paddingJoinCLM_apply]

/-- Every added-coordinate derivative has zero fiber integral
in the joined-coordinate convention. -/
theorem integral_fderiv_joinPoint_vertical_eq_zero {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {φ : (Fin (n + d) → ℝ) → B}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x : Fin n → ℝ) (v : Fin d → ℝ) :
    (∫ z : Fin d → ℝ, fderiv ℝ φ (joinPoint x z)
      (joinPoint (0 : Fin n → ℝ) v)) = 0 := by
  let F : ((Fin n → ℝ) × (Fin d → ℝ)) → B := φ ∘ paddingJoinCLM n d
  have hF : ContDiff ℝ 1 F := (hφ.of_le (by simp)).comp (paddingJoinCLM n d).contDiff
  have hFc : HasCompactSupport F :=
    hc.comp_homeomorph (paddingCoordinates n d).symm.toHomeomorph
  have he : ∀ p, fderiv ℝ F p = (fderiv ℝ φ (paddingJoinCLM n d p)).comp
      (paddingJoinCLM n d) := fun p =>
    ((hφ.differentiable (by simp) _).hasFDerivAt.comp p
      (paddingJoinCLM n d).hasFDerivAt).fderiv
  have h := integral_fderiv_fiberDirection_eq_zero hF hFc x v
  simpa only [he, ContinuousLinearMap.comp_apply, paddingJoinCLM_apply] using h

end RothschildStein.P1
