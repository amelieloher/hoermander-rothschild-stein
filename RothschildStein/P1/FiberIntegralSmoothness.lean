-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Integrating a compactly supported smooth function over the
added coordinates gives a smooth function on the base. -/
theorem contDiff_fiberIntegral {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, F (x, z)) := by
  apply contDiff_infty.mpr
  intro m
  induction m generalizing B with
  | zero =>
      apply contDiff_zero.mpr
      apply Differentiable.continuous (𝕜 := ℝ)
      intro x
      exact (hasFDerivAt_fiberIntegral (hF.of_le (by simp)) hFc x).differentiableAt
  | succ m ih =>
      let D : ((Fin n → ℝ) × (Fin d → ℝ)) → ((Fin n → ℝ) →L[ℝ] B) :=
        fun p => (fderiv ℝ F p).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))
      have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
        (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
      have hDc : HasCompactSupport D :=
        (hFc.fderiv ℝ).comp_left (g := fun L : ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] B => L.comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) (by simp)
      have hder : ∀ x, HasFDerivAt (fun y => ∫ z, F (y, z))
          (∫ z, D (x, z)) x :=
        fun x => hasFDerivAt_fiberIntegral (hF.of_le (by simp)) hFc x
      change ContDiff ℝ ((m : WithTop ℕ∞) + 1) (fun x => ∫ z, F (x, z))
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
      · simp
      · have he : fderiv ℝ (fun y => ∫ z, F (y, z)) =
            fun x => ∫ z, D (x, z) := funext fun x => (hder x).fderiv
        rw [he]
        exact ih hD hDc

end RothschildStein.P1
