-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralDomination
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1

/-- Differentiation of fiber integration in the base directions,
with the dominating function derived from compact support. -/
theorem hasFDerivAt_fiberIntegral {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => ∫ z, F (y, z))
      (∫ z, (fderiv ℝ F (x, z)).comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) x := by
  let D : ((Fin n → ℝ) × (Fin d → ℝ)) → ((Fin n → ℝ) →L[ℝ] B) :=
    fun p => (fderiv ℝ F p).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))
  have hD : Continuous D :=
    hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  have hDc : HasCompactSupport D :=
    (hFc.fderiv ℝ).comp_left (g := fun L : ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] B => L.comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) (by simp)
  obtain ⟨b, hb, hbound⟩ := exists_integrable_fiberMajorant hD hDc
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := b) (F' := fun y z => D (y, z)) (Filter.univ_mem)
  · exact Filter.Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact integrable_fiberSection hF.continuous hFc x
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z y _ => hbound y z
  · exact hb
  · exact Filter.Eventually.of_forall fun z y _ =>
      (hF.differentiable (by norm_num) (y, z)).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_left y z)

end RothschildStein.P1
