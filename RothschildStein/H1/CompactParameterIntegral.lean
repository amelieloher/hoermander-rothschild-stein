-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- A joint C¹ integrand can be differentiated in the
parameter under an integral over a fixed compact set. -/
theorem hasFDerivAt_integral_compact_parameter
    {Φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (x₀ : Fin N → ℝ) :
    HasFDerivAt (fun x => ∫ a in K, Φ (x, a))
      (∫ a in K, (fderiv ℝ Φ (x₀, a)).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))) x₀ := by
  let D := fun p => (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))
  have hD : Continuous D := (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hprod : IsCompact (Metric.closedBall x₀ 1 ×ˢ K) := (isCompact_closedBall x₀ 1).prod hK
  obtain ⟨C, hC⟩ := hprod.exists_bound_of_continuousOn hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x₀ 1) (F := fun x a => Φ (x,a)) (F' := fun x a => D (x,a))
    (bound := fun _ => C) (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x =>
      ((hΦ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro x hx
    exact hC (x,a) ⟨Metric.ball_subset_closedBall hx, ha⟩
  · exact continuousOn_const.integrableOn_compact hK
  · apply Eventually.of_forall
    intro a x hx
    have hd : HasFDerivAt Φ (fderiv ℝ Φ (x,a)) (x,a) :=
      (hΦ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun y : Fin N → ℝ => (y,a))
        (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ)) x := by
      have he : (ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
          (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) =
          ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ) := by
        exact ContinuousLinearMap.ext fun _ => rfl
      rw [← he]
      exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const a x)
    exact hd.comp x hi

end RothschildStein.H1
