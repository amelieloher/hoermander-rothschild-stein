-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeightedParameterIntegral
public import RothschildStein.Definitions.fieldDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory RothschildStein
namespace HeatKernel

/-- A field derivative passes through an integral of a smooth compact kernel against an
integrable weight. -/
theorem fieldDerivative_integral_weighted_compact_parameter
    {N : ℕ} {Φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    {f : (Fin N → ℝ) → ℝ} (hf : IntegrableOn f K volume)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    fieldDerivative V (fun z => ∫ a in K, f a * Φ (z,a)) x =
      ∫ a in K, f a * fieldDerivative V (fun z => Φ (z,a)) x := by
  let D := fun p => (fderiv ℝ Φ p).comp
    (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))
  have hD : Continuous D := (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hi : IntegrableOn (fun a => f a • D (x,a)) K volume :=
    hf.smul_continuousOn
      (hD.comp (continuous_const.prodMk continuous_id)).continuousOn hK
  have hd := hasFDerivAt_integral_weighted_compact_parameter hΦ hK hf x
  change fderiv ℝ (fun z => ∫ a in K, f a * Φ (z,a)) x (V x) = _
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro a
  have hdf : HasFDerivAt Φ (fderiv ℝ Φ (x,a)) (x,a) :=
    (hΦ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun z : Fin N → ℝ => (z,a))
      (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ)) x := by
    have he : (ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
        (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) =
        ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ) :=
      ContinuousLinearMap.ext fun _ => rfl
    rw [← he]
    exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const a x)
  have hp : HasFDerivAt (fun z => Φ (z,a)) (D (x,a)) x := hdf.comp x hin
  change f a * D (x,a) (V x) = f a * fderiv ℝ (fun z => Φ (z,a)) x (V x)
  rw [hp.fderiv]

end HeatKernel
