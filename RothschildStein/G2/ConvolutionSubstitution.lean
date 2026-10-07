-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The map y ↦ y⁻¹∘x preserves volume
(BB (3.27), pp. 118–119). -/
theorem measurePreserving_invRightAt (x : Fin N → ℝ) :
    MeasurePreserving (fun y : Fin N → ℝ => G.mul (G.inv y) x) :=
  (measurePreserving_rightTranslation G x).comp (measurePreserving_inv G)

/-- The map w ↦ x∘w⁻¹ preserves volume
(BB (3.27), pp. 118–119). -/
theorem measurePreserving_leftInvAt (x : Fin N → ℝ) :
    MeasurePreserving (fun w : Fin N → ℝ => G.mul x (G.inv w)) :=
  (measurePreserving_leftTranslation G x).comp (measurePreserving_inv G)

/-- The first and second BB Bochner formulas agree. The equality
also respects the Bochner default outside the absolute-convergence domain;
no convergence is inferred there (BB (3.27), p. 119). -/
theorem groupConvolution_eq_integral {𝕜 : Type*} [RCLike 𝕜]
    (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) :
    groupConvolution G f g x = ∫ y, f y * g (G.mul (G.inv y) x) := by
  rw [groupConvolution_def]
  let F : (Fin N → ℝ) → 𝕜 := fun y => f y * g (G.mul (G.inv y) x)
  have hp := measurePreserving_leftInvAt G x
  have he : MeasurableEmbedding (fun w : Fin N → ℝ => G.mul x (G.inv w)) :=
    hp.measurable.measurableEmbedding
      ((leftTranslation_bijective G x).comp (inv_bijective G)).injective
  have h := hp.integral_comp he F
  simpa only [F, inv_product, inv_inv, mul_assoc, inv_mul, mul_zero] using h

/-- Null changes in either slot change the nonnegative convolution
at no point (BB p. 119; measurability/pointwise well-definedness). -/
theorem lgroupConvolution_congr_ae {f f' g g' : (Fin N → ℝ) → ℝ≥0∞}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') (x : Fin N → ℝ) :
    lgroupConvolution G f g x = lgroupConvolution G f' g' x := by
  rw [lgroupConvolution_def, lgroupConvolution_def]
  apply lintegral_congr_ae
  have hgc := (measurePreserving_invRightAt G x).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hf, hgc] with y hy hgy
  simp only [Function.comp_apply] at hgy
  rw [hy, hgy]

/-- Null changes in either slot change the Bochner convolution at
no point (BB pp. 118–119; well-definedness). -/
theorem groupConvolution_congr_ae {𝕜 : Type*} [RCLike 𝕜]
    {f f' g g' : (Fin N → ℝ) → 𝕜}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') (x : Fin N → ℝ) :
    groupConvolution G f g x = groupConvolution G f' g' x := by
  rw [groupConvolution_eq_integral, groupConvolution_eq_integral]
  apply integral_congr_ae
  have hgc := (measurePreserving_invRightAt G x).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hf, hgc] with y hy hgy
  simp only [Function.comp_apply] at hgy
  rw [hy, hgy]

/-- The norm of the Bochner convolution is controlled by the
nonnegative convolution of norms (BB p. 119, absolute-convergence). -/
theorem enorm_groupConvolution_le {𝕜 : Type*} [RCLike 𝕜]
    (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) :
    ‖groupConvolution G f g x‖ₑ ≤ lgroupConvolution G (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x := by
  rw [groupConvolution_eq_integral, lgroupConvolution_def]
  simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
    (fun y => f y * g (G.mul (G.inv y) x))

end RothschildStein.G2
