-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- Joint strong measurability of the scalar integrand
(BB pp. 118–119; measurability). -/
theorem stronglyMeasurable_groupConvolution_integrand {f g : (Fin N → ℝ) → 𝕜}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      f p.1 * g (G.mul (G.inv p.1) p.2)) :=
  (hf.comp_measurable measurable_fst).mul (hg.comp_measurable
    ((continuous_mul G).comp (((continuous_inv G).comp continuous_fst).prodMk continuous_snd)).measurable)

/-- The Bochner convolution is strongly measurable
(BB pp. 118–119; measurability). -/
theorem stronglyMeasurable_groupConvolution {f g : (Fin N → ℝ) → 𝕜}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (groupConvolution G f g) := by
  have h := (stronglyMeasurable_groupConvolution_integrand G hf hg).integral_prod_left' (μ := volume)
  have he : groupConvolution G f g = fun x => ∫ y, f y * g (G.mul (G.inv y) x) :=
    funext (groupConvolution_eq_integral G f g)
  rw [he]
  exact h

/-- Measurable representatives give a strongly measurable
convolution for all almost-everywhere strongly measurable inputs (BB p. 119). -/
theorem aestronglyMeasurable_groupConvolution {f g : (Fin N → ℝ) → 𝕜}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (groupConvolution G f g) volume := by
  have he : groupConvolution G f g = groupConvolution G (hf.mk f) (hg.mk g) :=
    funext (groupConvolution_congr_ae G hf.ae_eq_mk hg.ae_eq_mk)
  rw [he]
  exact (stronglyMeasurable_groupConvolution G hf.stronglyMeasurable_mk
    hg.stronglyMeasurable_mk).aestronglyMeasurable

end RothschildStein.G2
