-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Joint measurability of the defining nonnegative integrand
(BB pp. 118–119; measurability). -/
theorem measurable_lgroupConvolution_integrand {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => f p.1 * g (G.mul (G.inv p.1) p.2)) :=
  (hf.comp measurable_fst).mul (hg.comp
    ((continuous_mul G).comp (((continuous_inv G).comp continuous_fst).prodMk continuous_snd)).measurable)

/-- Nonnegative group convolution is measurable by the multiplicative convolution theorem (BB pp. 118–119). -/
theorem measurable_lgroupConvolution {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (lgroupConvolution G f g) := by
  have : SFinite (volume : Measure (Carrier G)) := inferInstanceAs (SFinite (volume : Measure (Fin N → ℝ)))
  let : MeasurableMul₂ (Carrier G) := ⟨(continuous_mul G).measurable⟩
  let : MeasurableInv (Carrier G) := ⟨(continuous_inv G).measurable⟩
  exact MeasureTheory.measurable_mlconvolution (G := Carrier G) _ hf hg

/-- Weighted Tonelli identity for nonnegative group convolution
(BB pp. 118–119; Tonelli). -/
theorem lintegral_lgroupConvolution_mul {f g h : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ x, lgroupConvolution G f g x * h x) =
      ∫⁻ y, ∫⁻ w, f y * g w * h (G.mul y w) := by
  have hinner (x : Fin N → ℝ) :
      lgroupConvolution G f g x * h x =
        ∫⁻ y, f y * g (G.mul (G.inv y) x) * h x := by
    exact (lintegral_mul_const'' (h x)
      ((hf.mul (hg.comp ((continuous_mul G).comp
        ((continuous_inv G).prodMk continuous_const)).measurable)).aemeasurable)).symm
  simp_rw [hinner]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro y
    have ht := (measurePreserving_leftTranslation G y).lintegral_comp_emb
      ((measurePreserving_leftTranslation G y).measurable.measurableEmbedding
        (leftTranslation_bijective G y).injective)
      (fun x => f y * g (G.mul (G.inv y) x) * h x)
    simpa only [← mul_assoc G (G.inv y), inv_mul, zero_mul] using ht.symm
  · exact (((measurable_lgroupConvolution_integrand G hf hg).mul
      (hh.comp measurable_snd)).comp measurable_swap).aemeasurable

/-- The integral of a nonnegative convolution is the product of
integrals, with no finiteness assumption (BB pp. 118–119; Tonelli). -/
theorem lintegral_lgroupConvolution {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, lgroupConvolution G f g x) = (∫⁻ y, f y) * ∫⁻ w, g w := by
  have h := lintegral_lgroupConvolution_mul G hf hg (measurable_const (a := (1 : ℝ≥0∞)))
  simpa only [mul_one, lintegral_const_mul _ hg, lintegral_mul_const _ hf] using h

end RothschildStein.G2
