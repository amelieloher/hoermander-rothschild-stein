-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurIntegralExistence
public import RothschildStein.P1.BilinearTranspose

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- Finite Schur masses make the bilinearly tested kernel
integrable on the product. This discharges Fubini for positive types
using an L1 input and a bounded output test. -/
theorem schur_bilinear_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K : α → β → ℝ) (hK : Measurable (Function.uncurry K))
    (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) (hfi : Integrable f ν)
    (g : α → ℝ) (hg : Measurable g) (hgt : MemLp g ⊤ μ) :
    Integrable (fun p : α × β => g p.1 * (K p.1 p.2 * f p.2)) (μ.prod ν) := by
  let K₁ : α → β → ℝ := fun x y => |K x y|
  have hK₁ : Measurable (Function.uncurry K₁) := by
    change Measurable (fun p : α × β => |K p.1 p.2|)
    have hn := hK.norm
    change Measurable (fun p : α × β => ‖K p.1 p.2‖) at hn
    simpa only [Real.norm_eq_abs] using hn
  have hrow₁ : ∀ x, (∫⁻ y, ‖K₁ x y‖ₑ ∂ν) ≤ A := by
    intro x
    simpa only [K₁, Real.enorm_eq_ofReal_abs, abs_abs] using hrow x
  have hcolumn₁ : ∀ y, (∫⁻ x, ‖K₁ x y‖ₑ ∂μ) ≤ B := by
    intro y
    simpa only [K₁, Real.enorm_eq_ofReal_abs, abs_abs] using hcolumn y
  have hf₁ : MemLp (fun y => |f y|) (ENNReal.ofReal (1 : ℝ)) ν := by
    simpa only [ENNReal.ofReal_one, Real.norm_eq_abs] using
      (memLp_one_iff_integrable.mpr hfi.norm)
  have hLp := integralOperator_memLp μ ν K₁ hK₁ A B hA hB hrow₁ hcolumn₁
    (fun y => |f y|) (by simpa only [Real.norm_eq_abs] using hf.norm) (p := 1) (by norm_num) hf₁
  have hi : Integrable (fun x => ∫ y, K₁ x y * |f y| ∂ν) μ := by
    apply memLp_one_iff_integrable.mp
    simpa only [ENNReal.ofReal_one] using hLp
  have hnorm : Integrable (fun x => |g x| * (∫ y, |K x y| * |f y| ∂ν)) μ := by
    have h := hi.mul_of_top_left hgt.norm
    change Integrable (fun x => (∫ y, K₁ x y * |f y| ∂ν) * ‖g x‖) μ at h
    simpa only [Real.norm_eq_abs, K₁, mul_comm] using h
  have hmeas : AEStronglyMeasurable
      (fun p : α × β => g p.1 * (K p.1 p.2 * f p.2)) (μ.prod ν) :=
    ((hg.comp measurable_fst).mul (hK.mul (hf.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · have hfLp : MemLp f (ENNReal.ofReal (1 : ℝ)) ν := by
      simpa only [ENNReal.ofReal_one] using memLp_one_iff_integrable.mpr hfi
    filter_upwards [integralOperator_integrable_ae μ ν K hK A B hA hB hrow hcolumn
      f hf (p := 1) (by norm_num) hfLp] with x hx
    exact hx.const_mul (g x)
  · have he : (fun x => ∫ y, ‖g x * (K x y * f y)‖ ∂ν) =
        (fun x => |g x| * (∫ y, |K x y| * |f y| ∂ν)) := by
      funext x
      simp only [Real.norm_eq_abs, abs_mul]
      exact integral_const_mul _ _
    rw [he]
    exact hnorm

end RothschildStein.P1
