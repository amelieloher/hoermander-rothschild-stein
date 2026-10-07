-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurBilinearIntegrability

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- Fubini passes from a measurable Schur representative to the
actual kernel using equality almost everywhere on every row and column.
Arbitrary diagonal values require no joint measurability premise. -/
theorem schur_bilinearTranspose_of_representative {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K r : α → β → ℝ) (hr : Measurable (Function.uncurry r))
    (heRow : ∀ x, r x =ᶠ[ae ν] K x)
    (heCol : ∀ y, (fun x => r x y) =ᶠ[ae μ] fun x => K x y)
    (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖r x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖r x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) (hfi : Integrable f ν)
    (g : α → ℝ) (hg : Measurable g) (hgt : MemLp g ⊤ μ) :
    (∫ x, g x * (∫ y, K x y * f y ∂ν) ∂μ) =
      ∫ y, f y * (∫ x, K x y * g x ∂μ) ∂ν := by
  have hpair := integral_kernel_bilinearTranspose μ ν r f g
    (schur_bilinear_integrable μ ν r hr A B hA hB hrow hcolumn f hf hfi g hg hgt)
  calc
    _ = ∫ x, g x * (∫ y, r x y * f y ∂ν) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change g x * (∫ y, K x y * f y ∂ν) = g x * (∫ y, r x y * f y ∂ν)
      congr 1
      apply integral_congr_ae
      filter_upwards [heRow x] with y hy
      rw [hy]
    _ = ∫ y, f y * (∫ x, r x y * g x ∂μ) ∂ν := hpair
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change f y * (∫ x, r x y * g x ∂μ) = f y * (∫ x, K x y * g x ∂μ)
      congr 1
      apply integral_congr_ae
      filter_upwards [heCol y] with x hx
      rw [hx]

end RothschildStein.P1
