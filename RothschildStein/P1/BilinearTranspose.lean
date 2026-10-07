-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.P1
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Exchanging the two variables gives the bilinear transpose
pairing whenever the tested kernel is integrable (BB Proposition 11.14,
pp. 545–546). This applies to every integrable positive-type kernel
and separately to every symmetric truncation. -/
theorem integral_kernel_bilinearTranspose (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ) (f : β → ℝ) (g : α → ℝ)
    (hi : Integrable (fun p : α × β => g p.1 * (K p.1 p.2 * f p.2)) (μ.prod ν)) :
    (∫ x, g x * (∫ y, K x y * f y ∂ν) ∂μ) =
      ∫ y, f y * (∫ x, K x y * g x ∂μ) ∂ν := by
  calc
    _ = ∫ x, ∫ y, g x * (K x y * f y) ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (integral_const_mul (g x) _).symm)
    _ = ∫ y, ∫ x, g x * (K x y * f y) ∂μ ∂ν := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ x, g x * (K x y * f y) ∂μ) = f y * (∫ x, K x y * g x ∂μ)
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)

end RothschildStein.P1
