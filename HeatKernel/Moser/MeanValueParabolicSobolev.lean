-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueInterpolation

/-! # Time integration of spatial Sobolev interpolation -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Spatial Sobolev bounds and a uniform quadratic moment give the parabolic
higher moment. The spatial energy and its Sobolev constant are explicit inputs. -/
theorem lintegral_parabolic_power_le_of_spatial_sobolev
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    (τ : Measure T) (μ : Measure α) {f : T → α → ℝ≥0∞}
    {E : T → ℝ≥0∞} {A S : ℝ≥0∞} {ν : ℝ} (hν : 2 < ν)
    (hf : ∀ᵐ t ∂τ, AEMeasurable (f t) μ) (hE : AEMeasurable E τ)
    (hSob : ∀ᵐ t ∂τ,
      (∫⁻ x, f t x ^ (2 * ν / (ν - 2)) ∂μ) ^ ((ν - 2) / ν) ≤ A * E t)
    (hS : ∀ᵐ t ∂τ, (∫⁻ x, f t x ^ (2 : ℝ) ∂μ) ≤ S) :
    (∫⁻ t, ∫⁻ x, f t x ^ (2 + 4 / ν) ∂μ ∂τ) ≤
      A * S ^ (2 / ν) * (∫⁻ t, E t ∂τ) := by
  have hn : 0 ≤ 2 / ν := by positivity
  calc
    _ ≤ ∫⁻ t, (A * S ^ (2 / ν)) * E t ∂τ := by
      apply lintegral_mono_ae
      filter_upwards [hf, hSob, hS] with t ht hst hmt
      calc
        _ ≤ _ := lintegral_parabolic_power_le μ ht hν
        _ ≤ (A * E t) * S ^ (2 / ν) :=
          mul_le_mul' hst (ENNReal.rpow_le_rpow hmt hn)
        _ = _ := by ac_rfl
    _ = _ := lintegral_const_mul'' _ hE

end HeatKernel
