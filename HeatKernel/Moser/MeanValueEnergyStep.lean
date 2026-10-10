-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSobolevMoments
import Mathlib.Tactic

/-! # One parabolic higher-moment step from explicit energy bounds -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Spatial Sobolev and separate slice and integrated-energy estimates produce one
higher-moment step. The two energy estimates are explicit hypotheses. -/
theorem lintegral_parabolic_enorm_le_of_energy_bounds
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    (τ : Measure T) (μ : Measure α) {w : T → α → ℝ}
    {E : T → ℝ≥0∞} {A D M : ℝ≥0∞} {ν : ℝ} (hν : 2 < ν)
    (hw : ∀ᵐ t ∂τ, AEStronglyMeasurable (w t) μ) (hE : AEMeasurable E τ)
    (hSob : ∀ᵐ t ∂τ,
      eLpNorm (w t) (ENNReal.ofReal (2 * ν / (ν - 2))) μ ^ 2 ≤ A * E t)
    (hSlice : ∀ᵐ t ∂τ, (∫⁻ x, ‖w t x‖ₑ ^ (2 : ℝ) ∂μ) ≤ D * M)
    (hEnergy : (∫⁻ t, E t ∂τ) ≤ D * M) :
    (∫⁻ t, ∫⁻ x, ‖w t x‖ₑ ^ (2 + 4 / ν) ∂μ ∂τ) ≤
      A * (D * M) ^ (1 + 2 / ν) := by
  calc
    _ ≤ A * (D * M) ^ (2 / ν) * (∫⁻ t, E t ∂τ) :=
      lintegral_parabolic_enorm_le_of_eLpNorm_sq τ μ hν hw hE hSob hSlice
    _ ≤ A * (D * M) ^ (2 / ν) * (D * M) := mul_le_mul' le_rfl hEnergy
    _ = _ := by
      rw [show 1 + 2 / ν = 2 / ν + 1 by ring,
        ENNReal.rpow_add_of_nonneg (2 / ν) 1 (by positivity) (by norm_num), ENNReal.rpow_one]
      ac_rfl

end HeatKernel
