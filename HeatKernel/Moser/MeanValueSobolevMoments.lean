-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicSobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Tactic

/-! # Parabolic interpolation from squared spatial Sobolev norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The spatial Sobolev moment to its quadratic power is the squared extended norm. -/
theorem lintegral_sobolev_moment_eq_eLpNorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {w : α → ℝ}
    (hw : AEStronglyMeasurable w μ) {ν : ℝ} (hν : 2 < ν) :
    (∫⁻ x, ‖w x‖ₑ ^ (2 * ν / (ν - 2)) ∂μ) ^ ((ν - 2) / ν) =
      eLpNorm w (ENNReal.ofReal (2 * ν / (ν - 2))) μ ^ 2 := by
  have hq : 0 < 2 * ν / (ν - 2) := by positivity
  have hn : ν ≠ 0 := by linarith
  have hd : ν - 2 ≠ 0 := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top hw, ENNReal.toReal_ofReal hq.le,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Squared spatial Sobolev norms give the parabolic higher moment with an
explicit almost everywhere bound on the quadratic spatial moment. -/
theorem lintegral_parabolic_enorm_le_of_eLpNorm_sq
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    (τ : Measure T) (μ : Measure α) {w : T → α → ℝ}
    {E : T → ℝ≥0∞} {A S : ℝ≥0∞} {ν : ℝ} (hν : 2 < ν)
    (hw : ∀ᵐ t ∂τ, AEStronglyMeasurable (w t) μ) (hE : AEMeasurable E τ)
    (hSob : ∀ᵐ t ∂τ,
      eLpNorm (w t) (ENNReal.ofReal (2 * ν / (ν - 2))) μ ^ 2 ≤ A * E t)
    (hS : ∀ᵐ t ∂τ, (∫⁻ x, ‖w t x‖ₑ ^ (2 : ℝ) ∂μ) ≤ S) :
    (∫⁻ t, ∫⁻ x, ‖w t x‖ₑ ^ (2 + 4 / ν) ∂μ ∂τ) ≤
      A * S ^ (2 / ν) * (∫⁻ t, E t ∂τ) := by
  apply lintegral_parabolic_power_le_of_spatial_sobolev τ μ hν
    (hw.mono fun _ ht => ht.enorm) hE _ hS
  filter_upwards [hw, hSob] with t ht hst
  rwa [lintegral_sobolev_moment_eq_eLpNorm_sq μ ht hν]

end HeatKernel
