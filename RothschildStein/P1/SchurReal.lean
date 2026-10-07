-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurPower
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The actual real integral operator obeys Schur's moment
estimate, with the sharp row and column factors. -/
theorem integralOperator_schur_power_bound (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖∫ y, K x y * f y ∂ν‖ₑ ^ p ∂μ) ≤
      A ^ (p - 1) * B * ∫⁻ y, ‖f y‖ₑ ^ p ∂ν := by
  refine le_trans ?_ (kernel_schur_power_bound μ ν (fun x y => ‖K x y‖ₑ)
    hK.enorm A B hrow hcolumn f hf hp)
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ (by linarith)
  simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (fun y => K x y * f y)

/-- Schur's full p-norm bound for every p ≥ 1, including the
correct exponents A^(1-1/p) B^(1/p). -/
theorem integralOperator_schur_eLpNorm'_bound (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm' (fun x => ∫ y, K x y * f y ∂ν) p μ ≤
      A ^ (1 - 1 / p) * B ^ (1 / p) * eLpNorm' f p ν := by
  have hpne : p ≠ 0 := by linarith
  have hpinv : 0 ≤ 1 / p := by positivity
  have h := ENNReal.rpow_le_rpow
    (integralOperator_schur_power_bound μ ν K hK A B hrow hcolumn f hf hp) hpinv
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpinv,
    ENNReal.mul_rpow_of_nonneg _ _ hpinv, ← ENNReal.rpow_mul] at h
  have he : (p - 1) * (1 / p) = 1 - 1 / p := by field_simp [hpne]
  simpa only [he, eLpNorm'_eq_lintegral_enorm] using h

end RothschildStein.P1
