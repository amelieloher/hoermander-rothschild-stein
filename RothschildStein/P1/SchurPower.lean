-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedHolder
public import RothschildStein.P1.SchurMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- The weighted row inequality in p-th-power form, including
zero row mass. This is the exact pointwise step of the Schur proof. -/
theorem weightedKernel_power_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : α → ℝ≥0∞) (hK : AEMeasurable K μ)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y, K y * ‖f y‖ₑ ∂μ) ^ p ≤
      (∫⁻ y, K y * ‖f y‖ₑ ^ p ∂μ) * (∫⁻ y, K y ∂μ) ^ (p - 1) := by
  have hp0 : 0 ≤ p := by linarith
  have hpne : p ≠ 0 := by linarith
  have h := ENNReal.rpow_le_rpow (weightedKernel_holder_bound μ K hK f hf hp) hp0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  have hfirst : 1 / p * p = 1 := by field_simp [hpne]
  have hsecond : (1 - 1 / p) * p = p - 1 := by field_simp [hpne]
  simpa only [hfirst, hsecond, ENNReal.rpow_one] using h

/-- Schur's moment bound with the sharp powers A^(p-1) B.
It applies for every real p ≥ 1 and uses only row and column bounds;
the kernel and constants are fixed independently of the input. -/
theorem kernel_schur_power_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞)
    (hrow : ∀ x, (∫⁻ y, K x y ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, K x y ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) ^ p ∂μ) ≤
      A ^ (p - 1) * B * ∫⁻ y, ‖f y‖ₑ ^ p ∂ν := by
  have hm : Measurable (fun y => ‖f y‖ₑ ^ p) := hf.enorm.pow_const p
  calc
    _ ≤ ∫⁻ x, A ^ (p - 1) * (∫⁻ y, K x y * ‖f y‖ₑ ^ p ∂ν) ∂μ := by
      apply lintegral_mono
      intro x
      have h := weightedKernel_power_bound ν (K x) hK.of_uncurry_left.aemeasurable
        f hf.aestronglyMeasurable hp
      exact h.trans (by
        rw [mul_comm]
        exact mul_le_mul_left (ENNReal.rpow_le_rpow (hrow x) (by linarith)) _)
    _ ≤ A ^ (p - 1) * (B * ∫⁻ y, ‖f y‖ₑ ^ p ∂ν) := by
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul_right (kernel_column_lintegral_bound μ ν K hK B hcolumn _ hm) _
    _ = _ := by rw [mul_assoc]

end RothschildStein.P1
