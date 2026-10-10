-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.QuadraticRemainder

/-! # Integrated quadratic errors on square integrable spaces

A pointwise quadratic error controlled by a square integrable increment has its integral
bounded by the squared Hilbert norm. Measurability suffices for its integrability.
-/

@[expose] public section

open MeasureTheory Filter

namespace HeatKernel

/-- A measurable scalar error bounded by a square integrable increment squared is integrable,
and its integral has a quadratic norm bound. -/
theorem integrable_and_norm_integral_le_of_quadratic_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (k : Lp ℝ 2 μ) {r : α → ℝ} {C : ℝ}
    (hr : AEStronglyMeasurable r μ) (hb : ∀ᵐ x ∂μ, ‖r x‖ ≤ C * (k x) ^ 2) :
    Integrable r μ ∧ ‖∫ x, r x ∂μ‖ ≤ C * ‖k‖ ^ 2 := by
  have hk : Integrable (fun x => C * (k x) ^ 2) μ := (Lp.memLp k).integrable_sq.const_mul C
  have hi : Integrable r μ := hk.mono' hr hb
  refine ⟨hi, ?_⟩
  calc
    ‖∫ x, r x ∂μ‖ ≤ ∫ x, ‖r x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * (k x) ^ 2 ∂μ := integral_mono_ae hi.norm hk hb
    _ = C * ‖k‖ ^ 2 := by
      rw [integral_const_mul]
      congr 1
      rw [← real_inner_self_eq_norm_sq k, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end HeatKernel
