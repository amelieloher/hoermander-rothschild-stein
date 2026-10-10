-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanOscillation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Nonnegative pair-integral bounds for oscillation from the mean. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel

/-- Pointwise Jensen in nonnegative-integral form. -/
theorem ofReal_abs_sub_average_rpow_le_pair_integral {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ) (c : ℝ)
    (hpair : Integrable (fun y => |c - f y| ^ p) μ) :
    ENNReal.ofReal (|c - ⨍ y, f y ∂μ| ^ p) ≤
      (μ univ)⁻¹ * ∫⁻ y, ENNReal.ofReal (|c - f y| ^ p) ∂μ := by
  have hh := ENNReal.ofReal_le_ofReal
    (abs_sub_average_rpow_le_average_abs_sub_rpow hp hf c hpair)
  rw [ofReal_average hpair (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _),
    ENNReal.div_eq_inv_mul] at hh
  exact hh

/-- The integral of mean oscillation is bounded by the normalized point-pair integral.
No integrability assumption on the outer integral is required. -/
theorem lintegral_abs_sub_average_rpow_le_pairwise {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ)
    (hpairs : ∀ x, Integrable (fun y => |f x - f y| ^ p) μ) :
    (∫⁻ x, ENNReal.ofReal (|f x - ⨍ y, f y ∂μ| ^ p) ∂μ) ≤
      (μ univ)⁻¹ * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|f x - f y| ^ p) ∂μ ∂μ := by
  calc
    (∫⁻ x, ENNReal.ofReal (|f x - ⨍ y, f y ∂μ| ^ p) ∂μ) ≤
        ∫⁻ x, (μ univ)⁻¹ * (∫⁻ y, ENNReal.ofReal (|f x - f y| ^ p) ∂μ) ∂μ :=
      lintegral_mono fun x => ofReal_abs_sub_average_rpow_le_pair_integral hp hf (f x) (hpairs x)
    _ = _ := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
      (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)))

end HeatKernel
