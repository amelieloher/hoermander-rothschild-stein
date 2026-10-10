-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanShift

/-! Mean-shift bounds without prior power integrability. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel

/-- An integrable function satisfies the mean-shift power bound even when its
oscillation power is not known integrable. -/
theorem lintegral_abs_sub_average_rpow_le_const_of_integrable {E : Type*}
    [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ]
    {f : E → ℝ} {p : ℝ} (hp : 1 ≤ p) (hf : Integrable f μ) (c : ℝ) :
    (∫⁻ x, ENNReal.ofReal (|f x - ⨍ y, f y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p) * ∫⁻ x, ENNReal.ofReal (|f x - c| ^ p) ∂μ := by
  by_cases hI : (∫⁻ x, ENNReal.ofReal (|f x - c| ^ p) ∂μ) = ⊤
  · rw [hI, ENNReal.mul_top (by positivity)]
    exact le_top
  have hpow : AEStronglyMeasurable (fun x => |f x - c| ^ p) μ :=
    (Real.continuous_rpow_const (le_trans zero_le_one hp)).comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable
        (hf.aestronglyMeasurable.sub (aestronglyMeasurable_const (b := c))))
  have hi : Integrable (fun x => |f x - c| ^ p) μ := ⟨hpow,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)).mpr (lt_top_iff_ne_top.mpr hI)⟩
  exact lintegral_abs_sub_average_rpow_le_const hp hf c hi

end HeatKernel
