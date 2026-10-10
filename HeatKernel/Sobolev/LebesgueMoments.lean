-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NashMoments
import Mathlib.Tactic

/-! # Real first and second moments of Lebesgue space representatives -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace HeatKernel.Sobolev

/-- The ordinary L¹ norm is the first moment for a nonnegative real function. -/
theorem eLpNorm_one_toReal_eq_integral_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (h₀ : ∀ x, 0 ≤ f x) :
    (eLpNorm f 1 μ).toReal = ∫ x, f x ∂μ := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (h₀ _)]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h₀) hf.aestronglyMeasurable).symm

/-- The same quadratic identity holds for every representative of an L² element. -/
theorem norm_sq_eq_integral_sq_of_ae_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) {f : α → ℝ} (hf : ⇑u =ᵐ[μ] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have hmem : MemLp f 2 μ := (memLp_congr_ae hf).mp (Lp.memLp u)
  rw [Lp.norm_def, eLpNorm_congr_ae hf]
  simpa only [Lp.norm_toLp] using (integral_sq_eq_norm_toLp_sq hmem).symm

end HeatKernel.Sobolev
