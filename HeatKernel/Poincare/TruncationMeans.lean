-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.SymmetricTruncation
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- Symmetric truncation preserves almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_symmetric_truncation
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f : A → ℝ}
    (hf : AEStronglyMeasurable f μ) (M : ℝ) :
    AEStronglyMeasurable (fun x => max (-M) (min (f x) M)) μ := by
  have hc : Continuous (fun t : ℝ => max (-M) (min t M)) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact hc.comp_aestronglyMeasurable hf

/-- Means of symmetric truncations of an integrable function converge to its mean,
using only L¹ integrability of the untruncated function. -/
theorem tendsto_average_symmetric_truncation
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f : A → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ⨍ x, max (-(n : ℝ)) (min (f x) n) ∂μ)
      atTop (𝓝 (⨍ x, f x ∂μ)) := by
  have hI := tendsto_integral_of_dominated_convergence (fun x => |f x|)
    (fun n => aestronglyMeasurable_symmetric_truncation hf.aestronglyMeasurable n) hf.abs
    (fun n => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using
        abs_symmetric_truncation_le_abs (Nat.cast_nonneg n) (f x))
    (Eventually.of_forall fun x => tendsto_symmetric_truncation (f x))
  simpa only [average_eq, smul_eq_mul] using
    (tendsto_const_nhds (x := (μ.real univ)⁻¹)).mul hI

end HeatKernel
