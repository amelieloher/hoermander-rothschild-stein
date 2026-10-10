-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.TruncationMeans
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- Uniform bounds on the centered seminorms of symmetric truncations pass to an
L¹ function by convergence of the means and Fatou, without assuming it belongs to Lp. -/
theorem eLpNorm_mean_oscillation_le_of_symmetric_truncations
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f : A → ℝ} (hf : Integrable f μ)
    {p C : ℝ≥0∞}
    (hbound : ∀ n : ℕ, eLpNorm (fun x => max (-(n : ℝ)) (min (f x) n) -
      ⨍ y, max (-(n : ℝ)) (min (f y) n) ∂μ) p μ ≤ C) :
    eLpNorm (fun x => f x - ⨍ y, f y ∂μ) p μ ≤ C := by
  have hm := tendsto_average_symmetric_truncation hf
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (f := fun n x => max (-(n : ℝ)) (min (f x) n) -
      ⨍ y, max (-(n : ℝ)) (min (f y) n) ∂μ)
    (Eventually.of_forall hbound)
    (fun n => (aestronglyMeasurable_symmetric_truncation hf.aestronglyMeasurable n).sub
      aestronglyMeasurable_const)
    (hf.aestronglyMeasurable.sub aestronglyMeasurable_const)
  exact Eventually.of_forall fun x => (tendsto_symmetric_truncation (f x)).sub hm

end HeatKernel
