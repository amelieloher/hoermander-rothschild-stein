-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- A pointwise limit of finite partial sums is controlled in
L¹ by the sum of the individual L¹ tails (BB p. 320). -/
theorem lintegral_limit_le_tsum_of_partial_sums (μ : Measure X)
    (u : ι → X → ℝ) (hu : ∀ i, AEMeasurable (u i) μ)
    (s : ℕ → Finset ι) (v : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ∑ i ∈ s n, u i x) atTop (𝓝 (v x))) :
    (∫⁻ x, ‖v x‖ₑ ∂μ) ≤ ∑' i, ∫⁻ x, ‖u i x‖ₑ ∂μ := by
  rw [← lintegral_tsum (fun i => (hu i).enorm)]
  apply lintegral_mono_ae
  filter_upwards [hlim] with x hx
  apply le_of_tendsto (continuous_enorm.continuousAt.tendsto.comp hx)
  exact Eventually.of_forall fun n =>
    (enorm_sum_le (s n) (fun i => u i x)).trans (ENNReal.sum_le_tsum (s n))

end RothschildStein.H2
