-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CompactKernelDerivative
import Mathlib.Tactic

/-! # Continuity of compact-data kernel integrals

Joint continuity of a kernel gives joint continuity of its evolution of compact
integrable data. Local compact bounds supply domination in the parameter.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology
namespace HeatKernel.Gaussian

/-- A jointly continuous kernel integrated against compact integrable scalar
data is continuous on its open parameter region. -/
theorem continuousOn_kernel_integral_of_compact_data {H Z E : Type*}
    [PseudoMetricSpace H] [ProperSpace H]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) (k : H × Z → E)
    (hk : ContinuousOn k (U ×ˢ univ)) :
    ContinuousOn (fun x ↦ ∫ z, f z • k (x, z) ∂μ) U := by
  intro x₀ hx₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨ε, B, hε, _hB, _hsub, hbound⟩ := exists_local_uniform_bound_on_compact hU hx₀ hK hk
  apply continuousAt_of_dominated (bound := fun z ↦ B * ‖f z‖)
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    have hc : Continuous (fun z ↦ k (x, z)) := hk.comp_continuous
      (continuous_const.prodMk continuous_id) (fun z ↦ ⟨hx, mem_univ z⟩)
    exact hf.aestronglyMeasurable.smul hc.aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x₀ hε] with x hx
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · calc
        ‖f z • k (x, z)‖ = ‖f z‖ * ‖k (x, z)‖ := norm_smul _ _
        _ ≤ ‖f z‖ * B := mul_le_mul_of_nonneg_left (hbound x hx z hz) (norm_nonneg _)
        _ = B * ‖f z‖ := mul_comm _ _
    · have hz0 : f z = 0 := by
        by_contra hn
        exact hz (hsupp hn)
      simp [hz0]
  · exact hf.norm.const_mul B
  · apply Eventually.of_forall
    intro z
    have hc : ContinuousOn (fun x ↦ k (x, z)) U := hk.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun x hx ↦ ⟨hx, mem_univ z⟩)
    exact (hc.continuousAt (hU.mem_nhds hx₀)).const_smul (f z)

end HeatKernel.Gaussian
