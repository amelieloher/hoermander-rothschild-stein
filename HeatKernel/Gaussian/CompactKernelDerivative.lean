-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CompactParameterBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-! # Spatial differentiation of compact-data kernel integrals

Jointly continuous Fréchet derivatives have the same compact domination as
time derivatives. This also applies to derivative-valued kernels.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology
namespace HeatKernel.Gaussian

/-- Continuous vector-valued functions may multiply compact integrable scalar data. -/
theorem integrable_smul_continuous_of_support_subset_compact {Z E : Type*}
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Z) {f : Z → ℝ} {k : Z → E} (hf : Integrable f μ) (hk : Continuous k)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    Integrable (fun z ↦ f z • k z) μ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hk.continuousOn
  apply (hf.norm.const_mul (max B 0)).mono' (hf.aestronglyMeasurable.smul hk.aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  by_cases hz : z ∈ K
  · calc
      ‖f z • k z‖ = ‖f z‖ * ‖k z‖ := norm_smul _ _
      _ ≤ ‖f z‖ * max B 0 := mul_le_mul_of_nonneg_left ((hB z hz).trans (le_max_left _ _)) (norm_nonneg _)
      _ = max B 0 * ‖f z‖ := mul_comm _ _
  · have hz0 : f z = 0 := by
      by_contra hn
      exact hz (hsupp hn)
    simp [hz0]

/-- Joint continuity of a kernel and its Fréchet derivative justifies spatial
differentiation under the integral against compact integrable scalar data. -/
theorem hasFDerivAt_kernel_integral_of_compact_data {H Z E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) {x₀ : H} (hx₀ : x₀ ∈ U)
    (k : H × Z → E) (k' : H × Z → H →L[ℝ] E)
    (hk : ContinuousOn k (U ×ˢ univ)) (hk' : ContinuousOn k' (U ×ˢ univ))
    (hderiv : ∀ x ∈ U, ∀ z, HasFDerivAt (fun y ↦ k (y, z)) (k' (x, z)) x) :
    Integrable (fun z ↦ f z • k' (x₀, z)) μ ∧
      HasFDerivAt (fun x ↦ ∫ z, f z • k (x, z) ∂μ) (∫ z, f z • k' (x₀, z) ∂μ) x₀ := by
  have hc : ∀ x ∈ U, Continuous (fun z ↦ k (x, z)) := fun x hx ↦
    hk.comp_continuous (continuous_const.prodMk continuous_id) (fun z ↦ ⟨hx, mem_univ z⟩)
  have hc' : Continuous (fun z ↦ k' (x₀, z)) :=
    hk'.comp_continuous (continuous_const.prodMk continuous_id) (fun z ↦ ⟨hx₀, mem_univ z⟩)
  obtain ⟨ε, B, hε, _hB, hsub, hbound⟩ := exists_local_uniform_bound_on_compact hU hx₀ hK hk'
  refine ⟨integrable_smul_continuous_of_support_subset_compact μ hf hc' hK hsupp, ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ hε)
  · filter_upwards [hU.mem_nhds hx₀] with x hx
    exact hf.aestronglyMeasurable.smul (hc x hx).aestronglyMeasurable
  · exact integrable_smul_continuous_of_support_subset_compact μ hf (hc x₀ hx₀) hK hsupp
  · exact hf.aestronglyMeasurable.smul hc'.aestronglyMeasurable
  · apply Eventually.of_forall
    intro z x hx
    by_cases hz : z ∈ K
    · calc
        ‖f z • k' (x, z)‖ = ‖f z‖ * ‖k' (x, z)‖ := norm_smul _ _
        _ ≤ ‖f z‖ * B := mul_le_mul_of_nonneg_left (hbound x hx z hz) (norm_nonneg _)
        _ = B * ‖f z‖ := mul_comm _ _
    · have hz0 : f z = 0 := by
        by_contra hn
        exact hz (hsupp hn)
      simp [hz0]
  · exact hf.norm.const_mul B
  · exact Eventually.of_forall (fun z x hx ↦ (hderiv x (hsub hx) z).const_smul (f z))

end HeatKernel.Gaussian
