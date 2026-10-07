-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactUniformConvolutionLimit
public import RothschildStein.G2.MollifierUniform
public import RothschildStein.G2.MollifierSmooth
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Mollified compact continuous sources converge pointwise after
convolution with a locally integrable group kernel. A common compact
support is used (BB Proposition 8.49, p. 379). -/
theorem tendsto_groupConvolution_groupRegularize {N : ℕ} (G : HomogeneousGroup N)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    {f K : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hK : LocallyIntegrable K volume) (x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => G2.groupConvolution G (G2.groupRegularize G φ f ε) K x)
      (𝓝[>] 0) (𝓝 (G2.groupConvolution G f K x)) := by
  obtain ⟨S, hS, hsf, hreg⟩ := G2.exists_common_compact_support_groupRegularize G φ hc
  apply tendsto_groupConvolution_of_uniform_compact_support G (𝓝[>] 0)
    (fun ε => G2.groupRegularize G φ f ε) f K hK hf S hS
    ((subset_closure : Function.support f ⊆ tsupport f).trans hsf) ?_
    (G2.tendstoUniformly_groupRegularize G φ hf hc) x
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε he
  refine ⟨(G2.contDiff_groupRegularize G φ he.1 (p := (1 : ℝ≥0∞)) le_rfl
    (hf.memLp_of_hasCompactSupport hc)).continuous, hreg ε he.1 he.2.le⟩

end RothschildStein.H3
