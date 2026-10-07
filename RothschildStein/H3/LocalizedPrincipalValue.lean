-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalKernelSetting
public import RothschildStein.H2.SingularHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- The scaled truncated-kernel bounds yield a pointwise principal value
at every point of U and the Holder estimate for every exponent in (0,1). -/
theorem local_principalValue_holder_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    {f : ControlCarrier N → ℝ}
    (hf : letI := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) f) :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
    (∀ x ∈ ball (0 : ControlCarrier N) 2,
      Tendsto (fun ε : ℝ => H2.truncatedIntegral volume (ball 0 2) dist Q.cutoffKernel ε f x)
        (𝓝[>] 0) (𝓝 (Q.principalValue f x))) ∧
      H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Q.principalValue f) ≤
        ENNReal.ofReal (Q.operatorHolderConstant δ) *
          H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f := by
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
  constructor
  · intro x hx
    exact Q.principalValue_limit hδ hf hx
  · exact Q.principalValue_holder_bound hδ hδ1 hδ1 hδ1 hf

end RothschildStein.H3
