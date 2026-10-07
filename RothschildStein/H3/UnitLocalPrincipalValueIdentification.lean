-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UnitLocalKernelIdentification
public import RothschildStein.H3.LocalizedPrincipalValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The localized H2 principal value equals the full principal value minus
the finite annular tail on unit-supported sources in its Holder domain. -/
theorem localKernelData_unit_source_principalValue (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (k u : ControlCarrier N → ℝ)
    (H : let _localMetric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (hk : TypeZero G ν k) (hu : ContDiff ℝ 1 (fun y : Fin N → ℝ => u y))
    (hs : HasCompactSupport u) (hsu : ∀ y, 1 ≤ ν y → u y = 0)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hf : let _localMetric := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) u)
    {x : ControlCarrier N} (hx : ν x < 1) :
    let _localMetric := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (truncatedKernel G ν k) H
    Q.principalValue u x = H1.principalValueConvolution G ν k u x -
      G2.groupConvolution G u (typeZeroUnitTail ν k) x := by
  let _localMetric := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (truncatedKernel G ν k) H
  dsimp only
  have hxU : x ∈ ball (0 : ControlCarrier N) 2 := by
    change ν (G.mul (G.inv 0) x) < 2
    rw [G2.inv_zero, G2.zero_mul]
    linarith
  have hl := (local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym A S
    (truncatedKernel G ν k) H hδ hδ1 hf).1 x hxU
  have hr := unit_source_radial_truncation_limit G ν h1 hsym hk hu hs hsu hx
  have hr' : Tendsto (fun ε : ℝ => H2.truncatedIntegral volume
      (ball (0 : ControlCarrier N) 2) dist Q.cutoffKernel ε u x) (𝓝[>] 0)
      (𝓝 (H1.principalValueConvolution G ν k u x -
        G2.groupConvolution G u (typeZeroUnitTail ν k) x)) := by
    apply hr.congr'
    exact Eventually.of_forall fun ε =>
      (localKernelData_unit_source_truncation G ν h1 hsym A S k u H hsu hx ε).symm
  exact tendsto_nhds_unique hl hr'

end RothschildStein.H3
