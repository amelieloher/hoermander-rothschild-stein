-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UnitPrincipalValueFirstSeminorm
public import RothschildStein.H3.CompactSourceControlHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The unit-ball estimate for compact C1 sources requires no Holder-domain premise. -/
theorem compactUnitPrincipalValue_eLpNorm_bound_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (k : ControlCarrier N → ℝ)
    (H : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (Ht : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k y x))
    (hk : TypeZero G ν k) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun y : Fin N → ℝ => u y))
    (hs : HasCompactSupport u) (hsu : ∀ y, 1 ≤ ν y → u y = 0) :
    let _metric := gaugeMetric G ν h1 hsym
    let _Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (truncatedKernel G ν k) H
    eLpNorm (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
        (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤
      (ENNReal.ofReal ((kernelDerivativeBound ν k 1) * normalizedLocalLpConstant G ν h1 hsym A S hA hS p) +
        ENNReal.ofReal (kernelDerivativeBound ν k 1) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) *
          eLpNorm u (ENNReal.ofReal p) volume := by
  let _metric := gaugeMetric G ν h1 hsym
  have hf := compact_source_boundedHolder_control_ball G ν h1 hsym 2 u hu hs
    (δ := (1 / 2 : ℝ≥0)) (by norm_num)
  exact unitPrincipalValue_firstSeminorm_eLpNorm_bound_of_truncatedKernelFacts G ν h1 hsym A S hA hS
    k H Ht hk hp u hu hs hsu (δ := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num) hf

end RothschildStein.H3
