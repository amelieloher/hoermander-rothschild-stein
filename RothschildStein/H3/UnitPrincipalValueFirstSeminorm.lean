-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UnitPrincipalValueNormalizedEstimate
public import RothschildStein.H3.KernelDerivativeProperties

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The unit-ball estimate uses exactly the actual first kernel seminorm. -/
theorem unitPrincipalValue_firstSeminorm_eLpNorm_bound_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (k : ControlCarrier N → ℝ)
    (H : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (Ht : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k y x))
    (hk : TypeZero G ν k) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun y : Fin N → ℝ => u y))
    (hs : HasCompactSupport u) (hsu : ∀ y, 1 ≤ ν y → u y = 0)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hf : let _metric := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) u) :
    let _metric := gaugeMetric G ν h1 hsym
    let _Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (truncatedKernel G ν k) H
    eLpNorm (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
        (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤
      (ENNReal.ofReal ((kernelDerivativeBound ν k 1) * normalizedLocalLpConstant G ν h1 hsym A S hA hS p) +
        ENNReal.ofReal (kernelDerivativeBound ν k 1) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) *
          eLpNorm u (ENNReal.ofReal p) volume := by
  have hΛ := (kernelDerivativeBound_properties ν.gauge hk.smooth 1).1
  have hSphere : kernelSphereBound ν k ≤ kernelDerivativeBound ν k 1 := by
    rw [← kernelDerivativeBound_zero ν k]
    exact kernelDerivativeBound_mono ν k (by omega)
  exact unitPrincipalValue_normalized_eLpNorm_bound_of_truncatedKernelFacts G ν h1 hsym A S hA hS
    (kernelDerivativeBound ν k 1) hΛ k H Ht hk hSphere hp u hu hs hsu hδ hδ1 hf

end RothschildStein.H3
