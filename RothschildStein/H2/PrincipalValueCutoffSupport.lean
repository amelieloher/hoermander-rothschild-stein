-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.SingularHolder
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Every principal value carries its output cutoff pointwise,
including points outside its input ball. -/
theorem LocalKernelData.principalValue_zero_of_cutoff (Q : LocalKernelData D d)
    (f : X → ℝ) {x : X} (hx : Q.a x = 0) : Q.principalValue f x = 0 := by
  classical
  simp [LocalKernelData.principalValue, pvFormula, regularizedIntegral,
    LocalKernelData.cutoffKernel, localizedKernel, LocalKernelData.oneLimit, hx]

/-- Every truncated integral also carries its output cutoff. -/
theorem LocalKernelData.truncated_zero_of_cutoff (Q : LocalKernelData D d)
    (f : X → ℝ) (ε : ℝ) {x : X} (hx : Q.a x = 0) :
    truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x = 0 := by
  classical
  simp [truncatedIntegral, LocalKernelData.cutoffKernel, localizedKernel, hx]
end RothschildStein.H2
