-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedPrincipalValue
public import RothschildStein.H3.KernelNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter Metric
open scoped Topology
variable {X : Type*} [MeasurableSpace X]

/-- Every real truncation commutes with scalar multiplication of
the kernel, including the integral convention at exceptional inputs. -/
theorem truncatedIntegral_scale (μ : Measure X) (U : Set X) (d K : X → X → ℝ)
    (c ε : ℝ) (f : X → ℝ) (x : X) :
    H2.truncatedIntegral μ U d (fun x y => c * K x y) ε f x =
      c * H2.truncatedIntegral μ U d K ε f x := by
  simp only [H2.truncatedIntegral, mul_assoc, integral_const_mul]

/-- Uniqueness of actual principal-value limits transfers kernel
scaling to the pointwise operator. Both limits are independently certified. -/
theorem principalValue_scale_of_limits (μ : Measure X) (U : Set X)
    (d K L : X → X → ℝ) (c : ℝ) (hK : K = fun x y => c * L x y)
    (f : X → ℝ) (x : X) {v w : ℝ}
    (hv : Tendsto (fun ε : ℝ => H2.truncatedIntegral μ U d K ε f x)
      (𝓝[>] 0) (𝓝 v))
    (hw : Tendsto (fun ε : ℝ => H2.truncatedIntegral μ U d L ε f x)
      (𝓝[>] 0) (𝓝 w)) : v = c * w := by
  apply tendsto_nhds_unique hv
  simpa only [hK, truncatedIntegral_scale] using tendsto_const_nhds.mul hw

end RothschildStein.H3
