-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.LocalKernelData
public import RothschildStein.H2.KernelRestriction
public import Mathlib.Topology.MetricSpace.Thickening
public import RothschildStein.H2.Cutoffs
public import Mathlib.Algebra.BigOperators.Field
public import RothschildStein.H2.TransposeData
public import RothschildStein.H2.PrincipalValueCutoffSupport
public import RothschildStein.H2.HolderBallExtension
public import RothschildStein.H2.HolderFiniteSum
public import RothschildStein.H2.IntegralEnlargement
public import RothschildStein.H2.LocalizedKernelMeasurable
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal BigOperators
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Supported cutoff kernels equal their cutoff product everywhere. -/
theorem LocalKernelData.cutoffKernel_eq_product (Q : LocalKernelData D d) (x y : X) :
    Q.cutoffKernel x y = Q.a x * Q.sumKernel x y * Q.b y := by
  classical
  unfold LocalKernelData.cutoffKernel localizedKernel
  by_cases hx : x ∈ ball Q.z Q.R <;> by_cases hy : y ∈ ball Q.z Q.R
  · simp [hx, hy]
  · simp [hx, hy, Q.cutoff_b.outside y hy]
  · simp [hx, hy, Q.cutoff_a.outside x hx]
  · simp [hx, hy, Q.cutoff_a.outside x hx]

end RothschildStein.H2
