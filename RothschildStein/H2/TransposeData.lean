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

/-- The original and transposed Data D use the same centre, radii and
symmetric truncation distance, and exchanged cutoffs. The two splittings
need only have transposed sums (BB Remark 7.22, pp. 311–312). -/
structure TransposeData (Q : LocalKernelData D d) where
  data : LocalKernelData D d
  centre : data.z = Q.z
  radius : data.R = Q.R
  supportRadius : data.R' = Q.R'
  outerCutoff : data.a = Q.b
  innerCutoff : data.b = Q.a
  transpose : ∀ x ∈ ball Q.z (2 * Q.R), ∀ y ∈ ball Q.z (2 * Q.R),
    data.sumKernel x y = Q.sumKernel y x

/-- Exchanging cutoffs makes the localized kernel the exact transpose,
including outside the patch; no identity between individual pieces is needed. -/
theorem TransposeData.cutoffKernel_eq {Q : LocalKernelData D d} (P : TransposeData Q)
    (x y : X) : P.data.cutoffKernel x y = Q.cutoffKernel y x := by
  unfold LocalKernelData.cutoffKernel localizedKernel
  rw [P.centre, P.radius, P.outerCutoff, P.innerCutoff]
  by_cases hx : x ∈ ball Q.z Q.R <;> by_cases hy : y ∈ ball Q.z Q.R
  · simp only [hx, hy, and_self, ite_true]
    rw [P.transpose x (ball_subset_ball (by linarith [Q.radius_pos]) hx)
      y (ball_subset_ball (by linarith [Q.radius_pos]) hy)]
    ring
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

end RothschildStein.H2
