-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.PrincipalValueCutoffSupport
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The pointwise local principal value depends only on the input on its ball. -/
theorem LocalKernelData.principalValue_congr (Q : LocalKernelData D d) {f g : X → ℝ}
    (he : EqOn f g (ball Q.z Q.R)) {x : X} (hx : x ∈ ball Q.z Q.R) :
    Q.principalValue f x = Q.principalValue g x := by
  unfold LocalKernelData.principalValue pvFormula regularizedIntegral
  rw [he hx]
  congr 1
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro y hy
  dsimp only
  rw [he hy]
end RothschildStein.H2
