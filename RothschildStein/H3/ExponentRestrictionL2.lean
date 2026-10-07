-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderExponentL2
public import RothschildStein.H3.HolderRestrictionChoice
public import RothschildStein.H2.SingularL2Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Restriction of the Holder exponent preserves the L2 element. -/
theorem holderL2_exponentRestriction {δ s : ℝ≥0} {o : X} {R : ℝ} {μ : Measure X}
    (hR : 0 < R) (hδs : δ ≤ s) (hδ : 0 < δ) (hs : 0 < s)
    (hμ : μ (ball o R) < ⊤) (f : H2.holderFunctions s (ball o R)) :
    H2.holderL2 δ (ball o R) μ hδ isOpen_ball.measurableSet hμ
      (chosenHolderRestriction hR hδs f) =
    H2.holderL2 s (ball o R) μ hs isOpen_ball.measurableSet hμ f :=
  holderL2_eq_of_function_eq hδ hs isOpen_ball.measurableSet hμ _ _ (chosenHolderRestriction_coe hR hδs f)

/-- Principal values of the exponent-restricted input yield the
same L2 element as principal values in the higher Holder class. -/
theorem holderL2_principalValue_exponentRestriction
    {D : H2.LocDoubling X} {d : H2.TruncDist D} (Q : H2.LocalKernelData D d)
    {δ s : ℝ≥0} (hδs : δ ≤ s)
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hs : 0 < s) (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (f : H2.holderFunctions s (ball Q.z Q.R)) :
    H2.holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
      (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν
        (chosenHolderRestriction Q.radius_pos hδs f)) =
    H2.holderL2 s (ball Q.z Q.R) D.μ hs isOpen_ball.measurableSet Q.measure_ball_lt_top
      (Q.principalValueHolderOperator hs hs₀ hsβ hsν f) :=
  holderL2_eq_of_function_eq hδ hs isOpen_ball.measurableSet Q.measure_ball_lt_top _ _
    (principalValueHolder_function_eq Q hδ hδ₀ hδβ hδν hs hs₀ hsβ hsν _ _ (chosenHolderRestriction_coe Q.radius_pos hδs f))

end RothschildStein.H3
