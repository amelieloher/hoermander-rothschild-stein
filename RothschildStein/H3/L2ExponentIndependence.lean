-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExponentRestrictionL2
public import RothschildStein.H2.SingularL2Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : H2.LocDoubling X} {d : H2.TruncDist D}

/-- Uniqueness identifies two L2 realizations when one construction
exponent is lower than the other. The higher-exponent dense domain embeds
into the lower-exponent domain on the actual bounded integration ball. -/
theorem l2Operator_apply_higher_exponent {Q : H2.LocalKernelData D d} (P : H2.TransposeData Q)
    {δ s : ℝ≥0} (hδ : 0 < δ)
    (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (hs : 0 < s)
    (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (_hs₀' : (s : ℝ) < P.data.β₀) (_hsβ' : (s : ℝ) < P.data.β) (_hsν' : (s : ℝ) < P.data.ν)
    (hδs : δ ≤ s) (f : H2.holderFunctions s (ball Q.z Q.R)) :
    P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      (H2.holderL2 s (ball Q.z Q.R) D.μ hs isOpen_ball.measurableSet Q.measure_ball_lt_top f) =
    H2.holderL2 s (ball Q.z Q.R) D.μ hs isOpen_ball.measurableSet Q.measure_ball_lt_top
      (Q.principalValueHolderOperator hs hs₀ hsβ hsν f) := by
  exact (congrArg (P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν')
    (holderL2_exponentRestriction Q.radius_pos hδs hδ hs Q.measure_ball_lt_top f).symm).trans
    ((P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      (chosenHolderRestriction Q.radius_pos hδs f)).trans
      (holderL2_principalValue_exponentRestriction Q hδs hδ hδ₀ hδβ hδν
        hs hs₀ hsβ hsν f))

/-- Uniqueness identifies two L2 realizations when one construction
exponent is lower than the other. The higher-exponent dense domain embeds
into the lower-exponent domain on the actual bounded integration ball. -/
theorem l2Operator_eq_of_exponent_le {Q : H2.LocalKernelData D d} (P : H2.TransposeData Q)
    {δ s : ℝ≥0} (hδ : 0 < δ)
    (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (hs : 0 < s)
    (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (hs₀' : (s : ℝ) < P.data.β₀) (hsβ' : (s : ℝ) < P.data.β) (hsν' : (s : ℝ) < P.data.ν)
    (hδs : δ ≤ s) :
    P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' =
      P.l2Operator hs hs₀ hsβ hsν hs₀' hsβ' hsν' := by
  exact P.l2Operator_unique hs hs₀ hsβ hsν hs₀' hsβ' hsν' _
    (l2Operator_apply_higher_exponent P hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      hs hs₀ hsβ hsν hs₀' hsβ' hsν' hδs)

/-- The bounded local L2 realization is independent of the Holder
exponent used for its construction. It agrees for every positive Holder
exponent allowed by the kernel hypotheses, by uniqueness of the L2 extension. -/
theorem l2Operator_independent_exponent {Q : H2.LocalKernelData D d} (P : H2.TransposeData Q)
    {δ s : ℝ≥0} (hδ : 0 < δ)
    (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (hs : 0 < s)
    (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (hs₀' : (s : ℝ) < P.data.β₀) (hsβ' : (s : ℝ) < P.data.β) (hsν' : (s : ℝ) < P.data.ν) :
    P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' =
      P.l2Operator hs hs₀ hsβ hsν hs₀' hsβ' hsν' := by
  rcases le_total δ s with h | h
  · exact l2Operator_eq_of_exponent_le P hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      hs hs₀ hsβ hsν hs₀' hsβ' hsν' h
  · exact (l2Operator_eq_of_exponent_le P hs hs₀ hsβ hsν hs₀' hsβ' hsν'
      hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' h).symm

end RothschildStein.H3
