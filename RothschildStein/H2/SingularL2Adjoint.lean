-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularL2Extension
public import RothschildStein.H2.DenseOperatorAdjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The extended fixed-gauge principal values are adjoints on all L². -/
theorem TransposeData.l2Operator_adjoint {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (v w : Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R))) :
    inner ℝ (P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' v) w =
      inner ℝ v (P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' w) := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  apply adjoint_of_denseRange
    (holderL2_denseRange hδ hδ₁ isOpen_ball isBounded_ball Q.measure_ball_lt_top)
  intro f g
  rw [P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν',
    P.transposeL2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν']
  exact P.holderOperator_adjoint hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' Q.measure_ball_lt_top f g

/-- Uniqueness of the extension from the dense principal-value domain. -/
theorem TransposeData.l2Operator_unique {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (S : Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) →L[ℝ] Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)))
    (hS : ∀ f : holderFunctions δ (ball Q.z Q.R),
      S (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f) =
        holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
          (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f)) :
    S = P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  apply operator_unique_of_denseRange
    (holderL2_denseRange hδ hδ₁ isOpen_ball isBounded_ball Q.measure_ball_lt_top)
  intro f
  rw [hS f, P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν']

end RothschildStein.H2
