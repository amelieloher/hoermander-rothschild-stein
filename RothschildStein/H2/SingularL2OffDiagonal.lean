-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OffDiagonalOn
public import RothschildStein.H2.SingularL2Adjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The actual L² PV extension has the absolutely convergent
ordinary integral representation away from supported inputs. -/
theorem TransposeData.l2Operator_offDiagonal {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    OffDiagonalL2 D (ball Q.z Q.R) Q.cutoffKernel
      (P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν') := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  apply Q.offDiagonal_of_holder_formula hδ hδ₁
  intro f
  rw [P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν']
  let g := Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f
  filter_upwards [(g.property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top).coeFn_toLp,
    ae_restrict_mem isOpen_ball.measurableSet] with x hx hxU
  exact hx.trans (Q.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν f hxU)

/-- The transpose extension has the matching representation
for the transposed localized kernel and the same fixed gauge. -/
theorem TransposeData.transposeL2Operator_offDiagonal {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    OffDiagonalL2 D (ball Q.z Q.R) P.data.cutoffKernel
      (P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν') := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  apply P.data.offDiagonal_on_of_holder_formula
    (show ball Q.z Q.R = ball P.data.z P.data.R by rw [P.centre, P.radius])
    isOpen_ball.measurableSet Q.measure_ball_lt_top hδ hδ₁
  intro f
  rw [P.transposeL2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν']
  let g := P.principalValueHolderOperator hδ hδ₀' hδβ' hδν' f
  filter_upwards [(g.property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top).coeFn_toLp,
    ae_restrict_mem isOpen_ball.measurableSet] with x hx hxU
  exact hx.trans (P.principalValueHolderOperator_apply hδ hδ₀' hδβ' hδν' f hxU)

end RothschildStein.H2
