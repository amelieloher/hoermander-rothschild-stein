-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularL2Bounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The actual L² extension of the fixed-gauge principal value. -/
def TransposeData.l2Operator {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (_hδ₀' : (δ : ℝ) < P.data.β₀) (_hδβ' : (δ : ℝ) < P.data.β) (_hδν' : (δ : ℝ) < P.data.ν) :
    Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) →L[ℝ] Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) :=
  let e := holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  (e.comp (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν)).extendOfNorm e

/-- The actual extension of the transposed principal value. -/
def TransposeData.transposeL2Operator {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (_hδ₀ : (δ : ℝ) < Q.β₀) (_hδβ : (δ : ℝ) < Q.β) (_hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) →L[ℝ] Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) :=
  let e := holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  (e.comp (P.principalValueHolderOperator hδ hδ₀' hδβ' hδν')).extendOfNorm e

/-- The L² extension agrees with the principal value on the dense class. -/
theorem TransposeData.l2Operator_apply {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f) =
    holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
      (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f) := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  exact LinearMap.extendOfNorm_eq
    (holderL2_denseRange hδ hδ₁ isOpen_ball isBounded_ball Q.measure_ball_lt_top)
    ⟨P.l2Constant δ, fun g => (P.holder_l2_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' g).1⟩ f

/-- Agreement of the transpose extension on the dense class. -/
theorem TransposeData.transposeL2Operator_apply {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f) =
    holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
      (P.principalValueHolderOperator hδ hδ₀' hδβ' hδν' f) := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  exact LinearMap.extendOfNorm_eq
    (holderL2_denseRange hδ hδ₁ isOpen_ball isBounded_ball Q.measure_ball_lt_top)
    ⟨P.l2Constant δ, fun g => (P.holder_l2_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' g).2⟩ f

/-- Both extended operators have the universal norm bound. -/
theorem TransposeData.l2Operator_norm_bounds {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    ‖P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'‖ ≤ P.l2Constant δ ∧
      ‖P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'‖ ≤ P.l2Constant δ := by
  have hδ₁ : δ ≤ 1 := by exact_mod_cast (hδ₀.trans_le Q.singular.β_le_one).le
  have hd := holderL2_denseRange hδ hδ₁ isOpen_ball isBounded_ball Q.measure_ball_lt_top
  exact ⟨LinearMap.opNorm_extendOfNorm_le hd (P.l2Constant_nonneg δ)
      (fun f => (P.holder_l2_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' f).1),
    LinearMap.opNorm_extendOfNorm_le hd (P.l2Constant_nonneg δ)
      (fun f => (P.holder_l2_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' f).2)⟩

end RothschildStein.H2
