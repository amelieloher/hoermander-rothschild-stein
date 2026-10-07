-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderOperatorRelations
public import RothschildStein.H2.HolderKrein

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The integration patch has finite measure. -/
theorem LocalKernelData.measure_ball_lt_top (Q : LocalKernelData D d) :
    D.μ (ball Q.z Q.R) < ⊤ :=
  (measure_mono (Q.supported_localized_singular.sub_G.trans D.sub₁₂)).trans_lt D.finΩ₂

/-- The universal L² constant retains both splittings and
both T(1) Hölder bounds: sqrt(N₁ (N₂ + Hᵗ + H)) + C_c. -/
def TransposeData.l2Constant {Q : LocalKernelData D d} (P : TransposeData Q) (δ : ℝ) : ℝ :=
  Real.sqrt (Q.regularizedNormConstant δ *
    (P.data.operatorHolderConstant δ + Q.oneHolderConstant δ)) + Q.cancellationConstant

/-- The L² constant is nonnegative. -/
theorem TransposeData.l2Constant_nonneg {Q : LocalKernelData D d} (P : TransposeData Q) (δ : ℝ) :
    0 ≤ P.l2Constant δ := add_nonneg (Real.sqrt_nonneg _) Q.cancellationConstant_nonneg

/-- Both principal values satisfy the source's universal L²
bound on the dense Hölder class. The L² bound applies to the regularized map and its transpose; diagonal multiplication contributes C_c. -/
theorem TransposeData.holder_l2_bounds {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    let e := holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
    ‖e (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f)‖ ≤ P.l2Constant δ * ‖e f‖ ∧
      ‖e (P.principalValueHolderOperator hδ hδ₀' hδβ' hδν' f)‖ ≤ P.l2Constant δ * ‖e f‖ := by
  let U := ball Q.z Q.R
  let e := holderL2 δ U D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  let N := holderFunctionSeminorm δ U
  let R := Q.regularizedHolderOperator hδ hδ₀ hδβ
  let T := Q.principalValueHolderOperator hδ hδ₀ hδβ hδν
  let T' := P.principalValueHolderOperator hδ hδ₀' hδβ' hδν'
  let M := Q.oneHolderOperator hδ hδ₀ hδβ hδν
  let R' := T' - M
  let a := Q.regularizedNormConstant (δ : ℝ)
  let b := P.data.operatorHolderConstant (δ : ℝ) + Q.oneHolderConstant (δ : ℝ)
  have ha : 0 ≤ a := Q.regularizedNormConstant_nonneg hδ (lt_min hδ₀ hδβ)
  have hb : 0 ≤ b := add_nonneg
    (add_nonneg (P.data.regularizedNormConstant_nonneg hδ (lt_min hδ₀' hδβ'))
      (P.data.oneHolderConstant_nonneg hδ hδ₀' hδν')) (Q.oneHolderConstant_nonneg hδ hδ₀ hδν)
  have hT : T = R + M := Q.principalValueHolderOperator_eq hδ hδ₀ hδβ hδν
  have hR : ∀ g, N (R g) ≤ a * N g := Q.regularizedHolderOperator_bound hδ hδ₀ hδβ
  have hR' : ∀ g, N (R' g) ≤ b * N g := by
    intro g
    calc
      _ ≤ N (T' g) + N (M g) := map_sub_le_add N _ _
      _ ≤ P.data.operatorHolderConstant δ * N g + Q.oneHolderConstant δ * N g :=
        add_le_add (P.principalValueHolderOperator_bound hδ hδ₀' hδβ' hδν' g)
          (Q.oneHolderOperator_bound hδ hδ₀ hδβ hδν g)
      _ = b * N g := by dsimp [b]; ring
  have hadj : ∀ g h, inner ℝ (e (R g)) (e h) = inner ℝ (e g) (e (R' h)) := by
    intro g h
    have hr : R = T - M := by rw [hT]; abel
    rw [hr, LinearMap.sub_apply, map_sub, inner_sub_left,
      show R' h = T' h - M h from rfl, map_sub, inner_sub_right]
    rw [P.holderOperator_adjoint hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' Q.measure_ball_lt_top,
      Q.oneHolderOperator_symmetric hδ hδ₀ hδβ hδν Q.measure_ball_lt_top]
  have hRf := holder_krein_bound D hδ isOpen_ball Q.supported_localized_singular.sub_G
    Q.measure_ball_lt_top R R' ha hb hR hR' hadj f
  have hadj' : ∀ g h, inner ℝ (e (R' g)) (e h) = inner ℝ (e g) (e (R h)) := by
    intro g h
    rw [real_inner_comm, ← hadj h g, real_inner_comm]
  have hR'f := holder_krein_bound D hδ isOpen_ball Q.supported_localized_singular.sub_G
    Q.measure_ball_lt_top R' R hb ha hR' hR hadj' f
  rw [mul_comm b a] at hR'f
  have hMf := Q.oneHolderOperator_l2_bound hδ hδ₀ hδβ hδν Q.measure_ball_lt_top f
  have ht' : T' = R' + M := by dsimp [R']; abel
  constructor
  · change ‖e (T f)‖ ≤ _
    rw [hT, LinearMap.add_apply, map_add]
    exact (norm_add_le _ _).trans ((add_le_add hRf hMf).trans_eq (by dsimp [TransposeData.l2Constant, a, b]; ring))
  · change ‖e (T' f)‖ ≤ _
    rw [ht', LinearMap.add_apply, map_add]
    exact (norm_add_le _ _).trans ((add_le_add hR'f hMf).trans_eq (by dsimp [TransposeData.l2Constant, a, b]; ring))

end RothschildStein.H2
