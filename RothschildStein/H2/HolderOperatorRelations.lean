-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TransposeHolderOperator
public import RothschildStein.H2.PrincipalValueAdjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The PV operator splits into its regularized part and diagonal T(1). -/
theorem LocalKernelData.principalValueHolderOperator_eq (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν) :
    Q.principalValueHolderOperator hδ hδ₀ hδβ hδν =
      Q.regularizedHolderOperator hδ hδ₀ hδβ + Q.oneHolderOperator hδ hδ₀ hδβ hδν := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) x =
    (Q.regularizedHolderOperator hδ hδ₀ hδβ f : X → ℝ) x +
      (Q.oneHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) x
  by_cases hx : x ∈ ball Q.z Q.R
  · rw [Q.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν f hx,
      Q.regularizedHolderOperator_apply hδ hδ₀ hδβ f hx,
      Q.oneHolderOperator_apply hδ hδ₀ hδβ hδν f hx]
    rfl
  · rw [(Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f).property.2 x hx,
      (Q.regularizedHolderOperator hδ hδ₀ hδβ f).property.2 x hx,
      (Q.oneHolderOperator hδ hδ₀ hδβ hδν f).property.2 x hx, zero_add]

/-- The diagonal operator is symmetric for the L² inner product. -/
theorem LocalKernelData.oneHolderOperator_symmetric (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hμ : D.μ (ball Q.z Q.R) < ⊤) (f g : holderFunctions δ (ball Q.z Q.R)) :
    inner ℝ (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ
      (Q.oneHolderOperator hδ hδ₀ hδβ hδν f))
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ g) =
    inner ℝ (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ f)
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ
      (Q.oneHolderOperator hδ hδ₀ hδβ hδν g)) := by
  rw [holderL2_inner, holderL2_inner]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro x hx
  dsimp only
  rw [Q.oneHolderOperator_apply hδ hδ₀ hδβ hδν f hx,
    Q.oneHolderOperator_apply hδ hδ₀ hδβ hδν g hx]
  ring

/-- Adjointness as an identity of the embedded Hölder operators. -/
theorem TransposeData.holderOperator_adjoint {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (hμ : D.μ (ball Q.z Q.R) < ⊤) (f g : holderFunctions δ (ball Q.z Q.R)) :
    inner ℝ (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ
      (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f))
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ g) =
    inner ℝ (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ f)
      (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ
      (P.principalValueHolderOperator hδ hδ₀' hδβ' hδν' g)) := by
  rw [holderL2_inner, holderL2_inner]
  calc
    _ = ∫ x in ball Q.z Q.R, Q.principalValue f x * (g : X → ℝ) x ∂D.μ := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro x hx
      dsimp only
      rw [Q.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν f hx]
    _ = ∫ x in ball Q.z Q.R, (f : X → ℝ) x * P.data.principalValue g x ∂D.μ :=
      P.principalValue_adjoint hδ f.property.1 g.property.1
    _ = _ := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro x hx
      dsimp only
      rw [P.principalValueHolderOperator_apply hδ hδ₀' hδβ' hδν' g hx]

end RothschildStein.H2
