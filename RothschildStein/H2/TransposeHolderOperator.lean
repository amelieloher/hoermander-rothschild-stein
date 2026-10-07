-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OneHolderOperator

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The transposed PV acts on the same concrete Hölder module,
although its Data D splitting can be different. -/
def TransposeData.principalValueHolderOperator {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < P.data.β₀)
    (hδβ : (δ : ℝ) < P.data.β) (hδν : (δ : ℝ) < P.data.ν) :
    holderFunctions δ (ball Q.z Q.R) →ₗ[ℝ] holderFunctions δ (ball Q.z Q.R) :=
  holderEndomorphism P.data.principalValue
    (fun f hf => by
      have hfp : BoundedHolder δ (ball P.data.z P.data.R) f := by simpa only [P.centre, P.radius] using hf
      simpa only [P.centre, P.radius] using P.data.principalValue_boundedHolder hδ hδ₀ hδβ hδν hfp)
    (fun f g hf hg x hx => by
      have hfp : BoundedHolder δ (ball P.data.z P.data.R) f := by simpa only [P.centre, P.radius] using hf
      have hgp : BoundedHolder δ (ball P.data.z P.data.R) g := by simpa only [P.centre, P.radius] using hg
      exact P.data.principalValue_add hδ hfp hgp (by simpa only [P.centre, P.radius] using hx))
    (fun c f x _ => P.data.principalValue_smul c f x)

/-- Pointwise formula of the transposed module operator. -/
theorem TransposeData.principalValueHolderOperator_apply {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < P.data.β₀)
    (hδβ : (δ : ℝ) < P.data.β) (hδν : (δ : ℝ) < P.data.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) {x : X} (hx : x ∈ ball Q.z Q.R) :
    (P.principalValueHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) x = P.data.principalValue f x :=
  indicator_of_mem hx _

/-- The transpose Hölder bound retains all transpose splitting constants. -/
theorem TransposeData.principalValueHolderOperator_bound {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < P.data.β₀)
    (hδβ : (δ : ℝ) < P.data.β) (hδν : (δ : ℝ) < P.data.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    holderFunctionSeminorm δ (ball Q.z Q.R) (P.principalValueHolderOperator hδ hδ₀ hδβ hδν f) ≤
      P.data.operatorHolderConstant δ * holderFunctionSeminorm δ (ball Q.z Q.R) f := by
  have hC : 0 ≤ P.data.operatorHolderConstant (δ : ℝ) :=
    add_nonneg (P.data.regularizedNormConstant_nonneg hδ (lt_min hδ₀ hδβ))
      (P.data.oneHolderConstant_nonneg hδ hδ₀ hδν)
  apply holderEndomorphism_seminorm_le _ hC
  intro g
  rw [boundedHolderNorm_congr (fun _ hx => P.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν g hx)]
  have hgp : BoundedHolder δ (ball P.data.z P.data.R) (g : X → ℝ) :=
    by simpa only [P.centre, P.radius] using g.property.1
  simpa only [P.centre, P.radius] using P.data.principalValue_holder_bound hδ hδ₀ hδβ hδν hgp

end RothschildStein.H2
