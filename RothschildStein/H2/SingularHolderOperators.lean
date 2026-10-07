-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderEndomorphism
public import RothschildStein.H2.TransposeData

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The regularized singular operator acts linearly on the Hölder module. -/
def LocalKernelData.regularizedHolderOperator (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) :
    holderFunctions δ (ball Q.z Q.R) →ₗ[ℝ] holderFunctions δ (ball Q.z Q.R) :=
  holderEndomorphism (regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel)
    (fun _ hf => Q.supported_localized_singular.regularized_boundedHolder d Q.shellCancellation
      hδ (lt_min hδ₀ hδβ) hf)
    (fun _ _ hf hg _ hx => Q.regularized_add hδ hf hg hx)
    (fun c f x _ => Q.regularized_smul c f x)

/-- The regularized operator agrees with its integral on U. -/
theorem LocalKernelData.regularizedHolderOperator_apply (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β)
    (f : holderFunctions δ (ball Q.z Q.R)) {x : X} (hx : x ∈ ball Q.z Q.R) :
    (Q.regularizedHolderOperator hδ hδ₀ hδβ f : X → ℝ) x =
      regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel f x := indicator_of_mem hx _

/-- The regularized Hölder operator has exactly the N₁ bound. -/
theorem LocalKernelData.regularizedHolderOperator_bound (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    holderFunctionSeminorm δ (ball Q.z Q.R) (Q.regularizedHolderOperator hδ hδ₀ hδβ f) ≤
      Q.regularizedNormConstant δ * holderFunctionSeminorm δ (ball Q.z Q.R) f := by
  apply holderEndomorphism_seminorm_le _ (Q.regularizedNormConstant_nonneg hδ (lt_min hδ₀ hδβ))
  intro g
  rw [boundedHolderNorm_congr (fun _ hx => Q.regularizedHolderOperator_apply hδ hδ₀ hδβ g hx)]
  have he := Q.supported_localized_singular.regularized_holder_norm_le d Q.shellCancellation
    hδ (lt_min hδ₀ hδβ) g.property.1
  change boundedHolderNorm δ (ball Q.z Q.R)
    (regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel g) ≤
    ENNReal.ofReal (Q.regularizedNormConstant δ) * holderSemi δ (ball Q.z Q.R) g at he
  exact he.trans (mul_le_mul_right (le_add_left le_rfl) _)

/-- The principal value acts linearly on the Hölder module. -/
def LocalKernelData.principalValueHolderOperator (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν) :
    holderFunctions δ (ball Q.z Q.R) →ₗ[ℝ] holderFunctions δ (ball Q.z Q.R) :=
  holderEndomorphism Q.principalValue
    (fun _ hf => Q.principalValue_boundedHolder hδ hδ₀ hδβ hδν hf)
    (fun _ _ hf hg _ hx => Q.principalValue_add hδ hf hg hx)
    (fun c f x _ => Q.principalValue_smul c f x)

/-- The linear PV operator agrees with its fixed-gauge formula on U. -/
theorem LocalKernelData.principalValueHolderOperator_apply (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) {x : X} (hx : x ∈ ball Q.z Q.R) :
    (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) x = Q.principalValue f x :=
  indicator_of_mem hx _

end RothschildStein.H2
