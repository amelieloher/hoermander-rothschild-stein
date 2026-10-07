-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The localized singular sum has support radius 2R on U. -/
theorem LocalKernelData.supported_localized_singular (Q : LocalKernelData D d) :
    SupportedKernel D (ball Q.z Q.R) (ball Q.z Q.R) (min Q.β₀ Q.β) 0 Q.singularA Q.singularS
      (2 * Q.R) Q.cutoffKernel := by
  have hsub : ball Q.z Q.R ⊆ D.Ω₁ := (ball_subset_ball (by linarith [Q.radius_pos])).trans Q.doubledBall_subset
  refine ⟨isOpen_ball.measurableSet, subset_rfl, hsub, by linarith [Q.radius_pos],
    by linarith [Q.radius_lt, D.κ_pos], Q.localized_singular.restrict isOpen_ball.measurableSet hsub, ?_⟩
  intro x _ y _ hr
  exact localizedKernel_support _ _ _ hr

/-- The principal-value operator is the explicit regularized-plus-T(1)
formula on the dense Hölder input class, BB Corollary 7.19, p. 309. -/
def LocalKernelData.principalValue (Q : LocalKernelData D d) (f : X → ℝ) : X → ℝ :=
  pvFormula D.μ (ball Q.z Q.R) Q.cutoffKernel Q.oneLimit f

/-- The regularized operator Hölder constant N₁. -/
def LocalKernelData.regularizedNormConstant (Q : LocalKernelData D d) (δ : ℝ) : ℝ :=
  regularizedHolderConstant (min Q.β₀ Q.β) δ D.C_D d.θ₁ d.θ₂ *
    (Q.singularA + Q.singularS + Q.cancellationConstant) +
      volumeIntegralConstant D.C_D δ * Q.singularA * (2 * Q.R) ^ δ

/-- The universal principal-value Hölder constant. -/
def LocalKernelData.operatorHolderConstant (Q : LocalKernelData D d) (δ : ℝ) : ℝ :=
  Q.regularizedNormConstant δ + Q.oneHolderConstant δ

/-- The universal T(1) Hölder constant is nonnegative. -/
theorem LocalKernelData.oneHolderConstant_nonneg (Q : LocalKernelData D d) {δ : ℝ}
    (hδ : 0 < δ) (hδ₀ : δ < Q.β₀) (hδν : δ < Q.ν) : 0 ≤ Q.oneHolderConstant δ := by
  have hCD : 0 < D.C_D := by linarith [D.one_lt_C_D]
  have hcδ := (volumeIntegralConstant_pos hCD hδ).le
  have hcreg := regularizedHolderConstant_nonneg hCD hδ hδ₀ d.θ₁_pos.le (d.θ₁_pos.trans_le d.θ₁_le).le
  have hsemi := fractionalSemiConstant_nonneg (R := 2 * Q.R) hCD D.κ_pos (by linarith [Q.radius_pos]) Q.ν_pos hδν
  have hcf : 0 ≤ fractionalHolderConstant D.C_D D.κ (2 * Q.R) δ Q.ν := by
    unfold fractionalHolderConstant
    exact add_nonneg hsemi (mul_nonneg (volumeIntegralConstant_pos hCD Q.ν_pos).le
      (Real.rpow_nonneg (by linarith [Q.radius_pos]) _))
  have hA₀ := Q.singular.A_nonneg
  have hS₀ := Q.singular.S_nonneg
  have hA₁ := Q.fractional.A_nonneg
  have hS₁ := Q.supported_localized_fractional.kernel.S_nonneg
  have hR := Q.radius_pos.le
  unfold LocalKernelData.oneHolderConstant
  positivity

/-- The regularized Hölder operator constant is nonnegative. -/
theorem LocalKernelData.regularizedNormConstant_nonneg (Q : LocalKernelData D d) {δ : ℝ}
    (hδ : 0 < δ) (hδs : δ < min Q.β₀ Q.β) : 0 ≤ Q.regularizedNormConstant δ := by
  have hCD : 0 < D.C_D := by linarith [D.one_lt_C_D]
  have hcδ := (volumeIntegralConstant_pos hCD hδ).le
  have hcreg := regularizedHolderConstant_nonneg hCD hδ hδs d.θ₁_pos.le (d.θ₁_pos.trans_le d.θ₁_le).le
  have hA := Q.localized_singular.A_nonneg
  have hS := Q.localized_singular.S_nonneg
  have hCc := Q.cancellationConstant_nonneg
  have hR := Q.radius_pos.le
  unfold LocalKernelData.regularizedNormConstant
  positivity

/-- The principal value exists with the explicit formula, BB p. 309. -/
theorem LocalKernelData.principalValue_limit (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f) {x : X}
    (hx : x ∈ ball Q.z Q.R) :
    Tendsto (fun ε : ℝ => truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x)
      (𝓝[>] 0) (𝓝 (Q.principalValue f x)) :=
  Q.supported_localized_singular.principalValue_limit d hδ hf hx (Q.one_limit hx)

/-- Singular integrals preserve bounded Hölder spaces, with an explicit
universal constant linear in the kernel data. BB Corollary 7.19, p. 309. -/
theorem LocalKernelData.principalValue_holder_bound (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f) :
    boundedHolderNorm δ (ball Q.z Q.R) (Q.principalValue f) ≤
      ENNReal.ofReal (Q.operatorHolderConstant δ) * boundedHolderNorm δ (ball Q.z Q.R) f := by
  have hδs : (δ : ℝ) < min Q.β₀ Q.β := lt_min hδ₀ hδβ
  have he := Q.supported_localized_singular.principalValue_holder_norm_le d Q.shellCancellation
    hδ hδs (γ := δ) le_rfl hf (Q.one_boundedHolder hδ hδ₀ hδβ.le hδν)
  simp only [sub_self, Real.rpow_zero, max_self, ENNReal.ofReal_one, one_mul] at he
  change boundedHolderNorm δ (ball Q.z Q.R) (Q.principalValue f) ≤
    (ENNReal.ofReal (Q.regularizedNormConstant δ) + boundedHolderNorm δ (ball Q.z Q.R) Q.oneLimit) *
      boundedHolderNorm δ (ball Q.z Q.R) f at he
  have hn := Q.one_holder_norm_le hδ hδ₀ hδβ.le hδν
  calc
    _ ≤ _ := he
    _ ≤ (ENNReal.ofReal (Q.regularizedNormConstant δ) + ENNReal.ofReal (Q.oneHolderConstant δ)) *
        boundedHolderNorm δ (ball Q.z Q.R) f := mul_le_mul_left (add_le_add le_rfl hn) _
    _ = _ := by
      change _ = ENNReal.ofReal (Q.regularizedNormConstant (δ : ℝ) +
        Q.oneHolderConstant (δ : ℝ)) * _
      rw [ENNReal.ofReal_add
        (Q.regularizedNormConstant_nonneg (δ := (δ : ℝ)) hδ hδs)
        (Q.oneHolderConstant_nonneg (δ := (δ : ℝ)) hδ hδ₀ hδν)]

/-- Membership in the bounded Hölder output space. -/
theorem LocalKernelData.principalValue_boundedHolder (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f) :
    BoundedHolder δ (ball Q.z Q.R) (Q.principalValue f) :=
  (Q.principalValue_holder_bound hδ hδ₀ hδβ hδν hf).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end RothschildStein.H2
