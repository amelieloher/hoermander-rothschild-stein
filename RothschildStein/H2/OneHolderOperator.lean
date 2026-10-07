-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularHolderOperators
public import RothschildStein.H2.HolderL2Inner

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The fixed T(1) coefficient has the cancellation supremum bound. -/
theorem LocalKernelData.oneLimit_abs_le (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) : |Q.oneLimit x| ≤ Q.cancellationConstant := by
  apply le_of_tendsto (Q.one_limit hx).abs
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact Q.truncated_one_bound hx hε

/-- The diagonal T(1) multiplication on the Hölder module. -/
def LocalKernelData.oneHolderOperator (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν) :
    holderFunctions δ (ball Q.z Q.R) →ₗ[ℝ] holderFunctions δ (ball Q.z Q.R) :=
  holderEndomorphism (fun f x => Q.oneLimit x * f x)
    (fun _ hf => (Q.one_boundedHolder hδ hδ₀ hδβ.le hδν).mul hf)
    (fun f g _ _ x _ => by simp only [Pi.add_apply]; ring)
    (fun c f x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- Pointwise diagonal formula on U. -/
theorem LocalKernelData.oneHolderOperator_apply (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) {x : X} (hx : x ∈ ball Q.z Q.R) :
    (Q.oneHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) x = Q.oneLimit x * (f : X → ℝ) x  := by
  change (ball Q.z Q.R).indicator (fun x => Q.oneLimit x * (f : X → ℝ) x) x = _
  exact indicator_of_mem hx _

/-- The diagonal Hölder bound uses the universal T(1) norm constant. -/
theorem LocalKernelData.oneHolderOperator_bound (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    holderFunctionSeminorm δ (ball Q.z Q.R) (Q.oneHolderOperator hδ hδ₀ hδβ hδν f) ≤
      Q.oneHolderConstant δ * holderFunctionSeminorm δ (ball Q.z Q.R) f := by
  apply holderEndomorphism_seminorm_le _ (Q.oneHolderConstant_nonneg hδ hδ₀ hδν)
  intro g
  rw [boundedHolderNorm_congr (fun _ hx => Q.oneHolderOperator_apply hδ hδ₀ hδβ hδν g hx)]
  exact (boundedHolderNorm_mul_le (Q.one_boundedHolder hδ hδ₀ hδβ.le hδν) g.property.1).trans
    (mul_le_mul_left (Q.one_holder_norm_le hδ hδ₀ hδβ.le hδν) _)

/-- The diagonal L² bound is C_c, independent of the Hölder norm. -/
theorem LocalKernelData.oneHolderOperator_l2_bound (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hμ : D.μ (ball Q.z Q.R) < ⊤) (f : holderFunctions δ (ball Q.z Q.R)) :
    ‖holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ
      (Q.oneHolderOperator hδ hδ₀ hδβ hδν f)‖ ≤
      Q.cancellationConstant * ‖holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet hμ f‖ :=
  holderL2_mul_norm_le hδ isOpen_ball.measurableSet hμ f _ Q.cancellationConstant_nonneg
    (fun _ hx => Q.oneLimit_abs_le hx) (fun _ hx => Q.oneHolderOperator_apply hδ hδ₀ hδβ hδν f hx)

end RothschildStein.H2
