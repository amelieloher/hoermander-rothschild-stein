-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedFar
public import RothschildStein.H2.FarCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Assemble A₁₁ and A₁₂ on the strict far region. The d'-shell
endpoint correction is retained. BB Theorem 7.12, p. 303. -/
theorem SupportedKernel.regularized_far_difference {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    |∫ y in G ∩ {y | 2 * dist x₀ x < dist x₀ y},
      K x y * (f y - f x) - K x₀ y * (f y - f x₀) ∂D.μ| ≤
      (volumeIntegralConstant D.C_D (β - δ) * S + C_K +
        cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ * A) *
          (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ) := by
  let F : Set X := {y | 2 * dist x₀ x < dist x₀ y}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  obtain ⟨his, hbs⟩ := hK.regularized_far_smooth hδ hδβ hf hx₀ hx hxx hκ
  obtain ⟨hik, hbk⟩ := hK.far_cancellation_bound d hCan hx₀ hx hxx hκ
  have hic : IntegrableOn (fun y => (f x₀ - f x) * K x y) (G ∩ F) D.μ := hik.const_mul (f x₀ - f x)
  have he : (∫ y in G ∩ F, K x y * (f y - f x) - K x₀ y * (f y - f x₀) ∂D.μ) =
      (∫ y in G ∩ F, (K x y - K x₀ y) * (f y - f x₀) ∂D.μ) +
        (f x₀ - f x) * ∫ y in G ∩ F, K x y ∂D.μ := by
    rw [← integral_const_mul, ← integral_add his hic]
    congr 1
    funext y
    ring
  have hdiff := sub_le_holderSemi hf.parts.2 (hK.sub_EG hx₀) (hK.sub_EG hx)
  have hc : 0 ≤ C_K + cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ * A :=
    (abs_nonneg _).trans hbk
  have hmul := mul_le_mul hdiff hbk (abs_nonneg _)
    (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg dist_nonneg (δ : ℝ)))
  rw [he]
  have hb := abs_add_le (∫ y in G ∩ F, (K x y - K x₀ y) * (f y - f x₀) ∂D.μ)
    ((f x₀ - f x) * ∫ y in G ∩ F, K x y ∂D.μ)
  rw [abs_mul] at hb
  nlinarith

end RothschildStein.H2
