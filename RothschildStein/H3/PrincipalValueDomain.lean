-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LpPrincipalValueAgreement

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : H2.LocDoubling X} {d : H2.TruncDist D}

/-- The local principal value depends only on values in the
integration ball. The formula includes the same value at its center. -/
theorem principalValue_eqOn_of_eqOn (Q : H2.LocalKernelData D d)
    {f g : X → ℝ} (he : EqOn f g (ball Q.z Q.R)) :
    EqOn (Q.principalValue f) (Q.principalValue g) (ball Q.z Q.R) := by
  intro x hx
  unfold H2.LocalKernelData.principalValue H2.pvFormula
  rw [he hx]
  congr 1
  unfold H2.regularizedIntegral
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro y hy
  change Q.cutoffKernel x y * (f y - f x) = Q.cutoffKernel x y * (g y - g x)
  rw [he hy, he hx]

/-- Normalizing a Holder function outside the local domain preserves
its Lp class and its principal value at every point of the domain. -/
theorem holderNormalize_domain (Q : H2.LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f : X → ℝ} (hf : H2.BoundedHolder δ (ball Q.z Q.R) f)
    (p : ℝ≥0∞) :
    (holderLp D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
        (H2.holderNormalize hf) : X → ℝ) =ᵐ[D.μ.restrict (ball Q.z Q.R)] f ∧
    EqOn (Q.principalValue (H2.holderNormalize hf)) (Q.principalValue f)
      (ball Q.z Q.R) := by
  have he : EqOn (H2.holderNormalize hf : X → ℝ) f (ball Q.z Q.R) := by
    intro x hx
    exact indicator_of_mem hx f
  refine ⟨?_, principalValue_eqOn_of_eqOn Q he⟩
  exact (holderLp_coe_ae D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
    (H2.holderNormalize hf)).trans
    (by filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
        exact he hx)

end RothschildStein.H3
