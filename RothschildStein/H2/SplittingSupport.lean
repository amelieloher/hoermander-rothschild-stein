-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingKernelClass
public import RothschildStein.H2.PrincipalValueLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The doubled input ball lies inside the middle doubling domain. -/
theorem LocalKernelData.doubledBall_subset (Q : LocalKernelData D d) :
    ball Q.z (2 * Q.R) ⊆ D.Ω₁ :=
  (ball_subset_ball (by linarith [Q.radius_lt, D.κ_pos])).trans
    (ball_subset_closedBall.trans (D.incl₀ Q.z Q.center))

/-- The two pieces vanish at metric distance at least R, as follows
from their separate d'-support hypotheses and R'≤θ₁R. -/
theorem LocalKernelData.metric_support (Q : LocalKernelData D d) {x y : X}
    (hx : x ∈ ball Q.z Q.R) (hy : y ∈ ball Q.z (2 * Q.R)) (hr : Q.R ≤ dist x y) :
    Q.K₀ x y = 0 ∧ Q.K₁ x y = 0 := by
  have hx₂ : x ∈ ball Q.z (2 * Q.R) := ball_subset_ball (by linarith [Q.radius_pos]) hx
  have he : Q.R' ≤ d.d' x y := Q.support_radius_le.trans
    ((mul_le_mul_of_nonneg_left hr d.θ₁_pos.le).trans
      (d.comp x (Q.doubledBall_subset hx₂) y (Q.doubledBall_subset hy)).1)
  exact ⟨Q.support₀ x hx y hy he, Q.support₁ x hx y hy he⟩

/-- Data D supplies exactly the supported singular-kernel setting
needed for the regularized term on the doubled ball. -/
theorem LocalKernelData.supported_singular (Q : LocalKernelData D d) :
    SupportedKernel D (ball Q.z Q.R) (ball Q.z (2 * Q.R)) Q.β₀ 0 Q.A₀ Q.S₀ Q.R Q.K₀ := by
  refine ⟨isOpen_ball.measurableSet, ball_subset_ball (by linarith [Q.radius_pos]),
    Q.doubledBall_subset, Q.radius_pos, ?_, Q.singular, ?_⟩
  · linarith [Q.radius_lt, D.κ_pos]
  · intro x hx y hy hr
    exact (Q.metric_support hx hy hr).1

/-- BB (7.15), p. 307: every positive truncation of the singular
piece integrates to zero. Separate piece support removes the endpoint R'. -/
theorem LocalKernelData.truncated_singular_one_eq_zero (Q : LocalKernelData D d)
    {x : X} (hx : x ∈ ball Q.z Q.R) {ε : ℝ} (hε : 0 < ε) :
    truncatedIntegral D.μ (ball Q.z (2 * Q.R)) d.d' Q.K₀ ε (fun _ => 1) x = 0 := by
  classical
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hT : MeasurableSet {y | ε < d.d' x y} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {y | ε < d.d' x y ∧ d.d' x y < Q.R'} :=
    hT.inter (measurableSet_lt hm measurable_const)
  unfold truncatedIntegral
  simp only [mul_one]
  by_cases he : ε < Q.R'
  · have hz := Q.vanishing x hx ε Q.R' hε he le_rfl
    rw [← hz]
    rw [← setIntegral_indicator hT, ← setIntegral_indicator hS]
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro y hy
    by_cases hyε : ε < d.d' x y
    · by_cases hyR : d.d' x y < Q.R'
      · simp [hyε, hyR]
      · simp [hyε, hyR, Q.support₀ x hx y hy (le_of_not_gt hyR)]
    · simp [hyε]
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact Q.support₀ x hx y hy.1 ((le_of_not_gt he).trans hy.2.le)

end RothschildStein.H2
