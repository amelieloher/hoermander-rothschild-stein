-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneySelection

/-! Compact interior containment of dilated boundary-distance balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- Every closed dilate with dilation less than the boundary-distance denominator stays
in the open set. This gives the neighborhood needed for local smooth estimates. -/
theorem closedBall_boundaryRadius_subset {E : Type*} [MetricSpace E]
    {U : Set E} (hU : IsOpen U) (hcompl : Uᶜ.Nonempty) {z : E} (hz : z ∈ U)
    {c κ : ℝ} (hκ : 0 < κ) (hc : c < κ) :
    closedBall z (c * (infDist z Uᶜ / κ)) ⊆ U := by
  have hd : 0 < infDist z Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by simpa using hz)
  have ha : 0 < infDist z Uᶜ / κ := div_pos hd hκ
  have he : κ * (infDist z Uᶜ / κ) = infDist z Uᶜ := by field_simp [hκ.ne']
  have hlt : c * (infDist z Uᶜ / κ) < infDist z Uᶜ := by nlinarith
  exact (closedBall_subset_ball hlt).trans ball_infDist_compl_subset

end HeatKernel
