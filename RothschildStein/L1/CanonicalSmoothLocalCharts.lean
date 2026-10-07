-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartLocalInverse
public import RothschildStein.L1.SmoothLocalCharts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- Every second-variable chart has an actual local homeomorphism
with smooth forward and inverse maps on their entire open domains. -/
theorem theta_right_smooth_localChart (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hξ : ξ ∈ ball x D.radius) :
    ∃ e : OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ),
      (e : (Fin N → ℝ) → (Fin N → ℝ)) = (fun z => D.theta (η,z)) ∧ ξ ∈ e.source ∧
      e.source ⊆ ball x D.radius ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (e : (Fin N → ℝ) → (Fin N → ℝ)) e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => D.theta (η,z)) (ball x D.radius) :=
    D.theta_smooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => D.basePatch_subset ⟨hη,hz⟩)
  apply exists_smooth_local_chart_on _ isOpen_ball hθ _ ξ hξ
  intro z hz
  exact coordinateDerivative_injective_of_right_inverse _ _ z
    ((D.theta_right_contDiffAt η z hη hz).differentiableAt (by simp))
    ((D.forward_at_inverse_contDiffAt η z hη hz).differentiableAt (by simp))
    (D.right_inverse_eventually η z hη hz)

end CanonicalFrameChartData
end RothschildStein.L1
