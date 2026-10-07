-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointPullbackFields
public import RothschildStein.L1.RadialFrameDifferentiation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual canonical tangent frame is smooth on the common coefficient ball. -/
theorem coordinateField_contDiffOn (D : CanonicalFrameChartData Ω Y x)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (η : Fin N → ℝ) (hη : η ∈ ball x D.radius) (i : Fin N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.coordinateField η i) (ball 0 D.radius) := by
  have harg : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : Fin N → ℝ => (η,u)) (ball 0 D.radius) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := (D.pullbackField_contDiffOn_joint (Y i) (hY i)).comp harg
    (fun u hu => ⟨hη,hu⟩)
  exact h

end CanonicalFrameChartData
end RothschildStein.L1
