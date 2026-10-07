-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShiftedChartBallInclusions

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- The new image lies in the old image when the new upper
control-ball radius is smaller than the old inner-ball radius. Both
inclusions concern the original ambient-domain distance (BB p. 456). -/
theorem chart_image_subset_of_control_ball_inclusions {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (F G : (Fin n → ℝ) → (Fin n → ℝ)) {S U : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} {c b r : ℝ} (hr : 0 ≤ r) (hcb : 2 * c ≤ b)
    (hnew : F '' S ⊆ {y | controlDistance Ω w Z x y < ENNReal.ofReal (2 * c * r)})
    (hold : {y | controlDistance Ω w Z x y < ENNReal.ofReal (b * r)} ⊆ G '' U) :
    F '' S ⊆ G '' U := by
  intro y hy
  apply hold
  exact (hnew hy).trans_le (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hcb hr))

/-- Actual selected-plus-auxiliary trajectories give the new
image's upper control-ball inclusion; the auxiliary shift has the same
small budget as the selected coordinates. -/
theorem chart_image_control_ball_subset_of_trajectories {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → Fin m)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hdet : frameDet Z B x ≠ 0) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (v : Fin m → ℝ) (hv : v ∈ weightedBox w (c * r))
    (Γ : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hflow : ∀ u ∈ weightedBox (w ∘ B) (c * r),
      AbsolutelyContinuousOnInterval (Γ u) 0 1 ∧ MapsTo (Γ u) (Icc (0 : ℝ) 1) Ω ∧
      Γ u 0 = x ∧ Γ u 1 = F u ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt (Γ u)
        (∑ j : Fin (n + m), Fin.append u v j • Z (Fin.addCases B id j) (Γ u t)) t) :
    F '' weightedBox (w ∘ B) (c * r) ⊆
      {y | controlDistance Ω w Z x y < ENNReal.ofReal (2 * c * r)} := by
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨hAC, hmap, hzero, hone, hode⟩ := hflow u hu
  have hcost := selectedAuxiliaryTrajectory_constant_cost_lt Ω w Z B
    (frame_index_injective_of_frameDet_ne_zero Z B hdet) hc hc le_rfl hr u v hu hv
    (Γ u) hAC hmap hode
  rw [hzero, hone] at hcost
  exact (controlDistance_le_constantControlDistance Ω w Z x (F u)).trans_lt hcost

end RothschildStein.G4
