-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShiftedControlBallInclusion
public import RothschildStein.G4.SelectedAuxiliaryTrajectoryCost
public import RothschildStein.G1.ControlledReparam

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- All three shifted ball inclusions follow from actual
selected-plus-auxiliary trajectories and the constructed short-path
lifts. The shift budget is br, and repeated fields give exactly the
factor-two upper radius (BB Prop 9.52, pp. 448–449). -/
theorem shifted_chart_ball_inclusions {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → Fin m)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hdet : frameDet Z B x ≠ 0)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hr : 0 < r)
    (v : Fin m → ℝ) (hv : v ∈ weightedBox w (b * r))
    (Γ : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hflow : ∀ u ∈ weightedBox (w ∘ B) (a * r),
      AbsolutelyContinuousOnInterval (Γ u) 0 1 ∧ MapsTo (Γ u) (Icc (0 : ℝ) 1) Ω ∧
      Γ u 0 = x ∧ Γ u 1 = F u ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt (Γ u)
        (∑ j : Fin (n + m), Fin.append u v j • Z (Fin.addCases B id j) (Γ u t)) t)
    (hlift : ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w Z (2 * b * r) γ →
      F 0 = γ 0 → ∃ θ, IsChartPathLift F γ θ (weightedBox (w ∘ B) (a * r)) 1) :
    ({y | controlDistance Ω w Z x y < ENNReal.ofReal (b * r)} ⊆
      F '' weightedBox (w ∘ B) (a * r)) ∧
    (F '' weightedBox (w ∘ B) (a * r) ⊆
      {y | constantControlDistance Ω w Z x y < ENNReal.ofReal (2 * a * r)}) ∧
    ({y | constantControlDistance Ω w Z x y < ENNReal.ofReal (2 * a * r)} ⊆
      {y | controlDistance Ω w Z x y < ENNReal.ofReal (2 * a * r)}) := by
  have hzero : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ B) (a * r) := by
    intro i
    change |(0 : ℝ)| < (a * r) ^ (w (B i) : ℕ)
    rw [abs_zero]
    exact pow_pos (mul_pos ha hr) _
  obtain ⟨hAC0, hmap0, hinit0, hend0, hd0⟩ := hflow 0 hzero
  have hshift := selectedAuxiliaryShift_constant_cost_lt Ω w Z B hb hr v hv (Γ 0) hAC0 hmap0 hd0
  rw [hinit0, hend0] at hshift
  have hshift' : controlDistance Ω w Z (F 0) x < ENNReal.ofReal (b * r) := by
    rw [G1.controlDistance_symm Ω w Z (F 0) x]
    exact (controlDistance_le_constantControlDistance Ω w Z x (F 0)).trans_lt hshift
  refine ⟨controlBall_subset_chart_image_of_path_lifting Ω w Z F _ hb hr hshift' hlift, ?_, ?_⟩
  · rintro y ⟨u, hu, rfl⟩
    change constantControlDistance Ω w Z x (F u) < ENNReal.ofReal (2 * a * r)
    obtain ⟨hAC, hmap, hinit, hend, hd⟩ := hflow u hu
    have hc := selectedAuxiliaryTrajectory_constant_cost_lt Ω w Z B
      (frame_index_injective_of_frameDet_ne_zero Z B hdet) ha hb hba hr u v hu hv
      (Γ u) hAC hmap hd
    rw [hinit, hend] at hc
    exact hc
  · intro y hy
    exact (controlDistance_le_constantControlDistance Ω w Z x y).trans_lt hy

end RothschildStein.G4
