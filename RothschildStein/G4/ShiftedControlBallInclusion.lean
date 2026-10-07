-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartPathLift
public import RothschildStein.G1.WeightedTriangle

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.G4

/-- Actual short-path lifts yield the shifted inner ball
inclusion. The shift has quantified cost less than br; the triangle
inequality therefore gives an actual path of cost less than 2br
(BB Prop 9.52, (9.49), p. 449). -/
theorem controlBall_subset_chart_image_of_path_lifting {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Q : Set (Fin n → ℝ))
    {x : Fin n → ℝ} {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hshift : controlDistance Ω w Z (F 0) x < ENNReal.ofReal (b * r))
    (hlift : ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w Z (2 * b * r) γ →
      F 0 = γ 0 → ∃ θ, IsChartPathLift F γ θ Q 1) :
    {y | controlDistance Ω w Z x y < ENNReal.ofReal (b * r)} ⊆ F '' Q := by
  intro y hy
  have hdist : controlDistance Ω w Z (F 0) y < ENNReal.ofReal (2 * b * r) := by
    calc
      _ ≤ controlDistance Ω w Z (F 0) x + controlDistance Ω w Z x y :=
        G1.controlDistance_triangle Ω w Z (F 0) x y
      _ < ENNReal.ofReal (b * r) + ENNReal.ofReal (b * r) :=
        ENNReal.add_lt_add hshift hy
      _ = ENNReal.ofReal (2 * b * r) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hb.le hr.le) (mul_nonneg hb.le hr.le)]
        congr 1
        ring
  obtain ⟨δ, _hδ, hδr, γ, hγ, hγ0, hγ1⟩ := G1.exists_controlledCurve_of_controlDistance_lt hdist
  obtain ⟨θ, hθ⟩ := hlift γ (G1.isControlledCurve_mono_parameter hγ hδr.le) hγ0.symm
  exact ⟨θ 1, hθ.2.2.1 ⟨zero_le_one, le_rfl⟩,
    (hθ.2.2.2 ⟨zero_le_one, le_rfl⟩).trans hγ1⟩

end RothschildStein.G4
