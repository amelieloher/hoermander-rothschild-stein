-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ChartAnalyticData
public import RothschildStein.G4.ShiftedChartBallInclusions
public import RothschildStein.G4.ControlledChartPathLifting
public import RothschildStein.G4.InjectiveChartSmoothInverse
public import RothschildStein.G4.ZeroShiftTrajectoryCost
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators
namespace RothschildStein.G4

/-- Analytic estimates and actual trajectories give shifted
ball inclusions without any injectivity hypothesis. The shift radius is
chosen before the field family and all selected charts. -/
theorem exists_shifted_chart_ball_radius {m n s : ℕ} {a D : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      ∀ (w : Fin m → ℕ+) (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
        (B : Fin n → Fin m), (∀ i, (w (B i) : ℕ) ≤ s) →
      ∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ)
        (F : (Fin n → ℝ) → (Fin n → ℝ)) (Γ : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
        (r κ : ℝ), 0 < r → r ≤ 1 → 0 ≤ κ → (n : ℝ)*κ ≤ 1/4 →
      ∀ v ∈ weightedBox w (b*r), frameDet Z B x ≠ 0 →
      ChartAnalyticBounds Ω w Z B F (weightedBox (w ∘ B) (a*r)) r κ D →
      ChartTrajectories Ω Z B F (weightedBox (w ∘ B) (a*r)) x v Γ →
      let Q := weightedBox (w ∘ B) (a*r)
      ({y | controlDistance Ω w Z x y < ENNReal.ofReal (b*r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantControlDistance Ω w Z x y < ENNReal.ofReal (2*a*r)}) ∧
      ({y | constantControlDistance Ω w Z x y < ENNReal.ofReal (2*a*r)} ⊆
        {y | controlDistance Ω w Z x y < ENNReal.ofReal (2*a*r)}) ∧
      (v = 0 → F '' Q ⊆ {y | constantControlDistance Ω w Z x y < ENNReal.ofReal (a*r)})  := by
  obtain ⟨b,hb,hba,hb1,hlifter⟩ := exists_uniform_controlled_chart_lift_radius
    (m := m) (n := n) (s := s) ha ha1 hD
  refine ⟨b,hb,hba,hb1,?_⟩
  intro w Z B hw Ω x F Γ r κ hr hr1 hκ hsmall v hv hBx hAB htraj Q
  have hlift : ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w Z (2*b*r) γ →
      F 0 = γ 0 → ∃ θ, IsChartPathLift F γ θ Q 1 := by
    intro γ hγ hstart
    obtain ⟨θ,hθ,_,_⟩ := hlifter w B hw Z F r κ hr hr1 hκ hsmall
      hAB.1 hAB.2.2.1 hAB.2.2.2.1 hAB.2.2.2.2.1 hAB.2.2.2.2.2 Ω γ hγ hstart
    exact ⟨θ,hθ⟩
  have hballs := shifted_chart_ball_inclusions Ω w Z B F hBx ha hb
    (by linarith : b ≤ a) hr v hv Γ htraj hlift
  have hzeroUpper : v = 0 → F '' Q ⊆
      {y | constantControlDistance Ω w Z x y < ENNReal.ofReal (a*r)} := by
    intro hv0
    subst v
    rintro y ⟨u,hu,rfl⟩
    obtain ⟨hac,hmap,hinit,hend,hder⟩ := htraj u hu
    have he := selectedAuxiliaryTrajectory_zero_shift_cost_lt Ω w Z B
      (frame_index_injective_of_frameDet_ne_zero Z B hBx) (mul_pos ha hr) u hu
      (Γ u) hac hmap hder
    rw [hinit,hend] at he
    exact he
  exact ⟨hballs.1,hballs.2.1,hballs.2.2,hzeroUpper⟩
end RothschildStein.G4
