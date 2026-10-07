-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamily
public import RothschildStein.P1.PaddingCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- Two actual families centered at a lifted point share a
positive closed neighborhood of admissible centers. This neighborhood
is chosen before selecting any frame or application radius. -/
theorem paired_family_center_neighborhood {q n m s : ℕ} {w : Fin q → ℕ+}
    {Uo : Set (Fin n → ℝ)} {Ul : Set (Fin (n+m) → ℝ)}
    {Xo : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {Xl : Fin q → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ)}
    {ξ : Fin (n+m) → ℝ} {tO tl : ℝ}
    (Fo : JointShortChartFamily (n := n) (s := s) w Uo Xo (basePoint ξ) tO)
    (Fl : JointShortChartFamily (n := n+m) (s := s) w Ul Xl ξ tl) :
    ∃ R : ℝ, 0 < R ∧ ∀ ζ ∈ closedBall ξ R,
      basePoint ζ ∈ closedBall (basePoint ξ) (Fo.R/16) ∧
      ζ ∈ closedBall ξ (Fl.R/16) := by
  have hp : Continuous (basePoint (n := n) (m := m)) :=
    (P1.paddingBaseCLM n m).continuous
  have ho : IsOpen ((basePoint ⁻¹' ball (basePoint ξ) (Fo.R/16)) ∩
      ball ξ (Fl.R/16)) := (isOpen_ball.preimage hp).inter isOpen_ball
  have hc : ξ ∈ (basePoint ⁻¹' ball (basePoint ξ) (Fo.R/16)) ∩
      ball ξ (Fl.R/16) := by
    exact ⟨mem_ball_self (div_pos Fo.R_pos (by norm_num)),
      mem_ball_self (div_pos Fl.R_pos (by norm_num))⟩
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp ho ξ hc
  refine ⟨r/2,by positivity,?_⟩
  intro ζ hζ
  have hz := hsub (closedBall_subset_ball (by linarith) hζ)
  exact ⟨ball_subset_closedBall hz.1,ball_subset_closedBall hz.2⟩

end RothschildStein.L1
