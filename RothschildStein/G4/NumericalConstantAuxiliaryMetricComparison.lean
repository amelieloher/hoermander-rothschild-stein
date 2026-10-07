-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalConstantShortBallSandwich
public import RothschildStein.G4.ConstantControlSelf
public import RothschildStein.G1.ControlSeparation
public import RothschildStein.G4.ShiftedChartBallRadius
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Primitive finite-jet and rank budgets give the
pointwise constant-control comparison. Constants precede the domain
and fields and use no injectivity theorem. -/
theorem exists_numerical_constant_auxiliary_metric_comparison (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ x ∈ ball x₀ (R/8), ∀ y,
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
        auxiliaryDistance (s := s) Ω w X x y ≤ constantShortDistance (s := s) Ω w X x y ∧
        constantShortDistance (s := s) Ω w X x y ≤ ENNReal.ofReal C *
          auxiliaryDistance (s := s) Ω w X x y := by
  obtain ⟨C,η,hC,hη,hbound⟩ := exists_numerical_constant_short_ball_sandwich
    k n s h q hn hs horder hq w M Δ R hM hΔ hR
  refine ⟨2*C,η/2,by positivity,by positivity,?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax x hx y hxy
  refine ⟨auxiliaryDistance_le_constantShortDistance Ω w X x y,?_⟩
  have hxR : x ∈ closedBall x₀ R := ball_subset_closedBall (ball_subset_ball (by linarith) hx)
  by_cases hzero : auxiliaryDistance (s := s) Ω w X x y = 0
  · have heq : x = y := (G1.controlDistance_eq_zero_iff hΩ
      (fun j => shortWeight w (shortIndex (s := s) w j))
      (fun j => shortField w X (shortIndex (s := s) w j))
      (fun j => (shortField_contDiffOn hΩ hX _).continuousOn) (hRΩ hxR)).mp hzero
    subst y
    change constantControlDistance Ω _ _ x x ≤ _
    rw [constantControlDistance_self _ _ (hRΩ hxR)]
    exact bot_le
  · let d := auxiliaryDistance (s := s) Ω w X x y
    have hdt : d ≠ ∞ := ne_top_of_lt (hxy.trans_le (le_top))
    have hdpos : 0 < d.toReal := ENNReal.toReal_pos hzero hdt
    have hdsmall : d.toReal < η/2 := by
      have hh := (ENNReal.toReal_lt_toReal hdt ENNReal.ofReal_ne_top).mpr hxy
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ η/2)] using hh
    have hcost := hbound Ω hΩ X hX hstep x₀ hRΩ hjets hmax x hx (2*d.toReal) (by positivity)
      (by linarith) (show y ∈ {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (2*d.toReal)} from by
        change d < ENNReal.ofReal (2*d.toReal)
        calc
          d = ENNReal.ofReal d.toReal := (ENNReal.ofReal_toReal hdt).symm
          _ < ENNReal.ofReal (2*d.toReal) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2*d.toReal)).mpr
              (by linarith))
    calc
      constantShortDistance (s := s) Ω w X x y ≤ ENNReal.ofReal (C*(2*d.toReal)) := hcost.le
      _ = ENNReal.ofReal (2*C) * d := by
        rw [show C*(2*d.toReal) = (2*C)*d.toReal by ring,
          ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hdt]
end RothschildStein.G4
