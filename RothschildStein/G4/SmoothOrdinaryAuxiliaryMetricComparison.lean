-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothOrdinaryAuxiliaryComparison
public import RothschildStein.G1.ControlSeparation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Two-sided comparison of the actual extended distances on
an original-domain patch, including coincident endpoints. -/
theorem exists_smooth_ordinary_auxiliary_metric_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C ε : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < C ∧ 0 < ε ∧
      ∀ x ∈ closedBall z (R/2), ∀ y ∈ closedBall z (R/2),
      auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
      auxiliaryDistance (s := s) Ω w X x y ≤ controlDistance Ω w X x y ∧
      controlDistance Ω w X x y ≤ ENNReal.ofReal C *
        auxiliaryDistance (s := s) Ω w X x y := by
  obtain ⟨R,C,η,hR,hRΩ,hC,hη,hbound⟩ :=
    exists_smooth_auxiliary_ordinary_comparison hn hs w hw hΩ X hX hstep hz
  refine ⟨R,2*C,η/2,hR,hRΩ,by positivity,by positivity,?_⟩
  intro x hx y hy hxy
  refine ⟨auxiliaryDistance_le Ω w X hw x y,?_⟩
  have hxR : x ∈ closedBall z R := closedBall_subset_closedBall (by linarith) hx
  by_cases hzero : auxiliaryDistance (s := s) Ω w X x y = 0
  · have heq : x = y := (G1.controlDistance_eq_zero_iff hΩ
      (fun j => shortWeight w (shortIndex (s := s) w j))
      (fun j => shortField w X (shortIndex (s := s) w j))
      (fun j => (shortField_contDiffOn hΩ hX _).continuousOn) (hRΩ hxR)).mp hzero
    subst y
    rw [G1.controlDistance_self w X (hRΩ hxR)]
    exact bot_le
  · let d := auxiliaryDistance (s := s) Ω w X x y
    have hdt : d ≠ ∞ := ne_top_of_lt (hxy.trans_le (le_top))
    have hdpos : 0 < d.toReal := ENNReal.toReal_pos hzero hdt
    have hdsmall : d.toReal < η/2 := by
      have hh := (ENNReal.toReal_lt_toReal hdt ENNReal.ofReal_ne_top).mpr hxy
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ η/2)] using hh
    have hcost := hbound x hxR y hy (2*d.toReal) (by positivity)
      (by linarith) (by
        change d < ENNReal.ofReal (2*d.toReal)
        calc
          d = ENNReal.ofReal d.toReal := (ENNReal.ofReal_toReal hdt).symm
          _ < ENNReal.ofReal (2*d.toReal) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2*d.toReal)).mpr
              (by linarith))
    calc
      controlDistance Ω w X x y ≤ ENNReal.ofReal (C*(2*d.toReal)) := hcost
      _ = ENNReal.ofReal (2*C) * d := by
        rw [show C*(2*d.toReal) = (2*C)*d.toReal by ring,
          ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hdt]
end RothschildStein.G4
