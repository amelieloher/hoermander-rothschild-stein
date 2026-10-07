-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalAuxiliaryOrdinaryComparison
public import RothschildStein.G1.ControlSeparation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Numerical two-sided comparison of the actual extended distances,
including coincident endpoints. -/
theorem exists_numerical_ordinary_auxiliary_metric_comparison (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (D : G3.FreeModelData (k+1) s w)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R₀ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR₀ : 0 < R₀) :
    ∃ R C ε : ℝ, 0 < R ∧ 0 < C ∧ 0 < ε ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R₀ ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R₀) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R₀, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ closedBall x₀ (R/2), ∀ y ∈ closedBall x₀ (R/2),
      auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
      auxiliaryDistance (s := s) Ω w X x y ≤ controlDistance Ω w X x y ∧
      controlDistance Ω w X x y ≤ ENNReal.ofReal C * auxiliaryDistance (s := s) Ω w X x y := by
  obtain ⟨R,C,η,hR,hC,hη,hprovider⟩ :=
    exists_numerical_auxiliary_ordinary_comparison k n s h q hn hs horder hq w D hw M Δ R₀ hM hΔ hR₀
  refine ⟨R,2*C,η/2,hR,by positivity,by positivity,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  obtain ⟨hRΩ',hbound⟩ := hprovider Ω hΩ X hX hstep z hRΩ hjets hmax
  refine ⟨hRΩ',?_⟩
  intro x hx y hy hxy
  refine ⟨auxiliaryDistance_le Ω w X hw x y,?_⟩
  have hxR : x ∈ closedBall z R := closedBall_subset_closedBall (by linarith) hx
  by_cases hzero : auxiliaryDistance (s := s) Ω w X x y = 0
  · have heq : x = y := (G1.controlDistance_eq_zero_iff hΩ
      (fun j => shortWeight w (shortIndex (s := s) w j))
      (fun j => shortField w X (shortIndex (s := s) w j))
      (fun j => (shortField_contDiffOn hΩ hX _).continuousOn) (hRΩ' hxR)).mp hzero
    subst y
    rw [G1.controlDistance_self w X (hRΩ' hxR)]
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
